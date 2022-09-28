#![allow(non_snake_case)]
// To regenerate the key shares w_i of party 1, 2, ..., n 
// of the private key u = u_1 + u_2 + ... + u_i
// 1. party_i owns u_i, y_i = u_i*G, while x_i/w_i has been dropped.
// 2.1 owns the polynomial P_i (coefficients, u_i, t) 
// 2.2 drops the polynomial P_i
use curv::{
    arithmetic::traits::Converter,
    // VSS algorithm
    cryptographic_primitives::{
        proofs::sigma_dlog::DLogProof, secret_sharing::feldman_vss::VerifiableSS,
    },
    // basic operations on elliptic curve 
    elliptic::curves::{secp256_k1::Secp256k1, Point, Scalar},
    // BigInt type
    BigInt,
};

// 
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::{
    KeyGenBroadcastMessage1, KeyGenDecommitMessage1, Keys, KeyParams, Parameters,
};

// paillier encrytpion
use paillier::EncryptionKey;
use reqwest::Client;
use sha2::Sha256;
use std::{env, fs, time};

// common tools: 
// 1: aes encrytion/decryption algorithms, 
// 2: broadcast/poll_for_broadcasts, postb, sendp2p, poll_for_p2p, 
// 3: Params, PartySignup, AEAD, AES_KEY_BYTES_LEN
mod common;
use common::{
    aes_decrypt, aes_encrypt, 
    broadcast, poll_for_broadcasts, poll_for_p2p, postb, sendp2p, 
    Params,PartySignup, AEAD, AES_KEY_BYTES_LEN,
};


// // the key.store structure
// #[derive(Serialize, Deserialize)]
// pub struct KeyParams {
//     pub keys: Keys,
//     pub shared_keys: SharedKeys ,
//     pub party_num_int: u16,
//     pub vss_scheme_vec: Vec<VerifiableSS<Secp256k1>>,
//     pub paillier_key_vec: Vec<EncryptionKey>,
//     pub y_sum: Point<Secp256k1>,
// }

pub fn signup(client: &Client) -> Result<PartySignup, ()> {
    let key = "signup-reshare".to_string();

    let res_body = postb(client, "signupreshare", key).unwrap();
    serde_json::from_str(&res_body).unwrap()
}

fn main (){

    // 判断参数是否正确 ./reshare http://127.0.0.1:8000 key.store reshare_Key.store
    if env::args().nth(4).is_some() {
        panic!("too many arguments")
    }
    if env::args().nth(3).is_none() {
        panic!("too few arguments")
    }

    // 从 key.store 中读取 u_i
    let filename = match env::args().nth(2){
        Some(filename) => filename,
        None => String::from("error"),
    };
    //let dest_name = env::args().nth(3);

    let data = std::fs::read_to_string(filename)
        .expect("Unable to read key information, make sure config file is present in the same folder ");
    let Key_Params: KeyParams = serde_json::from_str(&data).unwrap();
    //let u_i:Scalar<E> = Key_Params.keys.u_i.parse::<Scalar<E>>().unwrap();

    // 从 params.json 中读取参数
    // 默认 t = 1, n = 3, 2/3 signing
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    // PARTIES = 3
    let PARTIES: u16 = params.parties.parse::<u16>().unwrap();
    // THRESHOLD = 1
    let THRESHOLD: u16 = params.threshold.parse::<u16>().unwrap();


    // build a Client
    let client = Client::new();

    // delay:
    let delay = time::Duration::from_millis(25);
    let params = Parameters {
        threshold: THRESHOLD, // 1
        share_count: PARTIES, // 3
    };

    //signup: 
    let (party_num_int, uuid) = match signup(&client).unwrap() {
        PartySignup { number, uuid } => (number, uuid),
    };
    println!("number: {:?}, uuid: {:?}", party_num_int, uuid);
//////////////////////////////////////////////////////////////////////////////////////////
    // Regenerate the private key reshares for party i
    // generate Keys as party_keys: {u_i, y_i, e_k, d_k, i} for party i (i represents party_num_int)
    //let party_keys = Keys::create(party_num_int); 
    // let party_keys = Keys{
    //     u_i,
    //     y_i,
    //     dk:,
    //     ek:,
    //     party_index,
    // };

    let party_keys = Keys{
        u_i: Key_Params.keys.u_i,
        y_i: Key_Params.keys.y_i,
        dk: Key_Params.keys.dk,
        ek: Key_Params.keys.ek,
        party_index: party_num_int,
    };
    // generate the broadcasted commitment and decommitment of party i


    let (bc_i, decom_i) = party_keys.phase1_broadcast_phase3_proof_of_correct_key();

    // send commitment bc_i to ephemeral public keys, get round 1 commitments of other parties
    // send commitment of party i to other parties
    assert!(broadcast(
        &client,
        party_num_int,
        "round1",
        serde_json::to_string(&bc_i).unwrap(),
        uuid.clone()
    )
    .is_ok());
    // get commitments bc_1, bc_2, ..., bc_{i-1}, bc{i+1}, ..., bc_n of other parties
    let round1_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round1",
        uuid.clone(),
    );

    // get bc1_vec = [bc_1, bc_2, ..., bc_n]
    let mut bc1_vec = round1_ans_vec
        .iter()
        .map(|m| serde_json::from_str::<KeyGenBroadcastMessage1>(m).unwrap())
        .collect::<Vec<_>>(); 
    // insert bc_i
    bc1_vec.insert(party_num_int as usize - 1, bc_i);

    // send ephemeral public keys and check commitments correctness
    // send decommitment of party i to other parties
    assert!(broadcast(
        &client,
        party_num_int,
        "round2",
        serde_json::to_string(&decom_i).unwrap(),
        uuid.clone()
    )
    .is_ok());
    // get decommitments of other parities
    let round2_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round2",
        uuid.clone(),
    );

    let mut j = 0;
    let mut point_vec: Vec<Point<Secp256k1>> = Vec::new();  // [y_1, y_2, ..., y_n]
    let mut decom_vec: Vec<KeyGenDecommitMessage1> = Vec::new(); // [decom_1, decom_2, ..., decom_n]
    let mut enc_keys: Vec<Vec<u8>> = Vec::new(); 
    // length n-1, store the (n-1) aes encryption keys for party_1, party_2, ..., party_(i-1), party_(i+1), party_n
    
    
    for i in 1..=PARTIES {
        // for party i, store y_i and decom_i
        if i == party_num_int {
            point_vec.push(decom_i.y_i.clone());
            decom_vec.push(decom_i.clone());
        } 
        // for other parties, store y_j and decom_j, and 
        else {
            let decom_j: KeyGenDecommitMessage1 = serde_json::from_str(&round2_ans_vec[j]).unwrap();
            point_vec.push(decom_j.y_i.clone());
            decom_vec.push(decom_j.clone());
            // generate n-1 aes symmetric keys [ki1,ki2, ..., ki(i-1), ki(i+1), ..., kin]
            // = [u_i*u_1*G, u_i*u_2*G, ..., u_i*u_(i-1)*G, u_i*u_(i+1)*G,...,u_i*u_n*G]
            // in party j, he/her computes symmetric key: kji = u_j*u_i*G = kij
            let key_bn: BigInt = (decom_j.y_i.clone() * party_keys.u_i.clone()) // y_j * u_i = u_j * G * u_i
                .x_coord() // return x coordinate
                .unwrap();
            let key_bytes = BigInt::to_bytes(&key_bn);
            let mut template: Vec<u8> = vec![0u8; AES_KEY_BYTES_LEN - key_bytes.len()];
            template.extend_from_slice(&key_bytes[..]);
            enc_keys.push(template);
            j += 1;
        }
    }

    //////////////////////////////////////////////////////////////////////////
    // compute y_sum = (u_1 + u_2 + ... + u_n)*G
    let (head, tail) = point_vec.split_at(1); // split the vector point_vec into point_vec[0] and other
    let y_sum = tail.iter().fold(head[0].clone(), |acc, x| acc + x); 
    // y_sum = X*G = sum(y_1, y_2, ..., y_n) = (u_1*G + .. + u_n*G), where X is the private key, X = u_1 + u_2 + ... + u_n

    // According to feldmanVSS, generate the polynomial p_i and the shares of u_i for party i
    let (vss_scheme, secret_shares, _index) = party_keys
        .phase1_verify_com_phase3_verify_correct_key_phase2_distribute(
            &params, &decom_vec, &bc1_vec,
        )
        .expect("invalid key");

    //////////////////////////////////////////////////////////////////////////////
    // in this part, encrypt first and then send u_i's shares [s_i1, s_i2, ..., s_i(i-1), s_i(i+1), ..., s_in] to
    // party 1, 2, ..., i-1, i+1, ..., n, store s_ii locally.
    // k: the index of secret_shares, 0,1,...,n-1
    // i: the index of parties, 1,2,...,n
    // j: the index of encrykeys, 0,1,...,n-2
    let mut j = 0;
    for (k, i) in (1..=PARTIES).enumerate() { //(index, value)
        if i != party_num_int {
            // prepare encrypted ss for party i:
            let key_i = &enc_keys[j]; 
            // key_i = key_j = kij, the symmetric key between party i and party j
            let plaintext = BigInt::to_bytes(&secret_shares[k].to_bigint());
            let aead_pack_i = aes_encrypt(key_i, &plaintext); 
            // aead_pack_i: the aes ciphertext of the share s_ij of u_i: AES(s_ij)
            // send the AES(s_ij) to party j in the way of p2p
            assert!(sendp2p(
                &client,
                party_num_int,
                i,
                "round3",
                serde_json::to_string(&aead_pack_i).unwrap(),
                uuid.clone()
            )
            .is_ok());
            j += 1; 
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Receive the AES ciphertexts of the shares [s_1i, s_2i, ..., s_(i-1)i, s_(i+1)i, ...,s_ni]
    // from other parties, i.e., party_1, party_2, ..., party_(i-1), party_(i+1), ..., party_n
    let round3_ans_vec = poll_for_p2p(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round3",
        uuid.clone(),
    );

    // j: the index of round3_ans_vec, 0,1,...,n-2
    // i: the index of parties, 1,2,...,n
    // party_shares: the vector of shares, i.e., [s_1i, s_2i, ..., s_ii, ...,s_ni]
    let mut j = 0;
    let mut party_shares: Vec<Scalar<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES {
        if i == party_num_int {
            party_shares.push(secret_shares[(i - 1) as usize].clone());
        } else {
            let aead_pack: AEAD = serde_json::from_str(&round3_ans_vec[j]).unwrap();
            let key_i = &enc_keys[j];
            let out = aes_decrypt(key_i, aead_pack);
            let out_bn = BigInt::from_bytes(&out[..]);
            let out_fe = Scalar::<Secp256k1>::from(&out_bn);
            party_shares.push(out_fe);

            j += 1;
        }
    }

    ///////////////////////////////////////////////////////////////
    // round 4: send vss commitments and receive vss commitments from other parties
    // round4_ans_vec = [vss_scheme_1,...,vss_scheme_(i-1),vss_scheme_(i+1),...,vss_scheme_n)]
    assert!(broadcast(
        &client,
        party_num_int,
        "round4",
        serde_json::to_string(&vss_scheme).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round4_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round4",
        uuid.clone(),
    );

    // verify the commitments of all the shares
    // i: the index of parties, 1,2,...,n
    // j: the index of the vss commiment vector round4_ans_vec, 0,1,...,n-2
    // vss_scheme_vec = [vss_scheme_1, ...., vss_scheme_n]
    let mut j = 0;
    let mut vss_scheme_vec: Vec<VerifiableSS<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES {
        if i == party_num_int {
            vss_scheme_vec.push(vss_scheme.clone());
        } else {
            let vss_scheme_j: VerifiableSS<Secp256k1> =
                serde_json::from_str(&round4_ans_vec[j]).unwrap();
            vss_scheme_vec.push(vss_scheme_j);
            j += 1;
        }
    }

    let (shared_keys, dlog_proof) = party_keys
        .phase2_verify_vss_construct_keypair_phase3_pok_dlog(
            &params,
            &point_vec,
            &party_shares,
            &vss_scheme_vec,
            party_num_int,
        )
        .expect("invalid vss");

    // round 5: send dlog proof and // receive dlog proofs from other parties
    // dlog_proof_vec = [proof1, proof2,...,proofn]
    assert!(broadcast(
        &client,
        party_num_int,
        "round5",
        serde_json::to_string(&dlog_proof).unwrap(),
        uuid.clone()
    )
    .is_ok());
    
    let round5_ans_vec =
        poll_for_broadcasts(&client, party_num_int, PARTIES, delay, "round5", uuid);

    let mut j = 0;
    let mut dlog_proof_vec: Vec<DLogProof<Secp256k1, Sha256>> = Vec::new();
    for i in 1..=PARTIES {
        if i == party_num_int {
            dlog_proof_vec.push(dlog_proof.clone());
        } else {
            let dlog_proof_j: DLogProof<Secp256k1, Sha256> =
                serde_json::from_str(&round5_ans_vec[j]).unwrap();
            dlog_proof_vec.push(dlog_proof_j);
            j += 1;
        }
    }

    // verify the proofs
    Keys::verify_dlog_proofs(&params, &dlog_proof_vec, &point_vec).expect("bad dlog proof");

    //save key to file:
    let paillier_key_vec = (0..PARTIES)
        .map(|i| bc1_vec[i as usize].e.clone())
        .collect::<Vec<EncryptionKey>>();

    let keygen_json = serde_json::to_string(&(
        party_keys, // party_keys = {u_i, y_i, ek, dk, i}
        shared_keys, // {y, x_i}
        party_num_int, // party index i
        vss_scheme_vec, // [vss_scheme_1, vss_scheme_2, ..., vss_scheme_n]
        /* vss_scheme = {
            VerifiableSS {
                parameters: ShamirSecretSharing {
                    threshold: t,
                    share_count: n,
                },
                commitments, //a vector [coef_1*G, coef_2*G, ...]
                proof, // proof of u_i
            },
            SecretShares { shares, polynomial },
        }
        */
        paillier_key_vec, // paillier public key
        y_sum, // X*G the public key corresponding to private key X
    ))
    .unwrap();
    fs::write(env::args().nth(3).unwrap(), keygen_json).expect("Unable to save !");
}






