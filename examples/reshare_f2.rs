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

use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::{
    KeyGenBroadcastMessage1, KeyGenDecommitMessage1, Keys, KeyParams, Parameters,
    SignKeys, SharedKeys,
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
    let key = "signup-reshare2".to_string();

    let res_body = postb(client, "signupreshare2", key).unwrap();
    serde_json::from_str(&res_body).unwrap()
}

fn main (){

    // ./reshare_f2 http://127.0.0.1:8000 key.store reshare_key.store
    if env::args().nth(4).is_some() {
        panic!("too many arguments")
    }
    if env::args().nth(3).is_none() {
        panic!("too few arguments")
    }

    // 从 key.store 中读取 u_i, x_i
    let filename = match env::args().nth(2){
        Some(filename) => filename,
        None => String::from("error"),
    };
    
    let data = fs::read_to_string(filename)
        .expect("Unable to read key information, make sure config file is present in the same folder ");
    let Key_Params: KeyParams = serde_json::from_str(&data).unwrap();

    // 从 params.json 中读取参数
    // 默认 t = 1, n = 3
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    // PARTIES = 3, THRESHOLD = 1
    let PARTIES: u16 = params.parties.parse::<u16>().unwrap();
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

    // let party_keys = Keys{
    //     u_i: Key_Params.keys.u_i,
    //     y_i: Key_Params.keys.y_i,
    //     dk: Key_Params.keys.dk,
    //     ek: Key_Params.keys.ek,
    //     party_index: party_num_int,
    // };

    /*** round 0: collect resharers' IDs ***/
    // {party_num_int, round0, uuid} as the key, {party_id} as the value
    assert!(broadcast(
        &client,
        party_num_int,
        "round0",
        serde_json::to_string(&Key_Params.party_num_int).unwrap(), 
        // party's id: the party index in keygen
        uuid.clone()
    )
    .is_ok());

    // get other's party_ids
    // get the party_ids (assigned in keygen) of the signing party 1, ..., n-1
    // store them in round0_ans_vec
    let round0_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES - 1,
        delay,
        "round0",
        uuid.clone(),
    );


    // move the {n-1} party_ids {i_1, i_2, ..., i_(n-1)} 
    // from round0_ans_vec[0, 1, ..., n-2] to the resharers_vec {i_1 - 1, i_2 - 1, ..., i_(n-1) - 1}
    let mut j = 0;
    let mut signers_vec: Vec<u16> = Vec::new();
    for i in 1..=PARTIES - 1 {
        if i == party_num_int {
            signers_vec.push(Key_Params.party_num_int);
        } else {
            let signer_j: u16 = serde_json::from_str(&round0_ans_vec[j]).unwrap();
            signers_vec.push(signer_j);
            j += 1;
        }
    }

    // Compute li and wi
    let vss_scheme = &Key_Params.vss_scheme_vec[usize::from(Key_Params.party_num_int-1)];
    let li = VerifiableSS::<Secp256k1>::map_share_to_new_params(&vss_scheme.parameters, Key_Params.party_num_int, &signers_vec);
    let wi = li * &Key_Params.shared_keys.x_i;
    //println!("wi = {:?}", wi);

    // The share of the party 3: u3_1 = wi - ui
    let u3_1: Scalar<curv::elliptic::curves::Secp256k1> = wi - &Key_Params.keys.u_i;
   
    // The keys of party i
    let party_keys = Keys{
         u_i: Key_Params.keys.u_i,
         y_i: Key_Params.keys.y_i,
         dk: Key_Params.keys.dk,
         ek: Key_Params.keys.ek,
         party_index: party_num_int,
     };

    // According to the ui of party i, generate the VSS shares and the corresponding proof
    let (vss_scheme_i, secret_shares_i) =
        VerifiableSS::share(params.threshold, params.share_count, &party_keys.u_i);

    // According to the u3_1 of party 3, generate the VSS shares and the corresponding proof
    // p31' p32' p33'
    let (vss_scheme, secret_shares) = 
        VerifiableSS::share(params.threshold, params.share_count, &u3_1);

    let (bc_i, decom_i) = party_keys.phase1_broadcast_phase3_proof_of_correct_key();
    
    // send ephemeral public keys and check commitments correctness
    // send decommitment of party i to other parties
    assert!(broadcast(
        &client,
        party_num_int,
        "round1: y_i",
        serde_json::to_string(&decom_i).unwrap(),
        uuid.clone()
    )
    .is_ok());

    // get decommitments of other parities
    let round1_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES-1,
        delay,
        "round1: y_i",
        uuid.clone(),
    );

    // Generate the key_{ij}
    let mut j = 0;
    let mut point_vec: Vec<Point<Secp256k1>> = Vec::new();  // [y_1, y_2, ..., y_n]
    let mut decom_vec: Vec<KeyGenDecommitMessage1> = Vec::new(); // [decom_1, decom_2, ..., decom_n]
    let mut enc_keys: Vec<Vec<u8>> = Vec::new(); 

    for i in 1..=PARTIES-1 {
        // for party i, store y_i and decom_i
        if i == party_num_int {
            point_vec.push(decom_i.y_i.clone());
            decom_vec.push(decom_i.clone());
        } 
        // for other parties, store y_j and decom_j, and 
        else {
            let decom_j: KeyGenDecommitMessage1 = serde_json::from_str(&round1_ans_vec[j]).unwrap();
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

    /////////////// test //////////////////
    // output the enc keys
    // println!("Enc key:");
    // for i in 0..enc_keys.len(){
    //     println!("{:?}", enc_keys[i]);
    // }
    
    // Encrypt and send the shares pi1, pi2, pi3 to the corresponding party
    let mut j = 0;
    for (k, i) in (1..=PARTIES-1).enumerate() { //(index, value)
        if i != party_num_int {
            // prepare encrypted ss for party i:
            let key_i = &enc_keys[j]; 
            // key_i = key_j = kij, the symmetric key between party i and party j
            let plaintext = BigInt::to_bytes(&secret_shares_i[k].to_bigint());
            //println!("send: secret_shares_{k}: {:?}", secret_shares_i[k]);
            let aead_pack_i = aes_encrypt(key_i, &plaintext); 
            // aead_pack_i: the aes ciphertext of the share s_ij of u_i: AES(s_ij)
            // send the AES(s_ij) to party j in the way of p2p
            assert!(sendp2p(
                &client,
                party_num_int,
                i,
                "round2: pi1, pi2",
                serde_json::to_string(&aead_pack_i).unwrap(),
                uuid.clone()
            )
            .is_ok());
            j += 1; 
        }
    }

    let round2_ans_vec = poll_for_p2p(
        &client,
        party_num_int,
        PARTIES-1,
        delay,
        "round2: pi1, pi2",
        uuid.clone(),
    );

    let mut j = 0;
    let mut party_shares: Vec<Scalar<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES-1 {
        if i == party_num_int{
            party_shares.push(secret_shares_i[(i-1) as usize].clone());
        }
        else{
            let aead_pack: AEAD = serde_json::from_str(&round2_ans_vec[j]).unwrap();
            let key_i = &enc_keys[j];
            let out = aes_decrypt(key_i, aead_pack);
            let out_bn = BigInt::from_bytes(&out[..]);
            let out_fe = Scalar::<Secp256k1>::from(&out_bn);
            party_shares.push(out_fe);
            j += 1;
        }
    }

    // let aead_pack: AEAD = serde_json::from_str(&round2_ans_vec[0]).unwrap();
    // let key_i = &enc_keys[0];
    // let out = aes_decrypt(key_i, aead_pack);
    // let out_bn = BigInt::from_bytes(&out[..]);
    // let ans = Scalar::<Secp256k1>::from(&out_bn);
    // println!("receive: {:?}", ans);


    // Encrypt and send the shares p31, p32, p33 to the corresponding party
    let mut j = 0;
    for (k, i) in (1..=PARTIES-1).enumerate() { //(index, value)
        if i != party_num_int {
            // prepare encrypted ss for party i:
            let key_i = &enc_keys[j]; 
            // key_i = key_j = kij, the symmetric key between party i and party j
            let plaintext = BigInt::to_bytes(&secret_shares[k].to_bigint());
            //println!("send: secret_shares_{k}: {:?}", secret_shares[k]);
            let aead_pack_i = aes_encrypt(key_i, &plaintext); 
            // aead_pack_i: the aes ciphertext of the share s_ij of u_i: AES(s_ij)
            // send the AES(s_ij) to party j in the way of p2p
            assert!(sendp2p(
                &client,
                party_num_int,
                i,
                "round3: p31', p32'",
                serde_json::to_string(&aead_pack_i).unwrap(),
                uuid.clone()
            )
            .is_ok());
            j += 1; 
        }
    }

    let round3_ans_vec = poll_for_p2p(
        &client,
        party_num_int,
        PARTIES-1,
        delay,
        "round3: p31', p32'",
        uuid.clone(),
    );

    let aead_pack: AEAD = serde_json::from_str(&round3_ans_vec[0]).unwrap();
    let key_i = &enc_keys[0];
    let out = aes_decrypt(key_i, aead_pack);
    let out_bn = BigInt::from_bytes(&out[..]);
    let ans = Scalar::<Secp256k1>::from(&out_bn);

    // get the final party_shares
    party_shares.push(&secret_shares[(party_num_int - 1) as usize] + &ans);

   
    // get the key share
    // let mut x_i: Scalar<Secp256k1> = party_shares[0].clone();
    // for i in 1..=PARTIES{
    //     x_i = &x_i + party_shares[(i) as usize].clone(); 
    // }

    let x_i: Scalar<Secp256k1> = party_shares.iter().sum();

    // Generate the share of party 3
    // Encrypt and send the shares p31, p32, p33 to the corresponding party
    let mut j = 0;
    for (k, i) in (1..=PARTIES-1).enumerate() { //(index, value)
        if i != party_num_int {
            // prepare encrypted ss for party i:
            let key_i = &enc_keys[j]; 
            // key_i = key_j = kij, the symmetric key between party i and party j
            let plaintext = BigInt::to_bytes(&(&secret_shares[2] + &secret_shares_i[2]).to_bigint());
            let aead_pack_i = aes_encrypt(key_i, &plaintext); 
            // aead_pack_i: the aes ciphertext of the share s_ij of u_i: AES(s_ij)
            // send the AES(s_ij) to party j in the way of p2p
            assert!(sendp2p(
                &client,
                party_num_int,
                i,
                "round4: p3i+p33'",
                serde_json::to_string(&aead_pack_i).unwrap(),
                uuid.clone()
            )
            .is_ok());
            j += 1; 
        }
    }

    let round4_ans_vec = poll_for_p2p(
        &client,
        party_num_int,
        PARTIES-1,
        delay,
        "round4: p3i+p33'",
        uuid.clone(),
    );

    let aead_pack: AEAD = serde_json::from_str(&round4_ans_vec[0]).unwrap();
    let key_i = &enc_keys[0];
    let out = aes_decrypt(key_i, aead_pack);
    let out_bn = BigInt::from_bytes(&out[..]);
    let ans = Scalar::<Secp256k1>::from(&out_bn);
    let share3 = BigInt::to_bytes(&(&secret_shares[2] + &secret_shares_i[2] + &ans).to_bigint());
    // output
    println!("");
    println!("\nThe share of party 3: {:?}\n", share3);


    ///////////////////////////////////////////////////////////////
    // round 5: send vss commitments and receive vss commitments from other parties
    // round5_ans_vec = [vss_scheme_1,...,vss_scheme_(i-1),vss_scheme_(i+1),...,vss_scheme_n)]
    assert!(broadcast(
        &client,
        party_num_int,
        "round5: vss_i",
        serde_json::to_string(&vss_scheme_i).unwrap(),
        uuid.clone()
    )
    .is_ok());

    let round5_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES-1,
        delay,
        "round5: vss_i",
        uuid.clone(),
    );

    // verify the commitments of all the shares
    // i: the index of parties, 1,2,...,n
    // j: the index of the vss commiment vector round4_ans_vec, 0,1,...,n-2
    // vss_scheme_vec = [vss_scheme_1, ...., vss_scheme_n]
    let mut j = 0;
    let mut vss_scheme_vec_i: Vec<VerifiableSS<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES-1 {
        if i == party_num_int {
            vss_scheme_vec_i.push(vss_scheme_i.clone());
        } else {
            let vss_scheme_j: VerifiableSS<Secp256k1> =
                serde_json::from_str(&round5_ans_vec[j]).unwrap();
            vss_scheme_vec_i.push(vss_scheme_j);
            j += 1;
        }
    }
    
    ///////////////////////////////////////////////////////////////
    // round 6: send vss commitments and receive vss commitments from other parties
    // round6_ans_vec = [vss_scheme_1,...,vss_scheme_(i-1),vss_scheme_(i+1),...,vss_scheme_n)]
    assert!(broadcast(
        &client,
        party_num_int,
        "round6: vss",
        serde_json::to_string(&vss_scheme).unwrap(),
        uuid.clone()
    )
    .is_ok());

    let round6_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES-1,
        delay,
        "round6: vss",
        uuid.clone(),
    );

    // verify the commitments of all the shares
    // i: the index of parties, 1,2,...,n
    // j: the index of the vss commiment vector round4_ans_vec, 0,1,...,n-2
    // vss_scheme_vec = [vss_scheme_1, ...., vss_scheme_n]
    let mut j = 0;
    let mut vss_scheme_vec: Vec<VerifiableSS<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES-1 {
        if i == party_num_int {
            vss_scheme_vec.push(vss_scheme.clone());
        } else {
            let vss_scheme_j: VerifiableSS<Secp256k1> =
                serde_json::from_str(&round6_ans_vec[j]).unwrap();
            vss_scheme_vec.push(vss_scheme_j);
            j += 1;
        }
    }

    for i in 0..=THRESHOLD{
        vss_scheme_vec[0].commitments[i as usize] = &vss_scheme_vec[0].commitments[i as usize] + &vss_scheme_vec[1].commitments[i as usize];
    }
    vss_scheme_vec_i.push(vss_scheme_vec[0].clone());

    let key_json = serde_json::to_string(&(
        party_keys,
        SharedKeys{
            y: Key_Params.shared_keys.y, 
            x_i: x_i,
        } ,
        party_num_int,
        vss_scheme_vec_i,
        Key_Params.paillier_key_vec,
        Key_Params.y_sum,
    ))
    .unwrap();

    fs::write(env::args().nth(3).unwrap(), key_json).expect("Unable to save !");
}