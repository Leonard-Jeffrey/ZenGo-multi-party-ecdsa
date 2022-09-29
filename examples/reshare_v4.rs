#![allow(non_snake_case)]

use curv::{
    arithmetic::traits::*,
    cryptographic_primitives::{
        proofs::sigma_correct_homomorphic_elgamal_enc::HomoELGamalProof,
        proofs::sigma_dlog::DLogProof, secret_sharing::feldman_vss::VerifiableSS,
    },
    elliptic::curves::{secp256_k1::Secp256k1, Point, Scalar},
    BigInt,
};
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::{
    Keys, LocalSignature, PartyPrivate, Phase5ADecom1, Phase5Com1, Phase5Com2, Phase5DDecom2,
    SharedKeys, SignBroadcastPhase1, SignDecommitPhase1, SignKeys, Parameters, KeyGenBroadcastMessage1, 
    KeyGenDecommitMessage1
};
use multi_party_ecdsa::utilities::mta::*;
use sha2::Sha256;

use paillier::EncryptionKey;
use reqwest::Client;
use std::{env, fs, time};

mod common;
use common::{
    broadcast, check_sig, poll_for_broadcasts, poll_for_p2p, postb, sendp2p, Params, PartySignup,
    aes_decrypt, aes_encrypt, AEAD, AES_KEY_BYTES_LEN,
};

pub fn signup(client: &Client) -> Result<PartySignup, ()> {
    //let key = "signup-sign".to_string();
    let key = "signup-reshare2".to_string();
    
    // "signupsign" is the route function, key is the destination key of HashMap dm_mtx in SM_Manager;
    // res_body is the corresponding vlaue of key
    //let res_body = postb(client, "signupsign", key).unwrap();
    let res_body = postb(client, "signupreshare2", key).unwrap();
    serde_json::from_str(&res_body).unwrap()
}


#[allow(clippy::cognitive_complexity)]
fn main() {
    // verify the parameter number, not more than 4 and not less than 4, equals to 4
    if env::args().nth(4).is_some() {
        panic!("too many arguments")
    }
    if env::args().nth(3).is_none() {
        panic!("too few arguments")
    }


    let client = Client::new();
    // delay:
    let delay = time::Duration::from_millis(25);
    // read key file
    let data = fs::read_to_string(env::args().nth(2).unwrap())
        .expect("Unable to load keys, did you run keygen first? ");
    
        // the structure of the key file
        // party_keys: { u_i, y_i = u_i*G, dk=(p, q), ek = n, party_index = i}
        // shared_keys: {y = \sum y_i, x_i = \sum \lambda*u_ji}
        // parti_id = i (1, 2, 3, 4 ...)
        // VSS_scheme_vec = {vss_1 = (u_1*G, c_12*G,), vss_2 = (u_2), c_22*G, ...}, i.e., the two coefficients of the shamir polynomial
        // paillier_key_vector = {n_1, n_2, n_3, ...}
        // y_sum = Y_x (according to x-cordinate of a point, the y-cordinate is easily computed)
    let (party_keys, shared_keys, party_id, vss_scheme_vec, paillier_key_vector, y_sum): (
        Keys,
        SharedKeys,
        u16,
        Vec<VerifiableSS<Secp256k1>>,
        Vec<EncryptionKey>,
        Point<Secp256k1>,
    ) = serde_json::from_str(&data).unwrap();

    println!("\nvss_scheme_vec-------- 11111:: {:?}", vss_scheme_vec[0].commitments[0]);
    println!("\nvss_scheme_vec-------- 22222:: {:?}", vss_scheme_vec[0].commitments[1]);

    println!("\nvss_scheme_vec-------- 33333:: {:?}", vss_scheme_vec[1].commitments[0]);
    println!("\nvss_scheme_vec-------- 44444:: {:?}", vss_scheme_vec[1].commitments[1]);

    //read parameters:
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let THRESHOLD = params.threshold.parse::<u16>().unwrap();
    let PARTIES: u16 = params.parties.parse::<u16>().unwrap();

    let params = Parameters {
        threshold: THRESHOLD, // 1
        share_count: PARTIES, // 3
    };

    //signup:
    let (party_num_int, uuid) = match signup(&client).unwrap() {
        PartySignup { number, uuid } => (number, uuid),
    };
    println!("number: {:?}, uuid: {:?}", party_num_int, uuid);

    /*** round 0: collect signers IDs ***/
    // {party_num_int, round0, uuid} as the key, {party_id} as the value
    assert!(broadcast(
        &client,
        party_num_int,
        "round0",
        serde_json::to_string(&party_id).unwrap(), // party's id: String the party index in keygen
        uuid.clone()
    )
    .is_ok());
    // get other's party_ids
    // get the party_ids (assigned in keygen) of the signing party 1, 2 ..., t, i.e., {i_1, i_2, ..., i_(t-1)},{i+1}, ..., t
    // store them in round0_ans_vec
    let round0_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        //THRESHOLD + 1,
        PARTIES - 1,
        delay,
        "round0",
        uuid.clone(),
    );

    // move the {t-1} party_ids {i_1, i_2, ..., i_(t-1)} total t-1 party_ids 
    // from round0_ans_vec to the signers_vec, i.e., 0, 1, ..., t-1
    let mut j = 0;
    let mut signers_vec: Vec<u16> = Vec::new();
    for i in 1..=PARTIES-1 {
        if i == party_num_int {
            signers_vec.push(party_id - 1);
        } else {
            let signer_j: u16 = serde_json::from_str(&round0_ans_vec[j]).unwrap();
            signers_vec.push(signer_j - 1);
            j += 1;
        }
    }

    // party_keys = {u_i, y_i, ek, dk, party_id}, shared_keys = {y, x_i}

    // pub struct PartyPrivate {
    //     u_i: Scalar<Secp256k1>,
    //     x_i: Scalar<Secp256k1>,
    //     dk: DecryptionKey,
    // }
    let private = PartyPrivate::set_private(party_keys.clone(), shared_keys.clone());
    

    // vss_scheme_vec[i] = {c_i0*G = u_i*G, c_i1*G}
    // party_num_int - 1 = i-1 
    let sign_keys = SignKeys::create(
        &private,
        &vss_scheme_vec[usize::from(signers_vec[usize::from(party_num_int - 1)])],
        signers_vec[usize::from(party_num_int - 1)],
        &signers_vec,
    );

    println!("\nwi = {:?}\n", sign_keys.w_i);

    let wi = sign_keys.w_i;


    ///////////////////////////////////////////////////////////////////
        // The share of the party 3: u3_1 = wi - ui
    let u3_1: Scalar<Secp256k1> = &wi - &party_keys.u_i;
    println!("\nu3_1 = {:?}\n", u3_1);


    // Correct until now: wi and u3_1

    //////////////////////////////////////////////////////////////////
    
    // According to the ui of party i, generate the VSS shares and the corresponding proof
    let (vss_scheme_i, secret_shares_i) =
        VerifiableSS::share(params.threshold, params.share_count, &party_keys.u_i);

    // According to the u3_1 of party 3, generate the VSS shares and the corresponding proof
    // p31' p32' p33'
    let (vss_scheme, secret_shares_j) = 
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
    println!("Enc key:");
    for i in 0..enc_keys.len(){
        println!("{:?}", enc_keys[i]);
    }


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

    // round2_ans_vec = [pi]
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
    // party_shares = [p11, p21]
    // party_shares = [p12, p22]

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
            let plaintext = BigInt::to_bytes(&secret_shares_j[k].to_bigint());
            //println!("send: secret_shares_j_{k}: {:?}", secret_shares_j[k]);
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


    let mut j = 0;
    let mut party_shares_j: Vec<Scalar<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES-1 {
        if i == party_num_int{
            party_shares_j.push(secret_shares_j[(i-1) as usize].clone());
        }
        else{
            let aead_pack: AEAD = serde_json::from_str(&round3_ans_vec[j]).unwrap();
            let key_i = &enc_keys[j];
            let out = aes_decrypt(key_i, aead_pack);
            let out_bn = BigInt::from_bytes(&out[..]);
            let out_fe = Scalar::<Secp256k1>::from(&out_bn);
            party_shares_j.push(out_fe);
            j += 1;
        }
    }
    // party_shares_j = [p31', p31'']
    // party_shares_j = [p32', p32'']

    // let aead_pack: AEAD = serde_json::from_str(&round3_ans_vec[0]).unwrap();
    // let key_i = &enc_keys[0];
    // let out = aes_decrypt(key_i, aead_pack);
    // let out_bn = BigInt::from_bytes(&out[..]);
    // let ans = Scalar::<Secp256k1>::from(&out_bn);
    // println!("receive: {:?}", ans);

    // let aead_pack: AEAD = serde_json::from_str(&round3_ans_vec[0]).unwrap();
    // let key_i = &enc_keys[0];
    // let out = aes_decrypt(key_i, aead_pack);
    // let out_bn = BigInt::from_bytes(&out[..]);
    // let ans = Scalar::<Secp256k1>::from(&out_bn);



    // get the final party_shares
    //party_shares.push(&secret_shares[(party_num_int - 1) as usize] + &ans);
    // for i in 1..PARTIES-1{
    //     party_shares_j[0] = &party_shares_j[0] + &party_shares_j[i as usize];
    // }
    let p31 = party_shares_j.iter().sum();
    party_shares.push(p31);

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
            let plaintext = BigInt::to_bytes(&(&secret_shares_j[(PARTIES-1) as usize] + &secret_shares_i[(PARTIES-1) as usize]).to_bigint());
            let aead_pack_i = aes_encrypt(key_i, &plaintext); 
            // aead_pack_i: the aes ciphertext of the share s_ij of u_i: AES(s_ij)
            // send the AES(s_ij) to party j in the way of p2p
            assert!(sendp2p(
                &client,
                party_num_int,
                i,
                "round4: pi3+p33'",
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
        "round4: pi3+p33'",
        uuid.clone(),
    );

    let aead_pack: AEAD = serde_json::from_str(&round4_ans_vec[0]).unwrap();
    let key_i = &enc_keys[0];
    let out = aes_decrypt(key_i, aead_pack);
    let out_bn = BigInt::from_bytes(&out[..]);
    let ans = Scalar::<Secp256k1>::from(&out_bn);
    let share3 = BigInt::to_bytes(&(&secret_shares_j[(PARTIES-1) as usize] + &secret_shares_i[(PARTIES-1) as usize] + &ans).to_bigint());
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
    // vss_scheme_vec_i = [vss_scheme1, vss_scheme2] 

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
    let mut vss_scheme_vec_j: Vec<VerifiableSS<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES-1 {
        if i == party_num_int {
            vss_scheme_vec_j.push(vss_scheme.clone());
        } else {
            let vss_scheme_j: VerifiableSS<Secp256k1> =
                serde_json::from_str(&round6_ans_vec[j]).unwrap();
            vss_scheme_vec_j.push(vss_scheme_j);
            j += 1;
        }
    }
    // vss_scheme_vec_j = [vss_scheme1', vss_scheme2']
    //let vss_scheme_party_j = &vss_scheme_vec_j[0] + &vss_scheme_vec_j[1];
    
    //vss_scheme_vec_i.push(vss_scheme_party_j);
    println!("\nvss_scheme_vec_j-------- 1:: {:?}", vss_scheme_vec_j[0].commitments[0]);
    println!("\nvss_scheme_vec_j-------- 2:: {:?}", vss_scheme_vec_j[0].commitments[1]);

    println!("\nvss_scheme_vec_j-------- 3:: {:?}", vss_scheme_vec_j[1].commitments[0]);
    println!("\nvss_scheme_vec_j-------- 4:: {:?}", vss_scheme_vec_j[1].commitments[1]);

    vss_scheme_vec_j[0].commitments[0] = &vss_scheme_vec_j[0].commitments[0] + &vss_scheme_vec_j[1].commitments[0];
    vss_scheme_vec_j[0].commitments[1] = &vss_scheme_vec_j[0].commitments[1] + &vss_scheme_vec_j[1].commitments[1];
    
    // for i in 1..=PARTIES-1{
    //     if i == party_num_int {
    //         vss_scheme_vec_j[(party_num_int - 1) as usize].commitments[i as usize] = &vss_scheme_vec_j[(party_num_int - 1) as usize].commitments[i as usize] + &vss_scheme_vec_j[].commitments[i as usize];
    //     }else{

    //     }
    // }
    println!("\nvss_scheme_vec_j-------- 5: {:?}", vss_scheme_vec_j[0].commitments[0]);
    println!("\nvss_scheme_vec_j-------- 6: {:?}", vss_scheme_vec_j[0].commitments[1]);


    vss_scheme_vec_i.push(vss_scheme_vec_j[0].clone());

    let key_json = serde_json::to_string(&(
        party_keys,
        SharedKeys{
            y: shared_keys.y, 
            x_i: x_i,
        } ,
        party_num_int,
        vss_scheme_vec_i,
        paillier_key_vector,
        y_sum,
    ))
    .unwrap();

    fs::write(env::args().nth(3).unwrap(), key_json).expect("Unable to save !");

}