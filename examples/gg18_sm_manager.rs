use std::collections::HashMap;
use std::fs;
use std::sync::RwLock;

use rocket::serde::json::Json;
use rocket::{post, routes, State};
use uuid::Uuid;

mod common;
use common::{Entry, Index, Key, Params, PartySignup};

// The route path: /get
#[post("/get", format = "json", data = "<request>")]
fn get(
    db_mtx: &State<RwLock<HashMap<Key, String>>>,
    request: Json<Index>,
) -> Json<Result<Entry, ()>> {
    let index: Index = request.0;
    let hm = db_mtx.read().unwrap();
    match hm.get(&index.key) {
        Some(v) => {
            let entry = Entry {
                key: index.key,
                value: v.clone(),
            };
            Json(Ok(entry))
        }
        None => Json(Err(())),
    }
}

// The route path: /set
#[post("/set", format = "json", data = "<request>")]
fn set(db_mtx: &State<RwLock<HashMap<Key, String>>>, request: Json<Entry>) -> Json<Result<(), ()>> {
    let entry: Entry = request.0;
    let mut hm = db_mtx.write().unwrap();
    // In keygen broadcast, key = {party_num_int, "round1", uuid}, value = bc_i
    // In sign broadcast, key = {party_num_int, "round0", uuid}, value = party_id
    hm.insert(entry.key.clone(), entry.value);
    Json(Ok(()))
}

// The route path: /signupkeygen
// In the phase of signup_keygen, assign the "number" and "uuid" for each party i in parties (e.g., 3)
#[post("/signupkeygen", format = "json")]
fn signup_keygen(db_mtx: &State<RwLock<HashMap<Key, String>>>) -> Json<Result<PartySignup, ()>> {
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let parties = params.parties.parse::<u16>().unwrap();

    let key = "signup-keygen".to_string();

    let party_signup = {
        let hm = db_mtx.read().unwrap();
        let value = hm.get(&key).unwrap();
        let client_signup: PartySignup = serde_json::from_str(value).unwrap();
        if client_signup.number < parties {
            PartySignup {
                number: client_signup.number + 1,
                uuid: client_signup.uuid,
            }
        } else {
            PartySignup {
                number: 1,
                uuid: Uuid::new_v4().to_string(),
            }
        }
    };

    let mut hm = db_mtx.write().unwrap();
    hm.insert(key, serde_json::to_string(&party_signup).unwrap());
    Json(Ok(party_signup))
}

// The route path: /signupkeygen
// In the phase of signup_keygen, assign the "number" and "uuid" for each party i in parties (e.g., 3)
#[post("/signupreshare", format = "json")]
fn signup_reshare(db_mtx: &State<RwLock<HashMap<Key, String>>>) -> Json<Result<PartySignup, ()>> {
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let parties = params.parties.parse::<u16>().unwrap();

    let key = "signup-reshare".to_string(); 

    let party_signup = {
        let hm = db_mtx.read().unwrap();
        let value = hm.get(&key).unwrap();
        let client_signup: PartySignup = serde_json::from_str(value).unwrap();
        if client_signup.number < parties {
            PartySignup {
                number: client_signup.number + 1,
                uuid: client_signup.uuid,
            }
        } else {
            PartySignup {
                number: 1,
                uuid: Uuid::new_v4().to_string(),
            }
        }
    };

    let mut hm = db_mtx.write().unwrap();
    hm.insert(key, serde_json::to_string(&party_signup).unwrap());
    Json(Ok(party_signup))
}


// The route path: /signupkeygen
// In the phase of signup_keygen, assign the "number" and "uuid" for each party i in parties (e.g., 3)
#[post("/signupreshare2", format = "json")]
fn signup_reshare2(db_mtx: &State<RwLock<HashMap<Key, String>>>) -> Json<Result<PartySignup, ()>> {
    let data = fs::read_to_string("params_reshare.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let parties = params.parties.parse::<u16>().unwrap();

    let key = "signup-reshare2".to_string();

    let party_signup = {
        let hm = db_mtx.read().unwrap();
        let value = hm.get(&key).unwrap();
        let client_signup: PartySignup = serde_json::from_str(value).unwrap();
        if client_signup.number < parties {
            PartySignup {
                number: client_signup.number + 1,
                uuid: client_signup.uuid,
            }
        } else {
            PartySignup {
                number: 1,
                uuid: Uuid::new_v4().to_string(),
            }
        }
    };

    let mut hm = db_mtx.write().unwrap();
    hm.insert(key, serde_json::to_string(&party_signup).unwrap());
    Json(Ok(party_signup))
}


// The route path: /signupsign
#[post("/signupsign", format = "json")]
fn signup_sign(db_mtx: &State<RwLock<HashMap<Key, String>>>) -> Json<Result<PartySignup, ()>> {
    //read parameters:
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let threshold = params.threshold.parse::<u16>().unwrap();
    let key = "signup-sign".to_string();

    let party_signup = {
        let hm = db_mtx.read().unwrap();
        let value = hm.get(&key).unwrap();
        let client_signup: PartySignup = serde_json::from_str(value).unwrap();
        if client_signup.number < threshold + 1 {
            PartySignup {
                number: client_signup.number + 1,
                uuid: client_signup.uuid,
            }
        } else {
            PartySignup {
                number: 1,
                uuid: Uuid::new_v4().to_string(),
            }
        }
    };

    let mut hm = db_mtx.write().unwrap();
    hm.insert(key, serde_json::to_string(&party_signup).unwrap());
    Json(Ok(party_signup))
}

#[tokio::main]
async fn main() {
    // let mut my_config = Config::development();
    // my_config.set_port(18001);
    let db: HashMap<Key, String> = HashMap::new();
    let db_mtx = RwLock::new(db);
    //rocket::custom(my_config).mount("/", routes![get, set]).manage(db_mtx).launch();

    /////////////////////////////////////////////////////////////////
    //////////////////////////init signups://////////////////////////
    /////////////////////////////////////////////////////////////////

    let keygen_key = "signup-keygen".to_string();
    let sign_key = "signup-sign".to_string();
    let reshare_key = "signup-reshare".to_string();
    let reshare2_key = "signup-reshare2".to_string();

    let uuid_keygen = Uuid::new_v4().to_string();
    let uuid_sign = Uuid::new_v4().to_string();
    let uuid_reshare = Uuid::new_v4().to_string();
    let uuid_reshare2 = Uuid::new_v4().to_string();

    let party1 = 0;
    let party_signup_keygen = PartySignup {
        number: party1, // 0
        uuid: uuid_keygen, // Uuid string: ##########
    };
    let party_signup_sign = PartySignup {
        number: party1, // 0
        uuid: uuid_sign, // Uuid string: **********
    };
    let party_signup_reshare = PartySignup {
        number: party1, // 0
        uuid: uuid_reshare, // Uuid string: ^^^^^^^^^^
    };
    let party_signup_reshare2 = PartySignup {
        number: party1, // 0
        uuid: uuid_reshare2, // UUid string: $$$$$$$$$
    };
    {
        let mut hm = db_mtx.write().unwrap();
        hm.insert(
            keygen_key, // "signup-keygen"
            // 0, uuid ##
            serde_json::to_string(&party_signup_keygen).unwrap(),
        );
        hm.insert(
            sign_key, // "signup-sign"
            // 0, uuid **
            serde_json::to_string(&party_signup_sign).unwrap());
        hm.insert(
            reshare_key, // "signup-reshare"
            serde_json::to_string(&party_signup_reshare).unwrap(),
        );
        hm.insert(
            reshare2_key, // "signup-reshare2"
            serde_json::to_string(&party_signup_reshare2).unwrap(),
        );
    }
    /////////////////////////////////////////////////////////////////
    rocket::build()
        .mount("/", routes![get, set, signup_keygen, signup_sign, signup_reshare, signup_reshare2])
        .manage(db_mtx)
        .launch()
        .await
        .unwrap();
}
