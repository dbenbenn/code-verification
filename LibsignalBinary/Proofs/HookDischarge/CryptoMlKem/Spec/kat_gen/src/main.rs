// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Standalone differential KAT generator against `libcrux-ml-kem = "=0.0.10"` for
//! `LibsignalBinary/Proofs/HookDischarge/CryptoMlKem/Spec/MlKemKat.lean`.

use libcrux_ml_kem::mlkem1024::{portable as kyber1024_port, MlKem1024Ciphertext};
use libcrux_ml_kem::mlkem768::incremental::{
    decapsulate_compressed_key, encaps_state_len, encapsulate1, encapsulate2, shared_secret_size,
    validate_pk_bytes, Ciphertext1, Ciphertext2, KeyPairCompressedBytes,
};

fn fmt_lean_bytes(bs: &[u8]) -> String {
    let mut out = String::from("[");
    for (i, b) in bs.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&format!("0x{:02x}#8", b));
    }
    out.push(']');
    out
}

fn sha3_256(bs: &[u8]) -> [u8; 32] {
    libcrux_sha3::sha256(bs)
}

fn main() {
    // 1. Round-3 Kyber-1024 portable KATs (honest roundtrip + corrupted-ct FO implicit rejection)
    let mut k1024_seed = [0u8; 64];
    for i in 0..64 {
        k1024_seed[i] = (i as u8).wrapping_mul(37).wrapping_add(0x5a);
    }
    let mut k1024_rand = [0u8; 32];
    for i in 0..32 {
        k1024_rand[i] = (i as u8).wrapping_mul(91).wrapping_add(0xa3);
    }
    let kp1024 = kyber1024_port::kyber_generate_key_pair(k1024_seed);
    let pk1024_bytes: &[u8] = kp1024.public_key().as_slice();
    let sk1024_bytes: &[u8] = kp1024.private_key().as_slice();
    assert_eq!(pk1024_bytes.len(), 1568);
    assert_eq!(sk1024_bytes.len(), 3168);

    let (ct1024, ss1024_enc) = kyber1024_port::kyber_encapsulate(kp1024.public_key(), k1024_rand);
    let ss1024_dec = kyber1024_port::kyber_decapsulate(kp1024.private_key(), &ct1024);
    assert_eq!(ss1024_enc, ss1024_dec);

    let mut bad_ct1024_bytes = [0u8; 1568];
    bad_ct1024_bytes.copy_from_slice(ct1024.as_ref());
    bad_ct1024_bytes[0] ^= 0x01;
    let bad_ct1024 = MlKem1024Ciphertext::from(bad_ct1024_bytes);
    let ss1024_rej = kyber1024_port::kyber_decapsulate(kp1024.private_key(), &bad_ct1024);
    assert_ne!(ss1024_enc, ss1024_rej);

    // 2. Incremental FIPS 203 ML-KEM-768 KATs & boundary checks
    let mut m768_seed = [0u8; 64];
    for i in 0..64 {
        m768_seed[i] = (i as u8).wrapping_mul(53).wrapping_add(0x19);
    }
    let mut m768_rand = [0u8; 32];
    for i in 0..32 {
        m768_rand[i] = (i as u8).wrapping_mul(73).wrapping_add(0xc7);
    }
    let kp768 = KeyPairCompressedBytes::from_seed(m768_seed);
    let dk768: &[u8; 2400] = kp768.sk();
    let pk1: &[u8; 64] = kp768.pk1();
    let pk2: &[u8; 1152] = kp768.pk2();

    assert!(validate_pk_bytes(pk1, pk2).is_ok());
    assert!(validate_pk_bytes(&pk1[..63], pk2).is_err());
    assert!(validate_pk_bytes(pk1, &pk2[..1151]).is_err());
    let mut bad_pk1 = *pk1;
    bad_pk1[32] ^= 0x01;
    assert!(validate_pk_bytes(&bad_pk1, pk2).is_err());

    // Coeff 0 = 3328 (`0x0d00`, max valid) vs 3329 (`0x0d01`, min invalid) vs 4095 (`0x0fff`),
    // each paired with a freshly recomputed `SHA3-256(pk2' || seed)` so the hash check passes.
    for &(lo, hi_nib, expect_ok) in &[(0x00u8, 0x0du8, true), (0x01, 0x0d, false), (0xff, 0x0f, false)] {
        let mut pk2_mod = *pk2;
        pk2_mod[0] = lo;
        pk2_mod[1] = (pk2_mod[1] & 0xf0) | hi_nib;
        let mut full_pk = [0u8; 1184];
        full_pk[..1152].copy_from_slice(&pk2_mod);
        full_pk[1152..].copy_from_slice(&pk1[..32]);
        let h = sha3_256(&full_pk);
        let mut hdr_mod = [0u8; 64];
        hdr_mod[..32].copy_from_slice(&pk1[..32]);
        hdr_mod[32..].copy_from_slice(&h);
        assert_eq!(validate_pk_bytes(&hdr_mod, &pk2_mod).is_ok(), expect_ok);
    }

    // Note: in debug builds `State::serialize` additionally trips a `debug_assert!` when
    // `short_es.len() < 2080`, whereas release builds (matching the compiled libsignal binary)
    // return `Err(Error::InvalidInputLength)`.
    if !cfg!(debug_assertions) {
        let mut short_es = [0u8; 2079];
        let mut ok_ss = [0u8; 32];
        assert!(encapsulate1(pk1, m768_rand, &mut short_es, &mut ok_ss).is_err());
    }
    let mut ok_es = [0u8; 2080];
    let mut ok_ss = [0u8; 32];
    let mut short_ss = [0u8; 31];
    assert!(encapsulate1(pk1, m768_rand, &mut ok_es, &mut short_ss).is_err());
    assert!(encapsulate1(&pk1[..63], m768_rand, &mut ok_es, &mut ok_ss).is_err());

    let mut es = [0u8; encaps_state_len()];
    let mut ss768_enc = [0u8; shared_secret_size()];
    let ct1 = encapsulate1(pk1, m768_rand, &mut es, &mut ss768_enc).unwrap();
    let ct2 = encapsulate2(&es, pk2);
    let ss768_dec = decapsulate_compressed_key(dk768, &ct1, &ct2);
    assert_eq!(ss768_enc, ss768_dec);

    let mut bad_ct1_bytes = ct1.value;
    bad_ct1_bytes[0] ^= 0x80;
    let ss768_rej_ct1 = decapsulate_compressed_key(dk768, &Ciphertext1 { value: bad_ct1_bytes }, &ct2);

    let mut bad_ct2_bytes = ct2.value;
    bad_ct2_bytes[127] ^= 0x01;
    let ss768_rej_ct2 = decapsulate_compressed_key(dk768, &ct1, &Ciphertext2 { value: bad_ct2_bytes });

    let mut noncanon_es = [0u8; 2080];
    for i in 0..2080 {
        noncanon_es[i] = (i as u8).wrapping_mul(131).wrapping_add(0x7f);
    }
    let ct2_noncanon = encapsulate2(&noncanon_es, pk2);

    println!("private def rustPk1024Sha3 : List (BitVec 8) := {}", fmt_lean_bytes(&sha3_256(pk1024_bytes)));
    println!("private def rustSk1024Sha3 : List (BitVec 8) := {}", fmt_lean_bytes(&sha3_256(sk1024_bytes)));
    println!("private def rustCt1024Sha3 : List (BitVec 8) := {}", fmt_lean_bytes(&sha3_256(ct1024.as_ref())));
    println!("private def rustSs1024Enc : List (BitVec 8) := {}", fmt_lean_bytes(&ss1024_enc));
    println!("private def rustSs1024Rej : List (BitVec 8) := {}", fmt_lean_bytes(&ss1024_rej));
    println!("private def rustDk768Sha3 : List (BitVec 8) := {}", fmt_lean_bytes(&sha3_256(dk768)));
    println!("private def rustCt1_768Sha3 : List (BitVec 8) := {}", fmt_lean_bytes(&sha3_256(&ct1.value)));
    println!("private def rustEs768Sha3 : List (BitVec 8) := {}", fmt_lean_bytes(&sha3_256(&es)));
    println!("private def rustSs768Enc : List (BitVec 8) := {}", fmt_lean_bytes(&ss768_enc));
    println!("private def rustSs768RejCt1 : List (BitVec 8) := {}", fmt_lean_bytes(&ss768_rej_ct1));
    println!("private def rustSs768RejCt2 : List (BitVec 8) := {}", fmt_lean_bytes(&ss768_rej_ct2));
    println!("private def rustCt2_768 : List (BitVec 8) := {}", fmt_lean_bytes(&ct2.value));
    println!("private def rustCt2NoncanonPort : List (BitVec 8) := {}", fmt_lean_bytes(&ct2_noncanon.value));
}
