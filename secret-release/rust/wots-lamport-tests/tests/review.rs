//! Review regressions: explicit assumption boundaries and hostile inputs.
use secret_release::test_bytes;
use wots_lamport_tests::*;

#[test]
fn interleaved_horner_matches_scalar_field_evaluation() {
    let coefficients: Vec<[u64;16]>=(0..1024).map(|d|
        std::array::from_fn(|i| ((d*913+i*671+37) as u64)%PRIME)).collect();
    for x in [0,1,2,7,64,1023,1984,65536] {
        let values=eval_limbs(&coefficients,x);
        for i in 0..16 {
            let scalar: Vec<u64>=coefficients.iter().map(|row|row[i]).collect();
            assert_eq!(values[i],eval(&scalar,x));
        }
    }
}

fn fixture_keys() -> Keys {decode_keys(&test_bytes(71,b"review-keys",2144)).unwrap()}
fn hex(b: &[u8]) -> String {b.iter().map(|x|format!("{x:02x}")).collect()}

#[test]
fn pinned_upstream_sha256_fullwidth_vector() {
    // Exact constants from bf9ee0b base16/tests/hash_choice.rs. This cross-check
    // does NOT equate the upstream seeded law with 67 uniform independent seeds.
    let namespace=hash(&[b"bitcoin-lab/winternitz-sha256/v1".as_slice(),&[0x42;32],&32u64.to_be_bytes()].concat());
    let keys: Keys=std::array::from_fn(|j|hash(&[namespace.as_slice(),&(j as u32).to_be_bytes()].concat()));
    let m=std::array::from_fn(|j|j as u8);
    assert_eq!(hex(&hash(&encode_keys(&public_key(&keys)))),"b3adc3efa9a36dc3d0dc9a545ba390fa39131315d20b0bef27aba88a4f412ff5");
    assert_eq!(hex(&hash(&encode_keys(&sign(&keys,&m)))),"6850a0b422d98944a6596bbfd4865ca32dbb08178e6a8247ced71053ebd1e19e");
}

#[test]
fn domain_separation_points_and_seed_widths() {
    let pk=encode_keys(&public_key(&fixture_keys()));let mut seen=std::collections::BTreeSet::new();
    for i in [0,1,127,128,255] {for v in [false,true] {for x in [1,2,255,256,1982,1984] {for nonce in [[0;32],[1;32]] {for node in [[0;32],[1;32]] {
        for query in mask_queries(&pk,&nonce,i,v,x,&node) {
            assert_ne!(query.len(),32); // disjoint from ALL raw chain inputs
            assert!(query.starts_with(b"WOTS-LAMPORT/mask/v1"));
            assert!(seen.insert(query));
        }
    }}}}}
    assert_eq!(seen.len(),480);
    let key=fixture_keys();let pk_typed=public_key(&key);
    let mut raw=witness(&key,&[0;32]);
    // Duplicate a coordinate opening in an independent-key setup.
    raw[3]=raw[1].clone();let (word,nodes)=normalize_canonical_witness(&raw).unwrap();
    assert!(!verify(&pk_typed,&word,&nodes));
    for length in [0,1,16,20,31,33,64,520] {
        let mut raw=witness(&key,&[0;32]);raw[1]=vec![0;length];
        assert!(normalize_canonical_witness(&raw).is_none());
    }
    // Do not accidentally accept clamped selectors or numeric aliases here.
    for selector in [vec![0],vec![0x80],vec![1,0],vec![16],vec![0x81],vec![0xff;5]] {
        let mut raw=witness(&key,&[0;32]);raw[0]=selector;
        assert!(normalize_canonical_witness(&raw).is_none());
    }
    assert!(interpolate(&[]).is_none());
    assert!(interpolate(&[(1,[65537;16])]).is_none());
    assert!(interpolate(&[(1,[65536;16])]).is_none()); // not a lossless 16-bit limb
}

#[test]
fn degenerate_coins_preserve_correctness_but_are_not_security() {
    let keys=fixture_keys();let pk=public_key(&keys);let nonce=[0;32];let coins=vec![0;16*1023*32];
    for label in [[0;32],[255;32]] {
        let table=prepare_label(&keys,&nonce,255,false,&label,&coins);
        let comm=commitment(&encode_keys(&pk),&nonce,255,false,&label);
        let m=[0;32];let sig=sign(&keys,&m);
        assert_eq!(expand_label(&pk,&nonce,255,false,&m,&sig,&table,&comm),Some(label));
        // Zero coefficients make a constant polynomial. Bypass Expand: a single
        // unauthorized exposed share recovers the opposite label. Correctness
        // is universal in coins; security necessarily uses the fixed coin law.
        let m=[255;32];let word=digits(&m);let sig=sign(&keys,&m);
        let exposed=available_shares(&pk,&nonce,255,false,&word,&sig,&table).unwrap();
        assert_eq!(exposed.len(),threshold(false)-1);
        assert_eq!(interpolate(&exposed[..1]),Some(label));
        assert!(expand_label(&pk,&nonce,256,false,&m,&sig,&table,&comm).is_none());
    }
}

#[test]
fn public_endpoints_are_not_share_keys() {
    let keys=fixture_keys();let pk=public_key(&keys);let m=[0;32];let sig=sign(&keys,&m);let word=digits(&m);
    for i in 0..256 {for value in [false,true] {
        let all=slots(i,value);
        assert!(all.iter().all(|&(j,k)| k<maximum(j)));
        // Endpoints alone expose zero share-encryption keys by forward hashing.
        assert_eq!(all.iter().filter(|&&(j,k)|maximum(j)<=k).count(),0);
        // The post-release view contains actual public endpoints and all labels
        // selected by the original message; the opposite branch is distinct.
        assert!(verify(&pk,&word,&sig));
    }}
    // The caller's label bytes are not replaced by a hash or truncated digest.
    let zero=[0;32];let mut last_bit=zero;last_bit[31]=128;
    assert_ne!(digits(&zero),digits(&last_bit));
    assert_eq!(decode_word(&digits(&last_bit)),Some(last_bit));
}
