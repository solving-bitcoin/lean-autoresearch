use wots_lamport_tests::*;
use secret_release::{test_bytes, Bundle, Fixture, Result};

fn keys(seed: u64) -> Keys {
    decode_keys(&test_bytes(seed,b"independent-seed-fixture",2144)).unwrap()
}
fn hex(b: &[u8]) -> String {b.iter().map(|x|format!("{x:02x}")).collect()}

#[test]
fn independent_python_byte_vectors() {
    let expected: serde_json::Value=serde_json::from_str(include_str!("../../../../wots-lamport/test-vectors.json")).unwrap();
    let k: Keys=std::array::from_fn(|j|hash(&[b"python-rust-vector-key".as_slice(),&[j as u8]].concat()));
    let pk=encode_keys(&public_key(&k));let m=std::array::from_fn(|j|j as u8);let sig=encode_keys(&sign(&k,&m));
    assert_eq!(expected["publicKeySha256"],hex(&hash(&pk)));
    assert_eq!(expected["signatureSha256"],hex(&hash(&sig)));
    assert_eq!(expected["word"],serde_json::json!(digits(&m).as_slice()));
    let nonce=std::array::from_fn(|j|j as u8);let label=std::array::from_fn(|j|(7*j+11) as u8);
    let coins: Vec<u8>=(0..16*1023*32).map(|j|(17*j+3) as u8).collect();
    for v in expected["tables"].as_array().unwrap() {
        let value=v["value"].as_bool().unwrap();let wire=v["wire"].as_u64().unwrap() as usize;
        let table=prepare_label(&k,&nonce,wire,value,&label,&coins);
        assert_eq!(v["length"],table.len());assert_eq!(v["commitment"],hex(&commitment(&pk,&nonce,wire,value,&label)));
        for row in v["rows"].as_array().unwrap() {
            let index=row["index"].as_u64().unwrap() as usize;
            assert_eq!(row["ciphertext"],hex(&table[48*index..48*(index+1)]));
        }
    }
}
fn message_with_sum(mut sum: usize) -> Label {
    let mut n=[0u8;64];for d in &mut n { *d=sum.min(15) as u8;sum-=usize::from(*d); }
    assert_eq!(sum,0);std::array::from_fn(|j| n[2*j]*16+n[2*j+1])
}

#[test]
fn all_checksum_carries_and_bit_positions() {
    for sum in 0..=960 {
        let m=message_with_sum(sum);let d=digits(&m);
        assert_eq!(decode_word(&d),Some(m));
        assert_eq!((0..67).map(|j|weight(j)*usize::from(d[j])).sum::<usize>(),960);
        assert_eq!((0..67).map(|j|weight(j)*usize::from(maximum(j)-d[j])).sum::<usize>(),1023);
        for i in 0..256 {assert_eq!(holds(i,true,d[bit_chain(i)]),m[i/8]>>(i%8)&1==1);}
    }
    // Ordinary digit sums change at a mixed-radix carry: not a fixed-sum code.
    assert_ne!(digits(&message_with_sum(952)).iter().map(|&x|usize::from(x)).sum::<usize>(),
               digits(&message_with_sum(953)).iter().map(|&x|usize::from(x)).sum::<usize>());
    assert!(decode_word(&[16;67]).is_none());
    let mut d=digits(&[0;32]);d[66]=0;assert!(decode_word(&d).is_none());
}

#[test]
fn canonical_witness_and_forward_closure_negatives() {
    let k=keys(1);let pk=public_key(&k);
    for m in [[0;32],[255;32],std::array::from_fn(|j|j as u8),message_with_sum(953)] {
        let sig=sign(&k,&m);let d=digits(&m);
        assert!(verify(&pk,&d,&sig));
        assert_eq!(normalize_canonical_witness(&witness(&k,&m)),Some((d,sig)));
        for j in 0..67 {for e in d[j]..=maximum(j) { assert_eq!(chain(sig[j],e-d[j]),chain(k[j],e)); }}
        assert!(!verify(&pk,&d,&sig[..66]));
        let mut mixed=sig;mixed[0]=sign(&keys(2),&m)[0];assert!(!verify(&pk,&d,&mixed));
        let mut raw=witness(&k,&m);raw[1].push(0);assert!(normalize_canonical_witness(&raw).is_none());
        let mut raw=witness(&k,&m);raw[0]=vec![16];assert!(normalize_canonical_witness(&raw).is_none());
        let mut raw=witness(&k,&m);raw[0]=vec![0,0];assert!(normalize_canonical_witness(&raw).is_none());
    }
    assert!(!verify(&pk,&digits(&[0;32]),&[]));
    assert!(normalize_canonical_witness(&[]).is_none());
    assert!(decode_keys(&[0;2143]).is_none());
    assert!(decode_keys(&[0;2145]).is_none());
    // Signing twice at 00 and ff exposes EVERY seed, including checksum seeds.
    let a=sign(&k,&[0;32]);let b=sign(&k,&[255;32]);
    let recovered: Keys=std::array::from_fn(|j| if j<64 {a[j]} else {b[j]});
    assert_eq!(recovered,k);
    assert!(verify(&pk,&digits(&[42;32]),&sign(&recovered,&[42;32])));
}

#[test]
fn weighted_threshold_counts_all_wires_digits() {
    let mut cases=0;
    for i in 0..256 {for value in [false,true] {
        let points=slots(i,value);assert_eq!(points.len(),if value {1982}else{1984});
        assert!(points.iter().all(|&(j,k)|k<maximum(j)));
        for d in 0..16u8 {
            let mut m=[0;32];if i%8<4 {m[i/8]=d;} else {m[i/8]=d<<4;}
            let w=digits(&m);let count=points.iter().filter(|&&(j,k)|w[j]<=k).count();
            assert_eq!(count,threshold(value)-1+usize::from(holds(i,value,d)));
            cases+=1;
        }
    }}
    assert_eq!(cases,8192);
    assert_eq!(ARTIFACT_BYTES,48_752_768);
    assert_eq!(RANDOMNESS_BYTES,268_173_344);
}

#[test]
fn full_chain_geometry_sharing_reconstructs_only_authorized_label() {
    let k=keys(3);let pk=public_key(&k);let pk_bytes=encode_keys(&pk);let nonce=[23;32];
    let coin=test_bytes(4,b"coefficient-fixture",16*1023*32);
    let labels=[[0x7c;32],[0xa5;32]];
    let mut tables=vec![];
    for value in [false,true] {
        let v=usize::from(value);let table=prepare_label(&k,&nonce,0,value,&labels[v],&coin);
        for byte in [0u8,1,254,255] {
            let m=[byte;32];let w=digits(&m);let sig=sign(&k,&m);
            let shares=available_shares(&pk,&nonce,0,value,&w,&sig,&table).unwrap();
            assert_eq!(shares.len(),threshold(value)-1+usize::from(byte&1==v as u8));
            let comm=commitment(&pk_bytes,&nonce,0,value,&labels[v]);
            let expanded=expand_label(&pk,&nonce,0,value,&m,&sig,&table,&comm);
            assert_eq!(expanded,if byte&1==v as u8 {Some(labels[v])} else {None});
        }
        let m=[v as u8;32];let sig=sign(&k,&m);let comm=commitment(&pk_bytes,&nonce,0,value,&labels[v]);
        assert!(expand_label(&pk,&[24;32],0,value,&m,&sig,&table,&comm).is_none());
        assert!(expand_label(&pk,&nonce,0,value,&m,&sig,&table[..table.len()-1],&comm).is_none());
        assert!(expand_label(&pk,&nonce,0,value,&m,&sig,&table,&[0;32]).is_none());
        tables.push(table);
    }
    // Bypass Expand: two signatures supply all seeds and enough shares for BOTH
    // labels. The same artifact releases opposite labels after one-time misuse.
    let min_word=[0;67];
    for value in [false,true] {
        let shares=available_shares(&pk,&nonce,0,value,&min_word,&k,&tables[usize::from(value)]).unwrap();
        assert_eq!(interpolate(&shares[..threshold(value)]),Some(labels[usize::from(value)]));
    }
    assert!(interpolate(&[(1,[0;16]),(1,[0;16])]).is_none());
    assert!(interpolate(&[(0,[0;16])]).is_none());
    assert!(interpolate(&[(65537,[0;16])]).is_none());
}

#[test]
fn small_field_shamir_privacy_exhaustive() {
    // Enumerate ALL polynomials in F_7 of degree <3 for each secret and compare
    // the entire two-share distribution. This checks a toy fact, not ROM privacy.
    for secret in 0..7u64 {
        let mut counts=std::collections::BTreeMap::new();
        for a in 0..7 {for b in 0..7 {
            *counts.entry(((secret+a+b)%7,(secret+2*a+4*b)%7)).or_insert(0)+=1;
        }}
        assert_eq!(counts.len(),49);assert!(counts.values().all(|&n|n==1));
    }
}

#[test]
fn generated_lean_tools_when_bundle_is_supplied() -> Result<()> {
    let bundle=Bundle::from_env()?;let k=keys(10);let pk=public_key(&k);
    let labels: [[Label;2];256]=std::array::from_fn(|i|std::array::from_fn(|v|hash(&[i as u8,v as u8,51])));
    let output_keys: Vec<u8>=labels.iter().flatten().flatten().copied().collect();
    let m=std::array::from_fn(|i|i as u8);
    assert_eq!(bundle.reference(&[],&m)?,m);
    assert_eq!(bundle.roundtrip("input-keys",&encode_keys(&k))?,encode_keys(&k));
    let encoded=bundle.call("encode",&[],&[&m,&encode_keys(&k)],2)?;
    assert_eq!(encoded[0],m);assert_eq!(encoded[1],encode_keys(&sign(&k,&m)));
    if bundle.has_candidate() {
        // Acceptance is construction-neutral. A competitor chooses its own
        // randomness length, artifact format and (proved) universal bound.
        let count=bundle.metadata["randomnessBytes"].as_u64().ok_or("missing candidate randomness size")?;
        let count=usize::try_from(count)?;
        let fixture=Fixture {private:vec![],input:m.to_vec(),coins:test_bytes(10,b"coins",count),input_keys:encode_keys(&k),output_keys};
        let measured=bundle.assert_case(&fixture,&m)?;
        assert!(measured.artifact.len()>=2144);
        assert!(measured.artifact.len() as u64<=bundle.metadata["claimedBytes"].as_u64().ok_or("missing candidate bound")?);
        assert_eq!(&measured.artifact[..2144],encode_keys(&pk));
    }
    Ok(())
}

#[test]
#[ignore = "optional author check of THIS reference format, never an acceptance requirement"]
fn generated_reference_format_correspondence() -> Result<()> {
    let bundle=Bundle::from_env()?;
    assert!(bundle.has_candidate());
    assert_eq!(bundle.metadata["randomnessBytes"],RANDOMNESS_BYTES);
    let k=keys(40);let m=[0xa5;32];
    let labels: [[Label;2];256]=std::array::from_fn(|i|std::array::from_fn(|v|hash(&[i as u8,v as u8,83])));
    let fixture=Fixture {private:vec![],input:m.to_vec(),coins:test_bytes(41,b"coins",RANDOMNESS_BYTES),input_keys:encode_keys(&k),
        output_keys:labels.iter().flatten().flatten().copied().collect()};
    let measured=bundle.assert_case(&fixture,&m)?;
    assert_eq!(measured.artifact,prepare(&k,&labels,&fixture.coins));
    assert_eq!(expand(&measured.artifact,&m,&sign(&k,&m)),Some(measured.output));
    // Reuse the identical generated artifact for later messages, including
    // both bit extremes and a byte-order-sensitive message. Never re-garble.
    for later in [[0;32],[255;32],std::array::from_fn(|i|i as u8)] {
        let encoded=bundle.call("encode",&[],&[&later,&fixture.input_keys],2)?;
        assert_eq!(encoded[0],later);
        assert_eq!(encoded[1],encode_keys(&sign(&k,&later)));
        let started=std::time::Instant::now();
        let released=bundle.call("evaluate",&[],&[&measured.artifact,&later,&encoded[1]],1)?;
        let expected: Vec<u8>=(0..256).flat_map(|i|
            labels[i][usize::from(later[i/8]>>(i%8)&1==1)]).collect();
        assert_eq!(released[0],expected);
        eprintln!("Generated fixed-artifact later-message Expand: {:?}",started.elapsed());
    }
    Ok(())
}

#[test]
#[ignore = "full 256-wire prototype; run explicitly under the 1 GiB/300s native guard"]
fn full_fixed_artifact_multiple_later_messages() {
    let k=keys(11);let labels: [[Label;2];256]=std::array::from_fn(|i| std::array::from_fn(|v|hash(&[i as u8,v as u8,72])));
    let coins=test_bytes(12,b"full-coins",RANDOMNESS_BYTES);
    let started=std::time::Instant::now();
    let artifact=prepare(&k,&labels,&coins);
    eprintln!("Full reference Prepare: {:?}; {} public bytes",started.elapsed(),artifact.len());
    drop(coins);
    for m in [[0;32],[255;32],std::array::from_fn(|i|i as u8)] {
        let expected: Vec<u8>=(0..256).flat_map(|i|labels[i][usize::from(m[i/8]>>(i%8)&1==1)]).collect();
        let started=std::time::Instant::now();
        assert_eq!(expand(&artifact,&m,&sign(&k,&m)),Some(expected));
        eprintln!("Full reference Expand: {:?}",started.elapsed());
    }
    let m=[0;32];let sig=sign(&k,&m);
    assert!(expand(&artifact[..artifact.len()-1],&m,&sig).is_none());
    let mut modified=artifact.clone();modified.push(0);assert!(expand(&modified,&m,&sig).is_none());modified.pop();
    // The public-key prefix is authenticated by the canonical signature.
    modified[0]^=1;assert!(expand(&modified,&m,&sig).is_none());modified[0]^=1;
    // Changing the nonce (including swapping setup instances) breaks masks.
    modified[2144]^=1;assert!(expand(&modified,&m,&sig).is_none());modified[2144]^=1;
    // A replaced selected-label commitment is rejected.
    modified[2144+32]^=1;assert!(expand(&modified,&m,&sig).is_none());modified[2144+32]^=1;
    // Mutate a share which the zero message actually reveals (first slot).
    modified[2144+32+512*32]^=1;assert!(expand(&modified,&m,&sig).is_none());
}
