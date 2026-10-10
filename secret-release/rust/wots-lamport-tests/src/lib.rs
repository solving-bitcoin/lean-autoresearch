//! Independent executable research reference; never a substitute for Lean proofs.
//! All starts are independent 32-byte caller inputs. This is not upstream's
//! master-seed distribution. Byte transport is strict/canonical.
use sha2::{Digest, Sha256};

pub type Label = [u8; 32];
pub type Keys = [Label; 67];
pub const PRIME: u64 = 65537;
pub const RANDOMNESS_BYTES: usize = 32 + 512 * 16 * 1023 * 32;
pub const BODY_BYTES: usize = 32 + 512 * 32 + 256 * (1984 + 1982) * 48;
pub const ARTIFACT_BYTES: usize = 2144 + BODY_BYTES;
pub fn hash(bytes: &[u8]) -> Label { Sha256::digest(bytes).into() }
pub fn maximum(j: usize) -> u8 { if j == 64 || j == 65 { 7 } else { 15 } }
pub fn weight(j: usize) -> usize { match j { 65 => 8, 66 => 64, _ => 1 } }
pub fn digits(message: &Label) -> [u8; 67] {
    let mut out = [0; 67];
    for (j, byte) in message.iter().enumerate() {
        out[2*j] = byte >> 4; out[2*j+1] = byte & 15;
    }
    let sum: u16 = out[..64].iter().map(|&x| u16::from(15-x)).sum();
    out[64] = (sum & 7) as u8;
    out[65] = ((sum >> 3) & 7) as u8;
    out[66] = (sum >> 6) as u8;
    out
}
pub fn decode_word(word: &[u8]) -> Option<Label> {
    if word.len() != 67 || word.iter().enumerate().any(|(j,&d)| d > maximum(j)) { return None; }
    let mut message = [0; 32];
    for j in 0..32 { message[j] = word[2*j]*16 + word[2*j+1]; }
    (digits(&message).as_slice() == word).then_some(message)
}
pub fn chain(mut node: Label, count: u8) -> Label {
    for _ in 0..count { node = hash(&node); } node
}
pub fn public_key(keys: &Keys) -> Keys { std::array::from_fn(|j| chain(keys[j], maximum(j))) }
pub fn sign(keys: &Keys, message: &Label) -> Keys {
    let word = digits(message); std::array::from_fn(|j| chain(keys[j], word[j]))
}
pub fn verify(pk: &Keys, word: &[u8], nodes: &[Label]) -> bool {
    decode_word(word).is_some() && nodes.len() == 67 &&
        (0..67).all(|j| chain(nodes[j], maximum(j)-word[j]) == pk[j])
}
pub fn encode_keys(keys: &Keys) -> Vec<u8> { keys.iter().flatten().copied().collect() }
pub fn decode_keys(bytes: &[u8]) -> Option<Keys> {
    if bytes.len() != 2144 { return None; }
    Some(std::array::from_fn(|j| bytes[j*32..(j+1)*32].try_into().unwrap()))
}
/// Upstream exact-hash FullWidth to_witness order: [digit,node], chain 0..66.
pub fn witness(keys: &Keys, message: &Label) -> Vec<Vec<u8>> {
    let word = digits(message); let sig = sign(keys,message);
    (0..67).flat_map(|j| [if word[j] == 0 { vec![] } else { vec![word[j]] }, sig[j].to_vec()]).collect()
}
/// Canonical adapter only. No claim to accept every Script-accepted raw stack.
pub fn normalize_canonical_witness(raw: &[Vec<u8>]) -> Option<([u8;67],Keys)> {
    if raw.len() != 134 { return None; }
    let mut word = [0;67]; let mut nodes = [[0;32];67];
    for j in 0..67 {
        word[j] = match raw[2*j].as_slice() { [] => 0, [x] if *x >= 1 && *x <= maximum(j) => *x, _ => return None };
        nodes[j] = raw[2*j+1].as_slice().try_into().ok()?;
    }
    decode_word(&word)?; Some((word,nodes))
}
pub fn bit_chain(i: usize) -> usize { 2*(i/8) + usize::from(i%8 < 4) }
pub fn holds(i: usize, value: bool, d: u8) -> bool { ((d >> (i%4)) & 1 != 0) == value }
pub fn slots(i: usize, value: bool) -> Vec<(usize,u8)> {
    let mut out = vec![];
    for j in 0..67 {
        for k in 0..maximum(j) {
            let n = weight(j) as isize + if j == bit_chain(i) {
                isize::from(holds(i,value,k)) - isize::from(holds(i,value,k+1))
            } else { 0 };
            assert!(n >= 0);
            out.extend(std::iter::repeat_n((j,k), n as usize));
        }
    }
    out
}
pub fn threshold(value: bool) -> usize { if value { 1023 } else { 1024 } }
fn mul(a: u64,b: u64) -> u64 { a*b % PRIME }
fn sub(a: u64,b: u64) -> u64 { (a+PRIME-b)%PRIME }
fn inverse(mut a: u64) -> u64 { let mut r=1; for _ in 0..16 {r=mul(r,a);a=mul(a,a);} r }
pub fn eval(poly: &[u64], x: u64) -> u64 { poly.iter().rev().fold(0, |acc,&a| (a+x*acc)%PRIME) }
fn read_field(bytes: &[u8]) -> u64 { bytes.iter().rev().fold(0,|acc,&b| (acc*256+u64::from(b))%PRIME) }
fn domain(tag: &[u8], pk: &[u8], nonce: &Label, i: usize, value: bool) -> Vec<u8> {
    [tag, nonce, pk, &(i as u16).to_le_bytes(), &[u8::from(value)]].concat()
}
/// Fixed-width transcript, exposed for author audits of domain separation.
/// Valid construction inputs have i<256, 1<=x<=1984 and exactly 2,144 pk bytes.
pub fn mask_queries(pk: &[u8], nonce: &Label, i: usize, value: bool, x: usize, node: &Label) -> [Vec<u8>;2] {
    assert_eq!(pk.len(),2144);assert!(i<256);assert!((1..=1984).contains(&x));
    let mut d=domain(b"WOTS-LAMPORT/mask/v1",pk,nonce,i,value);
    d.extend((x as u16).to_le_bytes());d.extend(node);
    d.push(0);let first=d.clone();*d.last_mut().unwrap()=1;[first,d]
}
fn mask(pk: &[u8], nonce: &Label, i: usize, value: bool, x: usize, node: &Label) -> [u8;48] {
    let queries=mask_queries(pk,nonce,i,value,x,node);let a=hash(&queries[0]);let b=hash(&queries[1]);
    std::array::from_fn(|j| if j<32 {a[j]} else {b[j-32]})
}
pub fn commitment(pk: &[u8],nonce: &Label,i: usize,value: bool,label: &Label) -> Label {
    let mut d=domain(b"WOTS-LAMPORT/label/v1",pk,nonce,i,value);d.extend(label);hash(&d)
}
/// Independent coefficient blocks: 16 limbs * 1023 blocks * 32 bytes.
/// Reduction modulo 65537 is slightly biased; the ROM proof must account for it.
pub fn prepare_label(keys: &Keys,nonce: &Label,i: usize,value: bool,label: &Label,coins: &[u8]) -> Vec<u8> {
    assert!(i<256);assert_eq!(coins.len(),16*1023*32);
    let pk=encode_keys(&public_key(keys));
    let polys: Vec<Vec<u64>>=(0..16).map(|limb| (0..threshold(value)).map(|degree| {
        if degree==0 {u64::from(u16::from_le_bytes([label[2*limb],label[2*limb+1]]))}
        else {let p=(limb*1023+degree-1)*32;read_field(&coins[p..p+32])}
    }).collect()).collect();
    let nodes: Vec<Vec<Label>>=(0..67).map(|j| (0..maximum(j)).map(|k| chain(keys[j],k)).collect()).collect();
    let mut out=Vec::with_capacity(slots(i,value).len()*48);
    for (index,(j,k)) in slots(i,value).into_iter().enumerate() {
        let pad=mask(&pk,nonce,i,value,index+1,&nodes[j][k as usize]);
        for limb in 0..16 {
            let bytes=eval(&polys[limb],(index+1) as u64).to_le_bytes();
            out.extend((0..3).map(|b| bytes[b]^pad[3*limb+b]));
        }
    }
    out
}
/// Algebraic interpolation needs unique, nonzero field coordinates. Bad or
/// duplicated points are rejected even if a caller bypasses Expand.
pub fn interpolate(points: &[(u64,[u64;16])]) -> Option<Label> {
    if points.is_empty() {return None;}
    let mut seen=std::collections::BTreeSet::new();
    for (x,y) in points { if *x==0 || *x>=PRIME || !seen.insert(*x) || y.iter().any(|v|*v>=PRIME) {return None;} }
    let mut limbs=[0u64;16];
    for (a,ys) in points {
        let mut num=1;let mut den=1;
        for (b,_) in points { if a!=b {num=mul(num,sub(0,*b));den=mul(den,sub(*a,*b));} }
        let factor=mul(num,inverse(den));
        for limb in 0..16 {limbs[limb]=(limbs[limb]+mul(factor,ys[limb]))%PRIME;}
    }
    if limbs.iter().any(|&v|v>=65536) {return None;}
    Some(std::array::from_fn(|i| limbs[i/2].to_le_bytes()[i%2]))
}
pub fn available_shares(pk: &Keys,nonce: &Label,i: usize,value: bool,word: &[u8;67],nodes: &Keys,table: &[u8]) -> Option<Vec<(u64,[u64;16])>> {
    if i>=256 {return None;}
    let all=slots(i,value);if table.len()!=all.len()*48 {return None;}
    let pk_bytes=encode_keys(pk);let mut out=vec![];
    for (index,(j,k)) in all.into_iter().enumerate() {
        if word[j]<=k {
            let node=chain(nodes[j],k-word[j]);let pad=mask(&pk_bytes,nonce,i,value,index+1,&node);
            let fields=std::array::from_fn(|limb| (0..3).fold(0,|a,b|a+(((table[index*48+3*limb+b]^pad[3*limb+b]) as u64)<<(8*b))));
            if fields.iter().any(|&f|f>=PRIME) {return None;}
            out.push(((index+1) as u64,fields));
        }
    }
    Some(out)
}
pub fn expand_label(pk: &Keys,nonce: &Label,i: usize,value: bool,m: &Label,nodes: &Keys,table: &[u8],commit: &Label) -> Option<Label> {
    if i>=256 {return None;}
    let word=digits(m);if !verify(pk,&word,nodes) || holds(i,value,word[bit_chain(i)])==false {return None;}
    let shares=available_shares(pk,nonce,i,value,&word,nodes,table)?;
    if shares.len()!=threshold(value) {return None;}
    let label=interpolate(&shares)?;
    (commitment(&encode_keys(pk),nonce,i,value,&label)==*commit).then_some(label)
}
pub fn prepare(keys: &Keys,labels: &[[Label;2];256],coins: &[u8]) -> Vec<u8> {
    assert_eq!(coins.len(),RANDOMNESS_BYTES);
    let nonce: Label=coins[..32].try_into().unwrap();let pk=encode_keys(&public_key(keys));
    let mut out=Vec::with_capacity(ARTIFACT_BYTES);out.extend(&pk);out.extend(nonce);
    for (i,pair) in labels.iter().enumerate() {for (v,label) in pair.iter().enumerate() {out.extend(commitment(&pk,&nonce,i,v==1,label));}}
    let stride=16*1023*32;
    for (i,pair) in labels.iter().enumerate() {for (v,label) in pair.iter().enumerate() {
        let start=32+(2*i+v)*stride;
        out.extend(prepare_label(keys,&nonce,i,v==1,label,&coins[start..start+stride]));
    }}
    assert_eq!(out.len(),ARTIFACT_BYTES);out
}
pub fn expand(artifact: &[u8],m: &Label,nodes: &Keys) -> Option<Vec<u8>> {
    if artifact.len()!=ARTIFACT_BYTES {return None;}
    let pk=decode_keys(&artifact[..2144])?;let body=&artifact[2144..];let nonce=body[..32].try_into().ok()?;
    let mut out=Vec::with_capacity(8192);
    for i in 0..256 {
        let value=m[i/8]>>(i%8)&1==1;let v=usize::from(value);
        let offset=32+512*32+(i*(1984+1982)+v*1984)*48;
        let count=if value {1982} else {1984};
        let commit=body[32+(2*i+v)*32..32+(2*i+v+1)*32].try_into().ok()?;
        out.extend(expand_label(&pk,&nonce,i,value,m,nodes,&body[offset..offset+count*48],&commit)?);
    }
    Some(out)
}
