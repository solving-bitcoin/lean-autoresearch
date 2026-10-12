//! Copy into examples/ of the pinned bitcoin-scripts checkout and run --locked.
//! Public deterministic fixture keys. Never use these keys to hold funds.
use bitcoin::{consensus::encode::serialize, hashes::{sha256, Hash},
    hex::DisplayHex, secp256k1::{Keypair, Secp256k1, SecretKey},
    taproot::{LeafVersion, TaprootBuilder}, transaction, absolute, Amount,
    OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Witness};
use bitcoin_lab::{signatures::winternitz::{FastPublicKey, FastWinternitz, FullWidth, Sha256},
    support::{script::{script, ScriptCompilation},
    tapscript::{execute_tapscript, TapscriptProfile},
    taproot::verify_taproot_script_path_commitment}};
use serde_json::{json, Value};

fn hash(x: &[u8]) -> [u8;32] { sha256::Hash::hash(x).to_byte_array() }
fn seed(domain: u8, i: usize) -> [u8;32] {
    let mut bytes = vec![domain]; bytes.extend_from_slice(&(i as u32).to_le_bytes()); hash(&bytes)
}
fn chain(mut x: [u8;32], n: usize) -> [u8;32] { for _ in 0..n { x=hash(&x); } x }
fn digits(m: &[u8;32]) -> Vec<u8> {
    let mut d: Vec<u8> = m.iter().flat_map(|b| [b>>4,b&15]).collect();
    let c=960-d.iter().map(|&x| x as usize).sum::<usize>();
    d.extend([(c%8) as u8,((c/8)%8) as u8,(c/64) as u8]); d
}
fn selector(d: u8) -> Vec<u8> { if d==0 { vec![] } else { vec![d] } }
fn local(s: &ScriptBuf, w: &[Vec<u8>], expected: bool) -> Value {
    let mut rows=vec![];
    for p in [TapscriptProfile::Consensus,TapscriptProfile::Policy] {
        let r=execute_tapscript(s.clone(),w.to_vec(),p);
        assert_eq!(r.accepted(),Some(expected), "{p:?}: {:?}",r.outcome);
        rows.push(json!({"profile":format!("{p:?}"),"accepted":r.accepted(),
            "max_stack_items":r.execution().map(|x|x.stats.max_nb_stack_items)}));
    } json!(rows)
}
fn measure(name: &str, fixture: &str, m: &[u8;32], s: &ScriptBuf, data: Vec<Vec<u8>>) -> Value {
    let profiles=local(s,&data,true);
    let mut wrong=data.clone(); wrong[1][0]^=1; local(s,&wrong,false);
    let mut short=data.clone(); short[1].pop(); local(s,&short,false);
    let secp=Secp256k1::new();
    let key=Keypair::from_secret_key(&secp,&SecretKey::from_slice(&[42;32]).unwrap());
    let spend=TaprootBuilder::new().add_leaf(0,s.clone()).unwrap()
        .finalize(&secp,key.x_only_public_key().0).unwrap();
    let control=spend.control_block(&(s.clone(),LeafVersion::TapScript)).unwrap().serialize();
    let spk=ScriptBuf::new_p2tr_tweaked(spend.output_key());
    let mut w=Witness::from_slice(&data); w.push(s.as_bytes()); w.push(&control);
    assert_eq!(verify_taproot_script_path_commitment(&spk,&w),Ok(LeafVersion::TapScript));
    let tx=Transaction {version:transaction::Version::TWO,lock_time:absolute::LockTime::ZERO,
        input:vec![TxIn {previous_output:OutPoint::null(),script_sig:ScriptBuf::new(),
            sequence:Sequence::MAX,witness:w.clone()}],
        output:vec![TxOut {value:Amount::from_sat(100_000),script_pubkey:spk.clone()}]};
    let mut stripped=tx.clone(); stripped.input[0].witness=Witness::new();
    let base=serialize(&stripped).len(); let total=serialize(&tx).len();
    let witness=serialize(&w).len(); let weight=base*4+2+witness;
    assert_eq!(base,94); assert_eq!(total,base+2+witness);
    assert_eq!(tx.weight().to_wu(),weight as u64); assert_eq!(tx.vsize(),weight.div_ceil(4));
    json!({"scheme":name,"fixture":fixture,"message_hex":m.to_lower_hex_string(),
        "evidence":"locally-reproduced","deployment":"unclassified",
        "local_profiles":profiles,"malformed_preimage_and_width_rejected":true,
        "script_bytes":s.len(),"data_items":data.len(),"hint_items":0,
        "data_witness_bytes":serialize(&Witness::from_slice(&data)).len(),
        "control_bytes":control.len(),"complete_witness_bytes":witness,
        "stripped_tx_bytes":base,"total_tx_bytes":total,"weight":weight,
        "vsize":tx.vsize(),"incremental_witness_weight":2+witness,
        "script_hex":s.as_bytes().to_lower_hex_string(),
        "data_witness_hex":data.iter().map(|x|x.to_lower_hex_string()).collect::<Vec<_>>(),
        "control_block_hex":control.to_lower_hex_string(),
        "script_pubkey_hex":spk.as_bytes().to_lower_hex_string(),
        "transaction_hex":serialize(&tx).to_lower_hex_string()})
}
fn main() {
    let maxima:Vec<usize>=(0..67).map(|j|if j==64 || j==65 {7}else{15}).collect();
    let starts:Vec<_>=(0..67).map(|j|seed(1,j)).collect();
    let pk=FastPublicKey::<32,Sha256,FullWidth>::from_chain_ends(
        (0..67).map(|j|chain(starts[j],maxima[j])).collect()).unwrap();
    // Compile the complete leaf once, including cleanup and terminal truth.
    let wots=script! {{ FastWinternitz::<32,Sha256,FullWidth>::checksig_verify(&pk) }
        for _ in 0..64 { OP_DROP } OP_TRUE }.compile_with_policy();
    let labels:Vec<_>=(0..512).map(|j|seed(2,j)).collect();
    let commits:Vec<_>=labels.iter().map(|x|hash(x)).collect();
    let lamport=script! {
        for i in (0..256).rev() {
            OP_SIZE 32 OP_EQUALVERIFY OP_SHA256 OP_SWAP
            OP_IF { commits[2*i+1].to_vec() } OP_ELSE { commits[2*i].to_vec() } OP_ENDIF OP_EQUALVERIFY
        } OP_TRUE
    }.compile_with_policy();
    // All 67 selectors nonzero is attainable (0x11 => checksum 896: last digits
    // 0,0,14; replace first nibble 1 by 2 => 895: 7,7,13).
    let mut max_selectors=[0x11;32]; max_selectors[0]=0x21;
    assert_eq!(digits(&max_selectors).iter().filter(|&&x|x!=0).count(),67);
    let messages=[("zero",[0;32]),("ff",[255;32]),
        ("range",std::array::from_fn(|i|i as u8)),("max_wots_selectors",max_selectors)];
    let mut rows=vec![];
    for (fixture,m) in messages {
        let d=digits(&m); let mut ww=vec![]; let mut lw=vec![];
        for j in 0..67 {ww.push(selector(d[j]));ww.push(chain(starts[j],d[j] as usize).to_vec());}
        for i in 0..256 {let b=(m[i/8]>>(i%8))&1; lw.push(selector(b));lw.push(labels[2*i+b as usize].to_vec());}
        rows.push(measure("WOTS256-SHA256-FullWidth",fixture,&m,&wots,ww));
        rows.push(measure("Lamport256-SHA256",fixture,&m,&lamport,lw));
    }
    println!("{}",serde_json::to_string_pretty(&json!({
        "upstream_commit":"bf9ee0bb34987a9130ad9dc13a06e18fef137296",
        "compilation":"whole-leaf repository compile_with_policy",
        "offchain_artifact_bytes":48_752_768,"fixtures":rows})).unwrap());
}
