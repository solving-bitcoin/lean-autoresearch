use secret_release::{Bundle, Result, test_bytes};

#[test]
fn reference_and_generated_tools() -> Result<()> {
    let bundle=Bundle::from_env()?;
    bundle.check_sha256()?;
    let mut cases=vec![vec![0;64],vec![255;64],(0..64).collect(),vec![42;64]];
    for bit in 0..512 { let mut m=vec![0;64];m[bit/8]=1<<(bit%8);cases.push(m); }
    cases.push((0..64).map(|i| if i%2==0 {0x55} else {0xaa}).collect());
    cases.push(test_bytes(100,b"mixed-message",64));
    cases.push(test_bytes(101,b"mixed-message",64));
    assert_eq!(blake3::hash(&cases[2]).to_hex().as_str(),
        "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98");
    for (i,message) in cases.iter().enumerate() {
        let expected=blake3::hash(message);
        assert_eq!(bundle.reference(&[],message)?,expected.as_bytes());
        assert_eq!(bundle.roundtrip("input",message)?,*message);
        // The complete baseline is expensive; exercise diverse messages and keys.
        if i<4 || i%64==0 || i>=516 {
            let f=bundle.test_fixture(&[],message,i as u64)?;
            if bundle.has_candidate() {
                let run=bundle.assert_case(&f,expected.as_bytes())?;
                if bundle.metadata["fixture"] == true {
                    assert_eq!(run.artifact.len(),49162);
                    assert_eq!(run.artifact,[b"LEA".to_vec(),f.input_keys,f.output_keys,f.coins].concat());
                }
                println!("BLAKE3 case {i}: {} artifact bytes",run.artifact.len());
            } else { assert!(bundle.evaluate(&f).is_err()); }
        }
    }
    for n in [0,63,65] { assert!(bundle.roundtrip("input",&vec![0;n]).is_err()); }
    assert!(bundle.roundtrip("private",&[0]).is_err());
    let f=bundle.test_fixture(&[],&test_bytes(3,b"message",64),1)?;
    let mut equal=f.input_keys.clone(); let label=equal[..32].to_vec();equal[32..64].copy_from_slice(&label);
    assert!(bundle.roundtrip("input-keys",&equal).is_err());
    println!("BLAKE3: 519 official-crate reference cases");
    Ok(())
}
