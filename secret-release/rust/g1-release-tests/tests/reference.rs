use ark_bn254::{Fq, Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField, Zero};
use secret_release::{Bundle, Result, test_bytes};

fn field<F: PrimeField>(x: F) -> Vec<u8> { let mut v = x.into_bigint().to_bytes_le(); v.resize(32,0); v }
fn affine(a: G1Affine) -> Vec<u8> { [field(a.x),field(a.y)].concat() }
fn point(a: G1Affine) -> Vec<u8> { if a.is_zero() { vec![0;65] } else { [vec![1],affine(a)].concat() } }
fn private(q: G1Affine, r: Fr) -> Vec<u8> { [point(q),field(r)].concat() }
fn samples() -> Vec<(G1Affine,Fr,G1Affine)> {
    let g=G1Projective::generator(); let z=G1Affine::zero(); let a=g.into_affine();
    let mut v=vec![(z,Fr::zero(),a),(z,Fr::from(1),a),(z,-Fr::from(1),a),
        (a,Fr::zero(),a),(a,Fr::from(1),a),((-g).into_affine(),Fr::from(1),a),
        (z,Fr::zero(),(g*Fr::from(7)).into_affine()),
        ((g*Fr::from(12)).into_affine(),-Fr::from(1),(g*Fr::from(19)).into_affine())];
    for i in 0..12 {
        let r=Fr::from_le_bytes_mod_order(&test_bytes(i,b"scalar",32));
        let q=(g*Fr::from_le_bytes_mod_order(&test_bytes(i,b"offset",32))).into_affine();
        let a=(g*Fr::from_le_bytes_mod_order(&test_bytes(i,b"input",32))).into_affine();
        v.push((q,r,a));
    }
    let a=(g*Fr::from(333)).into_affine(); let r=Fr::from(123456789u64);
    v.push(((-a.mul_bigint(r.into_bigint())).into_affine(),r,a)); v
}
#[test]
fn reference_and_generated_tools() -> Result<()> {
    let bundle=Bundle::from_env()?;
    bundle.check_sha256()?;
    let mut max_bytes=0;
    for (i,(q,r,a)) in samples().into_iter().enumerate() {
        let expected=point((q.into_group()+a.mul_bigint(r.into_bigint())).into_affine());
        let p=private(q,r); let x=affine(a);
        assert_eq!(bundle.reference(&p,&x)?,expected);
        for (kind,raw) in [("private",&p),("input",&x),("output",&expected)] {
            assert_eq!(bundle.roundtrip(kind,raw)?,*raw);
        }
        let f=bundle.test_fixture(&p,&x,i as u64)?;
        for (kind,raw) in [("input-keys",&f.input_keys),("output-keys",&f.output_keys)] {
            assert_eq!(bundle.roundtrip(kind,raw)?,*raw);
        }
        if bundle.has_candidate() {
            let run=bundle.assert_case(&f,&expected)?;
            max_bytes=max_bytes.max(run.artifact.len());
            if bundle.metadata["fixture"] == true {
                assert_eq!(run.artifact,[p,f.input_keys,vec![0;0],f.coins].concat());
                let mut wrong=run.active.clone(); wrong[0]^=1;
                assert!(bundle.call("evaluate",&[],&[&run.artifact,&x,&wrong],1).is_err());
            }
        } else { assert!(bundle.evaluate(&f).is_err()); }
    }
    println!("G1: 21 Arkworks references, 105 codec round trips; artifact bytes {max_bytes}");
    Ok(())
}
#[test]
fn reject_noncanonical_encodings() -> Result<()> {
    let bundle=Bundle::from_env()?;
    let g=G1Affine::generator(); let x=affine(g); let p=private(g,Fr::zero());
    let modulus=Fq::MODULUS.to_bytes_le(); let scalar_modulus=Fr::MODULUS.to_bytes_le();
    let invalid=vec![
      ("input",[modulus.clone(),field(Fq::from(2))].concat()),("input",vec![0;64]),
      ("input",[field(Fq::from(1)),modulus.clone()].concat()),("input",[x.clone(),vec![0]].concat()),
      ("input",vec![0;63]),("output",[vec![2],x.clone()].concat()),("output",[vec![0],x.clone()].concat()),
      ("output",[vec![1],modulus,field(Fq::from(2))].concat()),("output",vec![0;64]),
      ("private",[point(g),scalar_modulus].concat()),("private",[p.clone(),vec![0]].concat()),
      ("private",[vec![0],x.clone(),vec![0;32]].concat())];
    for (kind,raw) in invalid { assert!(bundle.roundtrip(kind,&raw).is_err(),"accepted {kind}"); }
    let f=bundle.test_fixture(&p,&x,9)?;
    let mut equal=f.input_keys.clone(); let label=equal[..32].to_vec(); equal[32..64].copy_from_slice(&label);
    assert!(bundle.roundtrip("input-keys",&equal).is_err());
    assert!(bundle.call("encode",&[],&[&x,&equal],2).is_err());
    assert!(bundle.call("encode",&[],&[&vec![0;64],&f.input_keys],2).is_err());
    Ok(())
}
