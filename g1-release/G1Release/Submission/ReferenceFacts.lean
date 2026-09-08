import G1Release.Protected.Target

namespace G1Release.Submission
open SecretRelease G1Release.Protected GarblingPrize.Protected

theorem encodeOutput_injective : Function.Injective encodeOutput := by
  intro x y h
  change packBits (outputCodec.encode x) = packBits (outputCodec.encode y) at h
  have he := congrArg (unpackBits 520) h
  simp only [unpackBits_packBits, Option.some.injEq] at he
  have hd := congrArg outputCodec.decode he
  exact Option.some.inj ((outputCodec.decode_encode x).symm.trans
    (hd.trans (outputCodec.decode_encode y)))

/-- Checked connection to the existing canonical BN254 group, including infinity. -/
theorem reference_toPoint (p : Private) (a : Input) :
    (reference p a).toPoint = p.1.toPoint + p.2.val • BN254.ofAffine a.val.1 a.val.2 a.property :=
  BN254.CanonicalOutput.toPoint_ofPoint _

/-- The permitted byte leakage is exactly equality of the mathematical result. -/
theorem same_leakage_iff (p₀ p₁ : Private) (a : Input) :
    encodeOutput (reference p₀ a) = encodeOutput (reference p₁ a) ↔
      p₀.1.toPoint + p₀.2.val • BN254.ofAffine a.val.1 a.val.2 a.property =
      p₁.1.toPoint + p₁.2.val • BN254.ofAffine a.val.1 a.val.2 a.property := by
  constructor
  · intro h
    have := congrArg BN254.CanonicalOutput.toPoint (encodeOutput_injective h)
    exact (reference_toPoint p₀ a).symm.trans (this.trans (reference_toPoint p₁ a))
  · intro h
    delta reference
    exact congrArg (fun point => encodeOutput (BN254.CanonicalOutput.ofPoint point)) h

end G1Release.Submission
