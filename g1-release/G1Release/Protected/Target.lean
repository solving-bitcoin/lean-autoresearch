import G1Release.Protected.Codecs
import SecretRelease.Examples

namespace G1Release.Protected
open SecretRelease
open GarblingPrize.Protected

/-- Exact BN254 group semantics; A is a valid finite-affine point. -/
def reference (p : Private) (a : Input) : Output :=
  BN254.CanonicalOutput.ofPoint
    (p.1.toPoint + p.2.val • BN254.ofAffine a.val.1 a.val.2 a.property)

/-- Construction-independent, finite-label ROM challenge. The scalar and
point offset are private; the canonical plaintext result is permitted leakage. -/
def challenge : SecretRelease.Challenge where
  Private := Private
  Input := Input
  Output := Output
  privateCodec := privateCodec
  inputCodec := inputCodec
  inputs := Lamport inputCodec
  outputs := Plain encodeOutput
  reference := reference
  Claim := Fin 512 × SecretRelease.Label
  wins := fun _ _ a keys _ guess =>
    guess.2 = (keys guess.1).get (!(inputCodec.encode a)[guess.1.val])
  privateLeakage := some fun p a => encodeOutput (reference p a)
  rom := SecretRelease.Examples.rom128

abbrev CertifiedScheme := SecretRelease.Certified challenge

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
    simpa only [reference_toPoint] using this
  · intro h
    unfold reference
    rw [h]

/-- At one fixed input, every map has a representative with zero scalar and
an offset equal to the disclosed result. The privacy comparison is therefore
substantive; it cannot justify publishing the original scalar. -/
@[simp] theorem reference_zero_scalar (q : Output) (a : Input) :
    reference (q, (⟨0, by decide⟩ : CanonicalScalar)) a = q := by
  simp [reference]

theorem same_leakage_zero_map (p : Private) (a : Input) :
    encodeOutput (reference (reference p a, (⟨0, by decide⟩ : CanonicalScalar)) a) =
      encodeOutput (reference p a) := by
  rw [reference_zero_scalar]

end G1Release.Protected
