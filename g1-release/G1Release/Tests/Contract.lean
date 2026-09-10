import G1Release.Protected.Target

namespace G1Release.Tests
open SecretRelease G1Release.Protected G1Release.Math

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

end G1Release.Tests
