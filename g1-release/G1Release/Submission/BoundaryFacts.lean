import G1Release.Protected.Target

/-! Local unfolding facts avoid requesting lazily generated equation lemmas
inside verifier-owned namespaces. All facts are proved by kernel reduction. -/
namespace G1Release.Submission.BoundaryFacts
open SecretRelease G1Release.Protected

theorem scalar_modulus : GarblingPrize.Protected.scalarFieldModulus =
    21888242871839275222246405745257275088548364400416034343698204186575808495617 := rfl

theorem get_false (pair : Pair) : pair.get false = pair.val.1 := rfl
theorem get_true (pair : Pair) : pair.get true = pair.val.2 := rfl

theorem input_encode (a : Input) : inputCodec.encode a = encodeInput a := rfl

theorem profile_error (q : Nat) : challenge.rom.error q = (q+1 : ℚ≥0) / 2^128 := rfl

end G1Release.Submission.BoundaryFacts
