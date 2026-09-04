import GarblingPrize.Protected.SeededOracle

namespace GarblingPrize.Protected

/-!
# Production-shaped executable boundary

The garbler receives one protected internal-randomness seed and caller-supplied
label pairs. It does not receive `A`. Evaluation receives only artifact bytes,
`A`, and the active labels selected by the caller.
-/

namespace Scheme

/-- The only production-shaped seeded garbling entry point. The label pairs
are supplied independently; this function never derives or owns label keys. -/
def garbleWithSeedAndLabelPairs {profile : BN254.Profile}
    (scheme : Scheme profile) (randomnessSeed : MasterSeed)
    (hidden : HiddenInput profile) (pairs : LabelPairs) : ByteArray :=
  scheme.garbleBytes hidden (SeededInternalOracle.ofSeed randomnessSeed) pairs

/-- Labeled evaluation is the existing proved byte-level evaluator, exposed
under an API name that mirrors the future Rust adapter. -/
def evaluateWithLabels {profile : BN254.Profile} (scheme : Scheme profile)
    (artifact : ByteArray) (input : AffineInput profile)
    (labels : ActiveLabels) : Except EvalError profile.Output :=
  scheme.evaluateBytes artifact input labels

theorem garbleWithSeedAndLabelPairs_eq_garbleBytes
    {profile : BN254.Profile} (scheme : Scheme profile)
    (randomnessSeed : MasterSeed) (hidden : HiddenInput profile)
    (pairs : LabelPairs) :
    scheme.garbleWithSeedAndLabelPairs randomnessSeed hidden pairs =
      scheme.garbleBytes hidden
        (SeededInternalOracle.ofSeed randomnessSeed) pairs := rfl

/-- Universal ideal correctness specializes to the protected seeded oracle and
any independently supplied label pairs. -/
theorem evaluateWithLabels_correct {profile : BN254.Profile}
    (scheme : Scheme profile) (correct : Correct scheme)
    (randomnessSeed : MasterSeed) (hidden : HiddenInput profile)
    (pairs : LabelPairs) (input : AffineInput profile) :
    ∃ output : profile.Output,
      scheme.evaluateWithLabels
          (scheme.garbleWithSeedAndLabelPairs randomnessSeed hidden pairs)
          input (activeLabels pairs input) = .ok output ∧
        profile.outputEquiv output = reference profile hidden input := by
  exact correct hidden (SeededInternalOracle.ofSeed randomnessSeed) pairs input

/-- One seeded artifact can be evaluated at two different valid affine inputs.
Both evaluations use the same bytes; only `A` and its selected active labels
change. This is the explicit reusable-artifact consequence of universal
correctness and the absence of `A` from the garbling API. -/
theorem evaluateWithLabels_reusable {profile : BN254.Profile}
    (scheme : Scheme profile) (correct : Correct scheme)
    (randomnessSeed : MasterSeed) (hidden : HiddenInput profile)
    (pairs : LabelPairs) (leftInput rightInput : AffineInput profile) :
    ∃ leftOutput rightOutput : profile.Output,
      scheme.evaluateWithLabels
          (scheme.garbleWithSeedAndLabelPairs randomnessSeed hidden pairs)
          leftInput (activeLabels pairs leftInput) = .ok leftOutput ∧
        profile.outputEquiv leftOutput =
          reference profile hidden leftInput ∧
      scheme.evaluateWithLabels
          (scheme.garbleWithSeedAndLabelPairs randomnessSeed hidden pairs)
          rightInput (activeLabels pairs rightInput) = .ok rightOutput ∧
        profile.outputEquiv rightOutput =
          reference profile hidden rightInput := by
  obtain ⟨leftOutput, hleft, hleftOutput⟩ :=
    evaluateWithLabels_correct scheme correct randomnessSeed hidden pairs leftInput
  obtain ⟨rightOutput, hright, hrightOutput⟩ :=
    evaluateWithLabels_correct scheme correct randomnessSeed hidden pairs rightInput
  exact ⟨leftOutput, rightOutput, hleft, hleftOutput, hright, hrightOutput⟩

theorem garbleWithSeedAndLabelPairs_size_le {profile : BN254.Profile}
    (scheme : Scheme profile) (valid : ValidCandidate scheme maxBytes)
    (randomnessSeed : MasterSeed) (hidden : HiddenInput profile)
    (pairs : LabelPairs) :
    (scheme.garbleWithSeedAndLabelPairs randomnessSeed hidden pairs).size ≤
      maxBytes := by
  exact valid.artifact_bound hidden
    (SeededInternalOracle.ofSeed randomnessSeed) pairs

end Scheme

end GarblingPrize.Protected
