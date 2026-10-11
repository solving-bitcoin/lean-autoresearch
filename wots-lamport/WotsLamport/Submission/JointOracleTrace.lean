import WotsLamport.Submission.OracleTrace

namespace WotsLamport.Submission
open SecretRelease OracleComp MeasureTheory

/-- Couple two outputs on the same sample space. The only loss is the
probability that the outputs differ; no measurability shortcut is needed for
this outer-measure inequality. -/
theorem event_transfer_of_coupling {Ω A : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (real ideal : Ω → A) (event : Set A) :
    μ (real ⁻¹' event) ≤ μ (ideal ⁻¹' event) + μ {ω | real ω ≠ ideal ω} := by
  classical
  have hs : real ⁻¹' event ⊆ (ideal ⁻¹' event) ∪ {ω | real ω ≠ ideal ω} := by
    intro ω hω
    by_cases he : real ω = ideal ω
    · exact Or.inl (he ▸ hω)
    · exact Or.inr he
  exact (measure_mono hs).trans (measure_union_le _ _)

/-- The trace bound survives arbitrary independent public randomness, initial
state and program selection. The changed oracle may depend on the hidden
target; the baseline and program may only depend on the independent data.
An actual hybrid must establish precisely this product law. -/
theorem joint_reprogrammed_run_difference_bound {D R A : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (ν : Measure D) (μ : Measure R) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (ε : ENNReal) (mass : ∀ r, μ {r} ≤ ε)
    (parse : D → ByteArray → Option R) (baseline : D → Hash) (changed : D → R → Hash)
    (offTarget : ∀ data target input, parse data input ≠ some target →
      baseline data input = changed data target input)
    (program : D → Program A) (q : Nat) (bound : ∀ data, IsTotalQueryBound (program data) q)
    (measurable : MeasurableSet {sample : D × R |
      ROM.run (baseline sample.1) (program sample.1) ≠
        ROM.run (changed sample.1 sample.2) (program sample.1)}) :
    (ν.prod μ) {sample : D × R |
      ROM.run (baseline sample.1) (program sample.1) ≠
        ROM.run (changed sample.1 sample.2) (program sample.1)} ≤ (q : ENNReal)*ε := by
  rw [Measure.prod_apply measurable]
  calc
    _ ≤ ∫⁻ _ : D, (q : ENNReal)*ε ∂ν := by
      apply lintegral_mono
      intro data
      exact reprogrammed_run_difference_bound μ ε mass (parse data)
        (baseline data) (changed data) (offTarget data) (program data) q (bound data)
    _ = (q : ENNReal)*ε := by simp

end WotsLamport.Submission
