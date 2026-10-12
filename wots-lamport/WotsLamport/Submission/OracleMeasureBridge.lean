import WotsLamport.Submission.FiniteOracleLaw
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory OracleSpec OracleComp

/-- VCV's finite uniform sampler and the protected measure-theoretic uniform
law agree exactly. This bridges semantics; it introduces no sampling axiom. -/
theorem uniformSample_measure (A : Type) [Fintype A] [SampleableType A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] :
    (evalSPMF (uniformSample A)).toMeasure = uniformOn (Set.univ : Set A) := by
  apply Measure.ext_of_singleton
  intro a
  rw [SPMF.toMeasure_apply_singleton]
  change Pr[= a | uniformSample A] = _
  rw [probOutput_uniformSample, uniformOn_univ, Measure.count_singleton]
  simp

/-- The lazy finite random oracle has exactly the full uniform answer-table
measure. Together with `program_finite_table_probability`, this is the bridge
needed before importing VCV's lazy-oracle probability bounds into the ROM. -/
theorem finite_randomOracle_measure {D R A : Type}
    [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)]
    [MeasurableSpace R] [DiscreteMeasurableSpace R] [MeasurableSpace A]
    (p : OracleComp (D →ₒ R) A) :
    (evalSPMF ((simulateQ randomOracle p).run' ∅)).toMeasure =
      (uniformOn (Set.univ : Set (D → R))).map
        (fun table => evalWithAnswerFn (QueryImpl.ofFn table) p) := by
  rw [evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable]
  rw [bind_pure_comp, evalSPMF_map, SPMF.toMeasure_map _ _ Measurable.of_discrete,
    uniformSample_measure]

end WotsLamport.Submission
