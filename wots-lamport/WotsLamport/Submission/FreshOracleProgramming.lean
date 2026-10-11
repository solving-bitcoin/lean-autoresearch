import WotsLamport.Submission.OracleMeasureBridge

namespace WotsLamport.Submission
open SecretRelease OracleSpec OracleComp

variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)]

/-- A newly sampled answer and the programmed table have the same joint law
as reading that cell from a uniform table. This preserves the table itself,
not merely the marginal law of the answer. -/
theorem fresh_cell_joint_law (input : D) :
    evalSPMF (do
      let answer ← uniformSample R
      let baseline ← uniformSample (D → R)
      pure (answer, Function.update baseline input answer)) =
    evalSPMF (do
      let oracle ← uniformSample (D → R)
      pure (oracle input, oracle)) := by
  simpa only [Function.update_same] using
    evalSPMF_uniformSample_bind_update_map input (fun oracle => (oracle input, oracle))

/-- The same joint law holds in the presence of an already fixed cache,
provided the new input has not been cached. Reusing a cached address does
not satisfy this premise and must be handled separately as a collision. -/
theorem fresh_cached_cell_joint_law (cache : (D →ₒ R).QueryCache)
    (input : D) (fresh : cache input = none) :
    evalSPMF (do
      let answer ← uniformSample R
      let baseline ← uniformSample (D → R)
      pure (answer, tableExtending (cache.cacheQuery input answer) baseline)) =
    evalSPMF (do
      let baseline ← uniformSample (D → R)
      pure (tableExtending cache baseline input, tableExtending cache baseline)) := by
  have replace (baseline : D → R) (answer : R) :
      (tableExtending cache (Function.update baseline input answer) input,
        tableExtending cache (Function.update baseline input answer)) =
      (answer, tableExtending (cache.cacheQuery input answer) baseline) := by
    simp only [← tableExtending_update_of_none cache baseline fresh answer,
      Function.update_same, tableExtending_cacheQuery]
  simpa only [replace] using
    evalSPMF_uniformSample_bind_update_map input
      (fun baseline => (tableExtending cache baseline input, tableExtending cache baseline))

end WotsLamport.Submission
