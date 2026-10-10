import WotsLamport.Submission.OracleMeasureBridge
import WotsLamport.Submission.OraclePrograms

namespace WotsLamport.Submission
open SecretRelease OracleSpec OracleComp MeasureTheory ProbabilityTheory

/-- Replay a program through a finite table. Inputs outside the table return
the same fixed value as `extendOracleTable`; the finite-support theorem later
shows these fallback inputs are irrelevant to the original program. -/
noncomputable def restrictedOracleProgram {A : Type} (inputs : Finset OracleInput)
    (p : Program A) : OracleComp (inputs →ₒ Label) A := by
  classical
  exact OracleComp.construct (C := fun _ => OracleComp (inputs →ₒ Label) A)
    (fun a => pure a)
    (fun input _ tail => if hi : oracleInput input ∈ inputs then
      (liftM ((inputs →ₒ Label).query ⟨oracleInput input, hi⟩) >>= tail)
      else tail (Vector.replicate 32 0)) p

theorem run_restrictedOracleProgram {A : Type} (inputs : Finset OracleInput)
    (answers : inputs → Label) (p : Program A) :
    ROM.run (ROM.hash (extendOracleTable inputs answers)) p =
      evalWithAnswerFn (QueryImpl.ofFn answers) (restrictedOracleProgram inputs p) := by
  classical
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind input next ih =>
    rw [run_query_bind]
    change ROM.run (ROM.hash (extendOracleTable inputs answers))
        (next (ROM.hash (extendOracleTable inputs answers) input)) =
      evalWithAnswerFn (QueryImpl.ofFn answers)
        (if hi : oracleInput input ∈ inputs then
          (liftM ((inputs →ₒ Label).query ⟨oracleInput input, hi⟩) >>=
            fun answer => restrictedOracleProgram inputs (next answer))
          else restrictedOracleProgram inputs (next (Vector.replicate 32 0)))
    by_cases hi : oracleInput input ∈ inputs
    · rw [dif_pos hi, evalWithAnswerFn_bind]
      simp only [evalWithAnswerFn, simulateQ_spec_query, QueryImpl.ofFn_apply]
      change ROM.run (ROM.hash (extendOracleTable inputs answers))
        (next (extendOracleTable inputs answers (oracleInput input))) = _
      rw [show extendOracleTable inputs answers (oracleInput input) =
        answers ⟨oracleInput input, hi⟩ by simp [extendOracleTable, hi]]
      exact ih _
    · rw [dif_neg hi]
      change ROM.run (ROM.hash (extendOracleTable inputs answers))
        (next (extendOracleTable inputs answers (oracleInput input))) = _
      rw [show extendOracleTable inputs answers (oracleInput input) =
        Vector.replicate 32 0 by simp [extendOracleTable, hi]]
      exact ih _

/-- Restriction never increases the pathwise query budget. -/
theorem restrictedOracleProgram_query_bound {A : Type} (inputs : Finset OracleInput)
    (p : Program A) (q : Nat) (bound : IsTotalQueryBound p q) :
    IsTotalQueryBound (restrictedOracleProgram inputs p) q := by
  classical
  induction p using OracleComp.inductionOn generalizing q with
  | pure a => exact isQueryBound_pure a q _ _
  | query_bind input next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bound
    change IsTotalQueryBound
      (if hi : oracleInput input ∈ inputs then
        (liftM ((inputs →ₒ Label).query ⟨oracleInput input, hi⟩) >>=
          fun answer => restrictedOracleProgram inputs (next answer))
        else restrictedOracleProgram inputs (next (Vector.replicate 32 0))) q
    by_cases hi : oracleInput input ∈ inputs
    · rw [dif_pos hi, isTotalQueryBound_query_bind_iff]
      exact ⟨bound.1, fun answer => ih answer (q-1) (bound.2 answer)⟩
    · rw [dif_neg hi]
      exact (ih _ (q-1) (bound.2 _)).mono (Nat.sub_le q 1)

/-- Exact output-event equivalence with a finite lazy random oracle. The
finite input set may be enormous; this is a proof device, not an executable
enumeration or a claim that its cardinality is the query bound. -/
theorem protected_oracle_eq_finite_lazy (p : Program Bool) (event : Set Bool) :
    ∃ inputs : Finset OracleInput,
      oracleLaw {oracle | ROM.run (ROM.hash oracle) p ∈ event} =
        (evalSPMF ((simulateQ randomOracle
          (restrictedOracleProgram inputs p)).run' ∅)).toMeasure event := by
  classical
  obtain ⟨inputs, he⟩ := program_finite_table_probability p event
  refine ⟨inputs, ?_⟩
  rw [he, finite_randomOracle_measure,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  congr 1
  ext answers
  change (ROM.run (ROM.hash (extendOracleTable inputs answers)) p ∈ event) ↔ _
  rw [run_restrictedOracleProgram]

end WotsLamport.Submission
