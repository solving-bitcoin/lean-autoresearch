import WotsLamport.Submission.OracleSupport

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

abbrev OracleInput := List (Fin 256)

def oracleInput (bytes : ByteArray) : OracleInput := bytes.data.toList.map UInt8.toFin

noncomputable def oracleLaw : Measure ROM.Oracle :=
  Measure.infinitePi fun _ : OracleInput => uniformOn (Set.univ : Set Label)

noncomputable def extendOracleTable (inputs : Finset OracleInput)
    (answers : inputs → Label) : ROM.Oracle := by
  classical
  exact fun input => if hi : input ∈ inputs then answers ⟨input, hi⟩ else Vector.replicate 32 0

/-- The protected infinite random function has exactly the uniform finite
table law on every fixed finite set of inputs. -/
theorem oracle_restriction_law (inputs : Finset OracleInput) :
    oracleLaw.map inputs.restrict = uniformOn (Set.univ : Set (inputs → Label)) := by
  rw [oracleLaw, Measure.infinitePi_map_restrict]
  simpa using (uniformOn_pi (f := fun _ : inputs => (Set.univ : Set Label))).symm

/-- A total free oracle program depends on finitely many coordinates. This
does not bound the size of that set by its pathwise query budget. It permits
finite-table distribution arguments without replacing the protected ROM. -/
theorem program_finite_table_representation {A : Type} (p : Program A) :
    ∃ inputs : Finset OracleInput, ∀ oracle : ROM.Oracle,
      ROM.run (ROM.hash oracle) p =
        ROM.run (ROM.hash (extendOracleTable inputs (inputs.restrict oracle))) p := by
  classical
  obtain ⟨support, agrees⟩ := program_finite_query_support p
  let inputs := support.image oracleInput
  refine ⟨inputs, ?_⟩
  intro oracle
  apply agrees
  intro input hi
  have hmem : oracleInput input ∈ inputs := Finset.mem_image.mpr ⟨input, hi, rfl⟩
  change oracle (oracleInput input) =
    extendOracleTable inputs (inputs.restrict oracle) (oracleInput input)
  simp only [extendOracleTable, dif_pos hmem]
  rfl

/-- Every output event of a fixed program has an exact finite uniform-table
probability. The event need not be measurable on its ambient output type:
the finite answer-table preimage is discrete and measurable. -/
theorem program_finite_table_probability {A : Type} (p : Program A) (event : Set A) :
    ∃ inputs : Finset OracleInput,
      oracleLaw {oracle | ROM.run (ROM.hash oracle) p ∈ event} =
        uniformOn (Set.univ : Set (inputs → Label))
          {answers | ROM.run (ROM.hash (extendOracleTable inputs answers)) p ∈ event} := by
  classical
  obtain ⟨inputs, agrees⟩ := program_finite_table_representation p
  refine ⟨inputs, ?_⟩
  let tableEvent : Set (inputs → Label) :=
    {answers | ROM.run (ROM.hash (extendOracleTable inputs answers)) p ∈ event}
  have he : {oracle | ROM.run (ROM.hash oracle) p ∈ event} =
      inputs.restrict ⁻¹' tableEvent := by
    ext oracle
    change (ROM.run (ROM.hash oracle) p ∈ event) ↔
      (ROM.run (ROM.hash (extendOracleTable inputs (inputs.restrict oracle))) p ∈ event)
    rw [agrees]
  rw [he, ← Measure.map_apply inputs.measurable_restrict MeasurableSet.of_discrete,
    oracle_restriction_law]

end WotsLamport.Submission
