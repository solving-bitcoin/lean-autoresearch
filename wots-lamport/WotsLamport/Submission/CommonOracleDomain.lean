import WotsLamport.Submission.FiniteOracleLaw
import WotsLamport.Submission.DomainSeparation

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- A mathematical finite set, never enumerated by the executable. It includes
every byte string of the stated length before any secrets are sampled. -/
noncomputable def fullWidthInputs (n : Nat) : Finset OracleInput := by
  classical
  letI := Fintype.ofFinite (Bytes n)
  exact Finset.univ.image (fun bytes : Bytes n => oracleInput (ByteArray.mk bytes.toArray))

theorem fullWidthInputs_mem (n : Nat) (bytes : ByteArray) (size : bytes.size = n) :
    oracleInput bytes ∈ fullWidthInputs n := by
  classical
  unfold fullWidthInputs
  exact Finset.mem_image.mpr ⟨⟨bytes.data, size⟩, Finset.mem_univ _, rfl⟩

noncomputable def wotsProgrammingInputs : Finset OracleInput :=
  fullWidthInputs 32 ∪ fullWidthInputs 2232 ∪ fullWidthInputs 2234

theorem chain_input_in_programming_domain (node : Label) :
    oracleInput (ByteArray.mk node.toArray) ∈ wotsProgrammingInputs := by
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
    (fullWidthInputs_mem 32 _ (vectorBytes_size node)))))

theorem mask_input_in_programming_domain (pk nonce : ByteArray)
    (pkSize : pk.size = 2144) (nonceSize : nonce.size = 32)
    (wire : Nat) (value : Bool) (point : Nat) (node : Label) (block : Nat) :
    oracleInput (maskQuery pk nonce wire value point node block) ∈ wotsProgrammingInputs := by
  apply Finset.mem_union.mpr
  apply Or.inr
  apply fullWidthInputs_mem
  rw [maskQuery_size, pkSize, nonceSize]

theorem commitment_input_in_programming_domain (pk nonce : ByteArray)
    (pkSize : pk.size = 2144) (nonceSize : nonce.size = 32)
    (wire : Nat) (value : Bool) (label : Label) :
    oracleInput (commitmentQuery pk nonce wire value label) ∈ wotsProgrammingInputs := by
  apply Finset.mem_union.mpr
  apply Or.inl
  apply Finset.mem_union.mpr
  apply Or.inr
  apply fullWidthInputs_mem
  rw [commitmentQuery_size, pkSize, nonceSize]

/-- One finite table suffices jointly for every member of a finite setup
family. Additional finite domains can be included for later programming.
There is deliberately no cardinality bound by the pathwise query budget. -/
theorem program_family_finite_table_representation {I A : Type} [Fintype I]
    (program : I → Program A) (extra : Finset OracleInput) :
    ∃ inputs : Finset OracleInput, extra ⊆ inputs ∧ ∀ i (oracle : ROM.Oracle),
      ROM.run (ROM.hash oracle) (program i) =
        ROM.run (ROM.hash (extendOracleTable inputs (inputs.restrict oracle))) (program i) := by
  classical
  choose support agrees using fun i => program_finite_query_support (program i)
  let inputs := extra ∪ Finset.univ.biUnion (fun i : I => (support i).image oracleInput)
  refine ⟨inputs, Finset.subset_union_left, ?_⟩
  intro i oracle
  apply agrees i
  intro input member
  have hmem : oracleInput input ∈ inputs :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨input,member,rfl⟩⟩))
  change oracle (oracleInput input) =
    extendOracleTable inputs (inputs.restrict oracle) (oracleInput input)
  simp only [extendOracleTable, dif_pos hmem]
  rfl

/-- All setup-indexed output events use the same finite uniform oracle law.
This supplies a common domain for a later joint counting argument; it does
not assert that independently programmed cells have the real distribution. -/
theorem program_family_finite_table_probability {I A : Type} [Fintype I]
    (program : I → Program A) (event : I → Set A) (extra : Finset OracleInput) :
    ∃ inputs : Finset OracleInput, extra ⊆ inputs ∧ ∀ i,
      oracleLaw {oracle | ROM.run (ROM.hash oracle) (program i) ∈ event i} =
        uniformOn (Set.univ : Set (inputs → Label))
          {answers | ROM.run (ROM.hash (extendOracleTable inputs answers)) (program i) ∈ event i} := by
  classical
  obtain ⟨inputs, contains, agrees⟩ := program_family_finite_table_representation program extra
  refine ⟨inputs, contains, ?_⟩
  intro i
  let tableEvent : Set (inputs → Label) :=
    {answers | ROM.run (ROM.hash (extendOracleTable inputs answers)) (program i) ∈ event i}
  have he : {oracle | ROM.run (ROM.hash oracle) (program i) ∈ event i} =
      inputs.restrict ⁻¹' tableEvent := by
    ext oracle
    change (ROM.run (ROM.hash oracle) (program i) ∈ event i) ↔
      (ROM.run (ROM.hash (extendOracleTable inputs (inputs.restrict oracle))) (program i) ∈ event i)
    rw [agrees]
  rw [he, ← Measure.map_apply inputs.measurable_restrict MeasurableSet.of_discrete,
    oracle_restriction_law]

end WotsLamport.Submission
