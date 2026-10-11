import WotsLamport.Submission.GamePrograms
import WotsLamport.Submission.CommonOracleDomain
import WotsLamport.Submission.ChainPartitionLaw

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

local instance : MeasurableSpace Keys := ⊤
local instance : MeasurableSpace (Fin 256 → Pair) := ⊤

def flattenInitialSample (sample : InitialData × ROM.Oracle) : ROM.Sample (wrapped construction) :=
  (sample.1.1, sample.1.2.1, sample.1.2.2, sample.2)

theorem flattenInitialSample_measurable : Measurable flattenInitialSample :=
  (measurable_fst.fst).prodMk ((measurable_fst.snd.fst).prodMk
    ((measurable_fst.snd.snd).prodMk measurable_snd))

/-- This is precisely the protected key/label/coin/oracle product law,
regrouped as finite initial data and its independent infinite oracle. -/
theorem grouped_sample_law :
    ((uniformOn (Set.univ : Set InitialData)).prod oracleLaw).map flattenInitialSample =
      ROM.law (wrapped construction) := by
  classical
  letI := Fintype.ofFinite Keys
  letI := Fintype.ofFinite (Fin 256 → Pair)
  letI := Fintype.ofFinite (Bytes randomnessBytes)
  have regroup : flattenInitialSample =
      (Prod.map id (MeasurableEquiv.prodAssoc :
        ((Fin 256 → Pair) × Bytes randomnessBytes) × ROM.Oracle ≃ᵐ
          (Fin 256 → Pair) × Bytes randomnessBytes × ROM.Oracle)) ∘
      (MeasurableEquiv.prodAssoc :
        (Keys × ((Fin 256 → Pair) × Bytes randomnessBytes)) × ROM.Oracle ≃ᵐ
          Keys × ((Fin 256 → Pair) × Bytes randomnessBytes) × ROM.Oracle) := rfl
  rw [regroup, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable
    (measurable_id.prodMap MeasurableEquiv.prodAssoc.measurable)]
  rw [uniform_product, uniform_product, Measure.prodAssoc_prod,
    ← Measure.map_prod_map _ _ measurable_id MeasurableEquiv.prodAssoc.measurable,
    Measure.map_id, Measure.prodAssoc_prod]
  rfl

/-- One finite oracle domain represents the complete setup-dependent game,
not merely a fixed program after secrets have already been sampled. -/
theorem protected_game_finite_joint_law (game : InitialData → Program Bool)
    (extra : Finset OracleInput) :
    ∃ inputs : Finset OracleInput, extra ⊆ inputs ∧
      ROM.law (wrapped construction)
        {sample | ROM.run (ROM.hash sample.2.2.2)
          (game (sample.1, sample.2.1, sample.2.2.1)) = true} =
      uniformOn (Set.univ : Set (InitialData × (inputs → Label)))
        {sample | ROM.run (ROM.hash (extendOracleTable inputs sample.2)) (game sample.1) = true} := by
  classical
  letI := Fintype.ofFinite InitialData
  letI := Fintype.ofFinite Label
  obtain ⟨inputs,contains,agrees⟩ :=
    program_family_finite_table_probability game (fun _ => {true}) extra
  refine ⟨inputs, contains, ?_⟩
  have originalMeasurable : MeasurableSet
      {sample : ROM.Sample (wrapped construction) |
        ROM.run (ROM.hash sample.2.2.2) (game (sample.1,sample.2.1,sample.2.2.1)) = true} :=
    measurable_game_run game (measurableSet_singleton true)
  have groupedMeasurable : MeasurableSet
      {sample : InitialData × ROM.Oracle |
        ROM.run (ROM.hash sample.2) (game sample.1) = true} :=
    (measurable_program_family game Prod.snd Prod.fst measurable_snd measurable_fst)
      (measurableSet_singleton true)
  rw [← grouped_sample_law, Measure.map_apply flattenInitialSample_measurable originalMeasurable]
  change ((uniformOn (Set.univ : Set InitialData)).prod oracleLaw)
    {sample | ROM.run (ROM.hash sample.2) (game sample.1) = true} = _
  rw [uniform_product, Measure.prod_apply groupedMeasurable,
    Measure.prod_apply MeasurableSet.of_discrete]
  apply lintegral_congr
  intro initial
  simpa only [Set.mem_singleton_iff] using agrees initial

end WotsLamport.Submission
