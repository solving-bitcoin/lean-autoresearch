import G1Release.Submission.BoundaryFacts
import G1Release.Submission.CoinSampler
import G1Release.Submission.ProductSampling

namespace G1Release.Submission.Randomized
open G1Release.Math G1Release.Protected SecretRelease
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def coordinateShapeEquiv : OracleCoordinate ≃
    (Fin 160 ⊕ Fin 161 ⊕ (Fin 161 × Fin 8) ⊕
      (Fin 161 × ProjectiveMap.TableKind × Fin 253)) where
  toFun
    | .offset i => .inl i
    | .randomizer i => .inr (.inl i)
    | .chain i j => .inr (.inr (.inl (i,j)))
    | .table i k j => .inr (.inr (.inr (i,k,j)))
  invFun
    | .inl i => .offset i
    | .inr (.inl i) => .randomizer i
    | .inr (.inr (.inl (i,j))) => .chain i j
    | .inr (.inr (.inr (i,k,j))) => .table i k j
  left_inv c := by cases c <;> rfl
  right_inv c := by rcases c with i | i | ⟨i,j⟩ | ⟨i,k,j⟩ <;> rfl

theorem coordinate_card : Nat.card OracleCoordinate = coordinateCount := by
  rw [Nat.card_congr coordinateShapeEquiv]
  have hk : Fintype.card ProjectiveMap.TableKind = 11 := rfl
  simp [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod, hk, coordinateCount]

noncomputable def coordinateEquiv : OracleCoordinate ≃ Fin coordinateCount :=
  Equiv.ofBijective coordinateSlot
    ((Nat.bijective_iff_injective_and_card _).2
      ⟨coordinateSlot_injective, by simpa only [Nat.card_fin] using coordinate_card⟩)

noncomputable def tapeEquiv : SecretRelease.Bytes coinBytes ≃
    (OracleCoordinate → Fin (2^512)) where
  toFun tape c := FiniteProbability.bytesFinEquiv 64
    (FiniteProbability.blockEquiv coordinateCount 64 tape (coordinateSlot c))
  invFun values := (FiniteProbability.blockEquiv coordinateCount 64).symm
    (fun i => (FiniteProbability.bytesFinEquiv 64).symm (values (coordinateEquiv.symm i)))
  left_inv tape := by
    apply (FiniteProbability.blockEquiv coordinateCount 64).injective
    funext i
    simp only [Equiv.apply_symm_apply]
    change (FiniteProbability.bytesFinEquiv 64).symm
      (FiniteProbability.bytesFinEquiv 64
        (FiniteProbability.blockEquiv coordinateCount 64 tape
          (coordinateEquiv (coordinateEquiv.symm i)))) = _
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv values := by
    funext c
    simp only [Equiv.apply_symm_apply]
    change values (coordinateEquiv.symm (coordinateEquiv c)) = values c
    rw [Equiv.symm_apply_apply]

theorem sampleCoordinates_eq (coins : SecretRelease.Bytes coinBytes) :
    sampleCoordinates coins =
      ProductSampling.sample (2^512) rawModulus rawModulus_pos (tapeEquiv coins) := rfl

noncomputable def samplingError : ℝ := ∑ c : OracleCoordinate, (rawModulus c : ℝ) / (2:ℝ)^512

theorem sample_event_probability_bounds (hidden : Hidden) (event : Set (Randomness hidden)) :
    (uniformOn Set.univ ((fun coins => sample coins hidden) ⁻¹' event)).toReal ≤
        (idealLaw hidden event).toReal + samplingError ∧
      (idealLaw hidden event).toReal ≤
        (uniformOn Set.univ ((fun coins => sample coins hidden) ⁻¹' event)).toReal + samplingError := by
  classical
  have hb := ProductSampling.event_probability_bounds (ι := OracleCoordinate)
    (2^512) rawModulus (by positivity) rawModulus_pos
      (rawRandomnessEquiv hidden ⁻¹' event)
  have hpre : Nat.card ((fun coins => sample coins hidden) ⁻¹' event) =
      Nat.card (ProductSampling.sample (2^512) rawModulus rawModulus_pos ⁻¹'
        (rawRandomnessEquiv hidden ⁻¹' event)) := by
    have hset : ((fun coins => sample coins hidden) ⁻¹' event) = tapeEquiv ⁻¹'
        (ProductSampling.sample (2^512) rawModulus rawModulus_pos ⁻¹'
          (rawRandomnessEquiv hidden ⁻¹' event)) := by
      ext coins
      simp only [Set.mem_preimage, sample_eq, sampleCoordinates_eq]
    rw [hset]
    exact Nat.card_congr (FiniteProbability.preimageEquiv tapeEquiv _)
  have hraw := Nat.card_congr (rawRandomnessEquiv hidden)
  have hevent := Nat.card_congr (FiniteProbability.preimageEquiv (rawRandomnessEquiv hidden) event)
  have htape := Nat.card_congr tapeEquiv
  rw [FiniteProbability.uniform_real, idealLaw, FiniteProbability.uniform_real]
  rw [hpre, htape]
  simpa only [hevent, hraw, samplingError, Nat.cast_pow, Nat.cast_ofNat] using hb

set_option exponentiation.threshold 1024 in
theorem samplingError_le : samplingError ≤ (2:ℝ)^(-239 : ℤ) := by
  have hm (c : OracleCoordinate) : rawModulus c ≤ 2^254 := by
    cases c <;> norm_num [rawModulus, baseFieldModulus, BoundaryFacts.scalar_modulus]
  calc
    samplingError ≤ ∑ _ : OracleCoordinate, (2:ℝ)^254 / (2:ℝ)^512 := by
      apply Finset.sum_le_sum
      intro c _
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hm c
    _ = (coordinateCount : ℝ) * ((2:ℝ)^254 / (2:ℝ)^512) := by
      simp [← Nat.card_eq_fintype_card, coordinate_card]
    _ ≤ (2:ℝ)^(-239 : ℤ) := by norm_num [coordinateCount]

end G1Release.Submission.Randomized
