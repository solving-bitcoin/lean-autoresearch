import WotsLamport.Submission.FieldTableLaw

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤
local instance : MeasurableSpace (Bytes 32 ⊕ Fin 65537) := ⊤

/-- The first block stays byte-for-byte public. Only coefficient blocks are
reduced modulo the field size. Tags keep these two representations distinct. -/
def nonceFieldBlock {n : Nat} (index : Fin (n+1)) (bytes : Bytes 32) :
    Bytes 32 ⊕ Fin 65537 :=
  if index.val = 0 then Sum.inl bytes else Sum.inr (fieldBlock bytes)

noncomputable def nonceFieldLaw {n : Nat} (index : Fin (n+1)) :
    Measure (Bytes 32 ⊕ Fin 65537) :=
  (uniformOn (Set.univ : Set (Bytes 32))).map (nonceFieldBlock index)

noncomputable def idealNonceFieldLaw {n : Nat} (index : Fin (n+1)) :
    Measure (Bytes 32 ⊕ Fin 65537) :=
  if index.val = 0 then
    (uniformOn (Set.univ : Set (Bytes 32))).map Sum.inl
  else (uniformOn (Set.univ : Set (Fin 65537))).map Sum.inr

instance {n : Nat} (index : Fin (n+1)) : IsProbabilityMeasure (nonceFieldLaw index) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

instance {n : Nat} (index : Fin (n+1)) : IsProbabilityMeasure (idealNonceFieldLaw index) := by
  unfold idealNonceFieldLaw
  split <;> exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

theorem nonceFieldLaw_lower {n : Nat} (index : Fin (n+1)) :
    Sampler.ordinaryWeight • idealNonceFieldLaw index ≤ nonceFieldLaw index := by
  classical
  by_cases hi : index.val = 0
  · have he : nonceFieldBlock index = Sum.inl := by funext bytes; simp [nonceFieldBlock, hi]
    simp only [idealNonceFieldLaw, hi, ↓reduceIte, nonceFieldLaw, he]
    intro event
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (Sampler.mul_right_mono Sampler.ordinaryWeight_le_one _).trans_eq (one_mul _)
  · have he : nonceFieldBlock index = Sum.inr ∘ fieldBlock := by
      funext bytes
      simp [nonceFieldBlock, hi]
    have lower : Sampler.ordinaryWeight • uniformOn (Set.univ : Set (Fin 65537)) ≤
        Sampler.fieldLaw := by
      rw [Sampler.fieldLaw, Sampler.reduced_integer_mixture]
      exact le_add_right le_rfl
    simp only [idealNonceFieldLaw, hi, ↓reduceIte, nonceFieldLaw, he]
    rw [← Measure.map_map Measurable.of_discrete Measurable.of_discrete, fieldBlock_law]
    intro event
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    simpa only [Measure.smul_apply, smul_eq_mul] using lower (Sum.inr ⁻¹' event)

def nonceFieldTable (n : Nat) (coins : Bytes ((n+1)*32)) :
    Fin (n+1) → Bytes 32 ⊕ Fin 65537 :=
  fun index => nonceFieldBlock index (byteBlocksEquiv (n+1) coins index)

theorem nonceFieldTable_nonce (n : Nat) (coins : Bytes ((n+1)*32)) :
    nonceFieldTable n coins 0 = Sum.inl (byteBlocksEquiv (n+1) coins 0) := by
  simp [nonceFieldTable, nonceFieldBlock]

theorem nonceFieldTable_coefficient (coins : Bytes randomnessBytes) (j : Fin coefficientCount) :
    nonceFieldTable coefficientCount coins j.succ = Sum.inr (fieldBlock (coefficientBlock coins j)) := by
  simp [nonceFieldTable, nonceFieldBlock, coefficientBlock, coefficientBlocks]

theorem nonceFieldTable_law (n : Nat) :
    (uniformOn (Set.univ : Set (Bytes ((n+1)*32)))).map (nonceFieldTable n) =
      Measure.pi (fun index : Fin (n+1) => nonceFieldLaw index) := by
  letI (index : Fin (n+1)) : IsProbabilityMeasure
      ((uniformOn (Set.univ : Set (Bytes 32))).map (nonceFieldBlock index)) :=
    Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  have hf : nonceFieldTable n =
      (fun blocks : Fin (n+1) → Bytes 32 => fun index => nonceFieldBlock index (blocks index)) ∘
      byteBlocksEquiv (n+1) := rfl
  rw [hf, ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    uniform_map_equiv (byteBlocksEquiv (n+1)), uniform_blocks_product,
    Measure.pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable)]
  rfl

/-- Joint closeness holds even for events depending on the raw nonce and all
coefficients together. One extra exceptional-block allowance avoids requiring
any independence assumption about the event itself. -/
theorem nonceFieldTable_event_bounds (n : Nat)
    (event : Set (Fin (n+1) → Bytes 32 ⊕ Fin 65537)) :
    uniformOn (Set.univ : Set (Bytes ((n+1)*32))) ((nonceFieldTable n) ⁻¹' event) ≤
        (Measure.pi (fun index : Fin (n+1) => idealNonceFieldLaw index)) event +
          ((n+1 : Nat) : ENNReal)*Sampler.exceptionWeight ∧
    (Measure.pi (fun index : Fin (n+1) => idealNonceFieldLaw index)) event ≤
        uniformOn (Set.univ : Set (Bytes ((n+1)*32))) ((nonceFieldTable n) ⁻¹' event) +
          ((n+1 : Nat) : ENNReal)*Sampler.exceptionWeight := by
  classical
  letI := Fintype.ofFinite (Bytes 32 ⊕ Fin 65537)
  have hlaw : uniformOn (Set.univ : Set (Bytes ((n+1)*32))) ((nonceFieldTable n) ⁻¹' event) =
      (Measure.pi (fun index : Fin (n+1) => nonceFieldLaw index)) event := by
    rw [← nonceFieldTable_law, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [hlaw]
  exact probability_event_bounds _ _ (Sampler.ordinaryWeight^(n+1))
    (((n+1 : Nat) : ENNReal)*Sampler.exceptionWeight)
    (finite_family_domination (n+1) _ _ Sampler.ordinaryWeight nonceFieldLaw_lower)
    (bernoulli_mixture_bound _ _ Sampler.mixture_weights (n+1)) event MeasurableSet.of_discrete

theorem nonce_and_allocated_joint_loss :
    ((coefficientCount+1 : Nat) : ENNReal)*Sampler.exceptionWeight < 1/(2 : ENNReal)^233 := by
  norm_num [coefficientCount, Sampler.exceptionWeight, Sampler.sampleSize] <;>
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp <;> norm_num

end WotsLamport.Submission
