import GarblingPrize.Submission.GLVCompactOracleLaw

namespace GarblingPrize.Submission.HintProductLaw

/-! Regroup independent oracle and label coordinates. These equalities concern
countable product measures, so they retain the entire active-label oracle. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι κ : Type*}

theorem infinitePi_sum_symm {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι ⊕ κ) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i))) (Measure.infinitePi μ) := by
  refine ⟨(MeasurableEquiv.sumPiEquivProdPi X).symm.measurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' (s : Set (ι ⊕ κ)).pi t =
      ((s.toLeft : Set ι).pi (fun i => t (.inl i))) ×ˢ
      ((s.toRight : Set κ).pi (fun i => t (.inr i))) := by
    ext state
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h (.inl i) hi, fun i hi => h (.inr i) hi⟩
    · rintro ⟨hl, hr⟩ (i | i) hi
      · exact hl i hi
      · exact hr i hi
  rw [hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun i _ => ht (.inl i)),
    Measure.infinitePi_pi _ (fun i _ => ht (.inr i)),
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

theorem infinitePi_sum {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι ⊕ κ) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X)
      (Measure.infinitePi μ)
      ((Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i))) :=
  (infinitePi_sum_symm μ).symm (MeasurableEquiv.sumPiEquivProdPi X).symm

theorem infinitePi_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : ι → Measure A) (ν : ι → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving (fun state : (ι → A) × (ι → B) => fun i => (state.1 i, state.2 i))
      ((Measure.infinitePi μ).prod (Measure.infinitePi ν))
      (Measure.infinitePi fun i => (μ i).prod (ν i)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  let restrictA : MeasurePreserving (s.restrict : (ι → A) → (s → A))
      (Measure.infinitePi μ) (Measure.pi fun i : s => μ i) :=
    ⟨by fun_prop, Measure.infinitePi_map_restrict μ⟩
  let restrictB : MeasurePreserving (s.restrict : (ι → B) → (s → B))
      (Measure.infinitePi ν) (Measure.pi fun i : s => ν i) :=
    ⟨by fun_prop, Measure.infinitePi_map_restrict ν⟩
  have hfinite := (measurePreserving_arrowProdEquivProdArrow A B s
    (fun i => μ i) (fun i => ν i)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow A B s)
  have h := hfinite.comp (restrictA.prod restrictB)
  have hm : MeasurableSet (Set.univ.pi (fun i : s => t i)) :=
    MeasurableSet.univ_pi (fun i => ht i)
  rw [Measure.map_apply (by fun_prop)
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (fun state : (ι → A) × (ι → B) => fun i => (state.1 i, state.2 i)) ⁻¹'
      (s : Set ι).pi t =
      ((MeasurableEquiv.arrowProdEquivProdArrow A B s).symm ∘
        Prod.map s.restrict s.restrict) ⁻¹' Set.univ.pi (fun i : s => t i) := by
    ext state
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
      Function.comp_def]
  rw [hpre, h.measure_preimage hm.nullMeasurableSet, Measure.pi_pi]
  simp only [Finset.univ_eq_attach]
  exact Finset.prod_attach s (fun i => ((μ i).prod (ν i)) (t i))

theorem infinitePi_map {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : (i : ι) → Measure (X i)) (ν : (i : ι) → Measure (Y i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (f : (i : ι) → X i → Y i) (hf : ∀ i, MeasurePreserving (f i) (μ i) (ν i)) :
    MeasurePreserving (fun state i => f i (state i)) (Measure.infinitePi μ)
      (Measure.infinitePi ν) := by
  refine ⟨measurable_pi_lambda _ (fun i => (hf i).measurable.comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.infinitePi_map_pi _ (fun i => (hf i).measurable)]
  congr 1
  funext i
  exact (hf i).map_eq

theorem infinitePi_swap {X : Type*} [MeasurableSpace X]
    (μ : ι → κ → Measure X) [∀ i j, IsProbabilityMeasure (μ i j)] :
    MeasurePreserving (fun state : ι → κ → X => fun j i => state i j)
      (Measure.infinitePi fun i => Measure.infinitePi (μ i))
      (Measure.infinitePi fun j => Measure.infinitePi fun i => μ i j) := by
  have hflat : MeasurePreserving (MeasurableEquiv.curry ι κ X).symm
      (Measure.infinitePi fun i => Measure.infinitePi (μ i))
      (Measure.infinitePi fun p : ι × κ => μ p.1 p.2) :=
    ⟨by fun_prop, Measure.infinitePi_map_curry_symm μ⟩
  have hswap : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => X) (Equiv.prodComm ι κ))
      (Measure.infinitePi fun p : ι × κ => μ p.1 p.2)
      (Measure.infinitePi fun p : κ × ι => μ p.2 p.1) :=
    ⟨by fun_prop, Measure.infinitePi_map_piCongrLeft
      (fun p : κ × ι => μ p.2 p.1) (Equiv.prodComm ι κ)⟩
  have hcur : MeasurePreserving (MeasurableEquiv.curry κ ι X)
      (Measure.infinitePi fun p : κ × ι => μ p.2 p.1)
      (Measure.infinitePi fun j => Measure.infinitePi fun i => μ i j) :=
    ⟨by fun_prop, Measure.infinitePi_map_curry (fun j i => μ i j)⟩
  exact hcur.comp (hswap.comp hflat)

end GarblingPrize.Submission.HintProductLaw
