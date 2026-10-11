import WotsLamport.Submission.OracleOverlay

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- Swap newly supplied cell answers with the answers they overwrite. The
entire oracle table is retained, so this transports a joint distribution. -/
noncomputable def overlaySwapEquiv {I D R : Type} (address : I → D)
    (injective : Function.Injective address) :
    ((I → R) × (D → R)) ≃ ((D → R) × (I → R)) where
  toFun sample := (overlayOracle address sample.1 sample.2, sample.2 ∘ address)
  invFun sample := (sample.1 ∘ address, overlayOracle address sample.2 sample.1)
  left_inv sample := by
    refine Prod.ext ?_ (overlayOracle_restore address injective sample.2 sample.1)
    funext i
    exact overlayOracle_at address sample.1 sample.2 injective i
  right_inv sample := by
    refine Prod.ext (overlayOracle_restore address injective sample.1 sample.2) ?_
    funext i
    exact overlayOracle_at address sample.2 sample.1 injective i

theorem uniform_overlay_joint_event {I D R : Type} [Fintype I] [Fintype D] [Fintype R]
    [Nonempty R] [MeasurableSpace R] [DiscreteMeasurableSpace R]
    (address : I → D) (injective : Function.Injective address)
    (event : Set ((I → R) × (D → R))) :
    uniformOn (Set.univ : Set ((I → R) × (D → R)))
      {sample | (sample.1, overlayOracle address sample.1 sample.2) ∈ event} =
    uniformOn (Set.univ : Set (D → R))
      {oracle | (oracle ∘ address, oracle) ∈ event} := by
  classical
  let e := overlaySwapEquiv (R := R) address injective
  let target : Set ((D → R) × (I → R)) :=
    {sample | (sample.1 ∘ address, sample.1) ∈ event}
  have he : {sample : (I → R) × (D → R) |
      (sample.1, overlayOracle address sample.1 sample.2) ∈ event} = e ⁻¹' target := by
    ext sample
    have readback : overlayOracle address sample.1 sample.2 ∘ address = sample.1 := by
      funext i
      exact overlayOracle_at address _ _ injective i
    change _ ↔ (overlayOracle address sample.1 sample.2 ∘ address,
      overlayOracle address sample.1 sample.2) ∈ event
    rw [readback]
  rw [he, Shamir.uniform_event_equiv e]
  change uniformOn (Set.univ : Set ((D → R) × (I → R)))
    ({oracle | (oracle ∘ address, oracle) ∈ event} ×ˢ Set.univ) = _
  rw [uniform_product, Measure.prod_prod, measure_univ, mul_one]

theorem overlayOracle_commute {I J D R : Type} (a : I → D) (b : J → D)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (disjoint : ∀ i j, a i ≠ b j) (av : I → R) (bv : J → R) (base : D → R) :
    overlayOracle a av (overlayOracle b bv base) =
      overlayOracle b bv (overlayOracle a av base) := by
  classical
  funext input
  rcases Classical.em (∃ i, a i = input) with foundA | foundA
  · obtain ⟨i,rfl⟩ := foundA
    have offB : ∀ j, b j ≠ a i := fun j => (disjoint i j).symm
    rw [overlayOracle_at a av _ ha i, overlayOracle_off b bv _ _ offB,
      overlayOracle_at a av base ha i]
  · have offA : ∀ i, a i ≠ input := by intro i hi; exact foundA ⟨i,hi⟩
    rcases Classical.em (∃ j, b j = input) with foundB | foundB
    · obtain ⟨j,rfl⟩ := foundB
      rw [overlayOracle_off a av _ _ offA, overlayOracle_at b bv base hb j,
        overlayOracle_at b bv _ hb j]
    · have offB : ∀ j, b j ≠ input := by intro j hj; exact foundB ⟨j,hj⟩
      rw [overlayOracle_off a av _ _ offA, overlayOracle_off b bv _ _ offB,
        overlayOracle_off b bv _ _ offB, overlayOracle_off a av _ _ offA]

end WotsLamport.Submission
