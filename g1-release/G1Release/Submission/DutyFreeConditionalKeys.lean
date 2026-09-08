import G1Release.Submission.DutyFreeKeySplit

/-! Condition jointly on the selected Lamport labels and all fifteen
available bridge keys in every nibble. The remaining external ranks and
hidden bridge keys are independent uniform coordinates. -/
namespace G1Release.Submission.DutyFreeConditionalKeys

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
open SecretRelease G1Release.Protected DutyFreeSlots
open MeasureTheory ProbabilityTheory

abbrev KeyPair := Keys × HotKeys
abbrev Revealed (input : Input) := DutyFreeIdeal.Active × DutyFreeKeySplit.Public input
abbrev Hidden := (Fin 512 → LamportLaw.Rank) × DutyFreeKeySplit.Hidden

def shuffle (A R H P : Type*) : (A × R) × (H × P) ≃ (A × P) × (R × H) where
  toFun s := ((s.1.1,s.2.2),(s.1.2,s.2.1))
  invFun s := ((s.1.1,s.2.1),(s.2.2,s.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def split (input : Input) : KeyPair ≃ Revealed input × Hidden :=
  (Equiv.prodCongr (LamportLaw.keysEquiv (fun wire => (inputCodec.encode input)[wire.val]))
    (DutyFreeKeySplit.split input)).trans (shuffle _ _ _ _)

theorem bound {X : Type*} [MeasurableSpace X]
    (input : Input) (context : Measure X) [IsProbabilityMeasure context]
    (event : Set (KeyPair × X)) (he : MeasurableSet event) (error : ENNReal)
    (hc : ∀ revealed x,
      uniformOn (Set.univ : Set Hidden)
        {hidden | ((split input).symm (revealed,hidden),x) ∈ event} ≤ error) :
    ((uniformOn (Set.univ : Set KeyPair)).prod context) event ≤ error := by
  let revealedLaw : Measure (Revealed input) := uniformOn Set.univ
  let hiddenLaw : Measure Hidden := uniformOn Set.univ
  have hk : MeasurePreserving (split input).symm
      (revealedLaw.prod hiddenLaw) (uniformOn (Set.univ : Set KeyPair)) := by
    rw [show revealedLaw.prod hiddenLaw = uniformOn Set.univ from LamportLaw.prod_uniform_univ]
    exact FiniteProbability.uniform_equiv (split input).symm
  have hm := hk.prod (MeasurePreserving.id context)
  let pulled : Set ((Revealed input × Hidden) × X) :=
    (fun s => ((split input).symm s.1,s.2)) ⁻¹' event
  have hp : MeasurableSet pulled := hm.measurable he
  rw [← hm.measure_preimage he.nullMeasurableSet]
  change ((revealedLaw.prod hiddenLaw).prod context) pulled ≤ error
  rw [Measure.prod_apply_symm hp]
  calc
    (∫⁻ x, (revealedLaw.prod hiddenLaw) ((fun pair => (pair,x)) ⁻¹' pulled) ∂context) ≤
        ∫⁻ _ : X, error ∂context := by
      apply lintegral_mono
      intro x
      dsimp only
      have hx : MeasurableSet ((fun pair => (pair,x)) ⁻¹' pulled) := measurable_prodMk_right hp
      rw [Measure.prod_apply (μ := revealedLaw) (ν := hiddenLaw) hx]
      calc
        (∫⁻ revealed, hiddenLaw (Prod.mk revealed ⁻¹' ((fun pair => (pair,x)) ⁻¹' pulled)) ∂revealedLaw) ≤
            ∫⁻ _ : Revealed input, error ∂revealedLaw := by
          apply lintegral_mono
          intro revealed
          exact hc revealed x
        _ = error := by simp [revealedLaw]
    _ = error := by simp

end G1Release.Submission.DutyFreeConditionalKeys
