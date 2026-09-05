import GarblingPrize.Submission.GLVHintOracleLaw

namespace GarblingPrize.Submission.GLVHintRowLaw

/-! Group each private coin with its two external label pads. The resulting
rows are independent uniform finite states; no unused label coordinate is
removed from the probability space. -/

open GarblingPrize.Protected
open GLVCompactScheme GLVCompactOracleLaw GLVHintScheme GLVHintOracleLaw
open HintAffineTablePrivacy HintProductLaw
open MeasureTheory ProbabilityTheory

abbrev Pads := Bool → SeedLabel
abbrev Rows := BitIndex → Purpose → RowState
noncomputable def padsLaw : Measure Pads := Measure.infinitePi fun _ : Bool => seedLabelLaw
noncomputable def rowLaw : Measure RowState := uniformOn Set.univ
noncomputable def rowsLaw : Measure Rows :=
  Measure.infinitePi fun _ : BitIndex => Measure.infinitePi fun _ : Purpose => rowLaw

instance : IsProbabilityMeasure padsLaw := by unfold padsLaw; infer_instance
instance : IsProbabilityMeasure rowLaw := by unfold rowLaw; infer_instance
instance : IsProbabilityMeasure rowsLaw := by unfold rowsLaw; infer_instance
instance (hidden : Hidden) : IsProbabilityMeasure (randomnessLaw hidden) := by
  unfold randomnessLaw
  infer_instance

def rowEquiv : Coin × Pads ≃ RowState where
  toFun := fun state => ((state.2 false, state.1), state.2 true)
  invFun := fun state => (state.1.2, fun bit => if bit then state.2 else state.1.1)
  left_inv := by
    rintro ⟨coin, pads⟩
    apply Prod.ext
    · rfl
    · funext bit
      cases bit <;> rfl
  right_inv := by rintro ⟨⟨pad, coin⟩, pad'⟩; rfl

theorem rowEquiv_law : MeasurePreserving rowEquiv (coinLaw.prod padsLaw) rowLaw := by
  unfold coinLaw padsLaw seedLabelLaw rowLaw
  rw [infinitePi_uniform_univ, prod_uniform_univ]
  exact measurePreserving_uniformOfFiniteEquiv rowEquiv

def joinRows (state : Coins × LabelPairs) : Rows :=
  fun wire purpose => ((state.2 wire false purpose, state.1 wire purpose),
    state.2 wire true purpose)

theorem joinRows_law : MeasurePreserving joinRows (coinsLaw.prod labelPairsLaw) rowsLaw := by
  let rearrange : LabelPairs → BitIndex → Purpose → Pads :=
    fun pairs wire purpose bit => pairs wire bit purpose
  have hr : MeasurePreserving rearrange labelPairsLaw
      (Measure.infinitePi fun _ : BitIndex => Measure.infinitePi fun _ : Purpose => padsLaw) :=
    infinitePi_map _ _ _ (fun _ => infinitePi_swap (fun _ : Bool => fun _ : Purpose => seedLabelLaw))
  have hj : MeasurePreserving
      (fun state : (Purpose → Coin) × (Purpose → Pads) => fun purpose =>
        rowEquiv (state.1 purpose, state.2 purpose))
      ((Measure.infinitePi fun _ : Purpose => coinLaw).prod
        (Measure.infinitePi fun _ : Purpose => padsLaw))
      (Measure.infinitePi fun _ : Purpose => rowLaw) :=
    (infinitePi_map _ _ (fun _ => rowEquiv) (fun _ => rowEquiv_law)).comp
      (infinitePi_prod (fun _ : Purpose => coinLaw) (fun _ : Purpose => padsLaw))
  have hw := (infinitePi_map _ _ _ (fun _ : BitIndex => hj)).comp
    (infinitePi_prod
      (fun _ : BitIndex => Measure.infinitePi fun _ : Purpose => coinLaw)
      (fun _ : BitIndex => Measure.infinitePi fun _ : Purpose => padsLaw))
  exact hw.comp ((MeasurePreserving.id coinsLaw).prod hr)

def rowCoins (rows : Rows) : Coins := fun wire purpose => (rows wire purpose).1.2

def rowPairs (rows : Rows) : LabelPairs :=
  fun wire bit purpose => if bit then (rows wire purpose).2 else (rows wire purpose).1.1

@[simp] theorem rowCoins_joinRows (coins : Coins) (pairs : LabelPairs) :
    rowCoins (joinRows (coins, pairs)) = coins := rfl

@[simp] theorem rowPairs_joinRows (coins : Coins) (pairs : LabelPairs) :
    rowPairs (joinRows (coins, pairs)) = pairs := by
  funext wire bit purpose
  cases bit <;> rfl

def derivedState (hidden : Hidden) (state : HiddenState) : Randomness hidden × Rows :=
  (randomnessFromOracle hidden state.internalOracle,
    joinRows (coinsFromOracle state.internalOracle, state.pairs))

theorem derivedState_law (hidden : Hidden) :
    MeasurePreserving (derivedState hidden) hiddenStateLaw
      ((randomnessLaw hidden).prod rowsLaw) := by
  have hstate : MeasurePreserving HiddenState.measurableEquiv hiddenStateLaw
      (internalOracleLaw.prod labelPairsLaw) := by
    unfold hiddenStateLaw
    exact (HiddenState.measurableEquiv.symm.measurable
      |>.measurePreserving (internalOracleLaw.prod labelPairsLaw)).symm
        HiddenState.measurableEquiv.symm
  have horacle := (oracleState_law hidden).prod (MeasurePreserving.id labelPairsLaw)
  have hassoc := measurePreserving_prodAssoc (randomnessLaw hidden) coinsLaw labelPairsLaw
  have hrows := (MeasurePreserving.id (randomnessLaw hidden)).prod joinRows_law
  exact hrows.comp (hassoc.comp (horacle.comp hstate))

end GarblingPrize.Submission.GLVHintRowLaw
