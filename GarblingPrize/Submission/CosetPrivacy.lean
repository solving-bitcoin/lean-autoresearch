import GarblingPrize.Submission.CosetRowLaw
import GarblingPrize.Submission.CosetCorePrivacy

namespace GarblingPrize.Submission.CosetPrivacy

/-! Whole-view privacy follows from a skew product: the established GLV core
bijection preserves each selected affine output, and independent row
bijections preserve each serialized table and every selected label pad. -/

open GarblingPrize.Protected
open GLVCompactScheme (Hidden Input Profile xPairs yPairs xBits yBits)
open CosetRandomness (randomnessLaw)
open CosetCorePrivacy
open GLVHintRowLaw (Rows rowsLaw rowPairs rowCoins joinRows rowCoins_joinRows rowPairs_joinRows)
open CosetScheme CosetOracleLaw CosetRowLaw HintAffineTablePrivacy
open MeasureTheory ProbabilityTheory

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def tableOwner (purpose : Purpose) : Option (Fin 91 × CosetHintMap.TableKind) :=
  if h : purpose < 8 * 91 then
    some (⟨purpose / 8, (Nat.div_lt_iff_lt_mul (by decide)).mpr
      (by simpa [Nat.mul_comm] using h)⟩,
      ⟨purpose % 8, Nat.mod_lt _ (by decide)⟩)
  else none

@[simp] theorem tableOwner_purpose (index : Fin 91) (kind : CosetHintMap.TableKind) :
    tableOwner (CosetHintMap.purpose index.val kind) = some (index, kind) := by
  have hi := index.isLt
  have hk := kind.isLt
  unfold tableOwner CosetHintMap.purpose
  rw [dif_pos (by change 8 * index.val + kind.val < 728; omega)]
  apply congrArg some
  apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

noncomputable def coordinateChange (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) (wire : BitIndex)
    (purpose : Purpose) : Equiv.Perm RowState :=
  match tableOwner purpose with
  | none => Equiv.refl _
  | some (index, kind) =>
    match tableIndex kind wire with
    | none => Equiv.refl _
    | some row => rowTransport
        (mapParams source rs index kind)
        (mapParams target rt index kind)
        row (inputBit input wire)

noncomputable def transformRows (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) (rows : Rows) : Rows :=
  fun wire purpose => coordinateChange input source target rs rt wire purpose (rows wire purpose)

theorem transformRows_law (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) :
    MeasurePreserving (transformRows input source target rs rt) rowsLaw rowsLaw :=
  HintProductLaw.infinitePi_map _ _ _ (fun wire =>
    HintProductLaw.infinitePi_map _ _ _ (fun purpose =>
      measurePreserving_uniformOfFiniteEquiv
        (coordinateChange input source target rs rt wire purpose)))

theorem rowMap_joint_measurable {A : Type*} [MeasurableSpace A]
    [DiscreteMeasurableSpace A] [Finite A]
    (f : A → BitIndex → Purpose → RowState → RowState) :
    Measurable (fun state : A × Rows => fun wire purpose =>
      f state.1 wire purpose (state.2 wire purpose)) := by
  apply measurable_pi_lambda
  intro wire
  apply measurable_pi_lambda
  intro purpose
  have hf : Measurable (fun state : A × RowState => f state.1 wire purpose state.2) :=
    Measurable.of_discrete
  have hv : Measurable (fun state : A × Rows => (state.1, state.2 wire purpose)) :=
    measurable_fst.prodMk (by fun_prop)
  exact hf.comp hv

theorem transformRows_joint_measurable (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    Measurable (fun state : Randomness source × Rows =>
      transformRows input source target state.1
        (targetRandomness input source target hequal state.1) state.2) := by
  exact rowMap_joint_measurable (fun randomness wire purpose state =>
    coordinateChange input source target randomness
      (targetRandomness input source target hequal randomness) wire purpose state)

noncomputable def productChange (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (state : Randomness source × Rows) : Randomness target × Rows :=
  (targetRandomness input source target hequal state.1,
    transformRows input source target state.1
      (targetRandomness input source target hequal state.1) state.2)

theorem productChange_law (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    MeasurePreserving (productChange input source target hequal)
      ((randomnessLaw source).prod rowsLaw) ((randomnessLaw target).prod rowsLaw) := by
  exact MeasurePreserving.skew_product
    (randomnessEquiv_measurePreserving input source target hequal)
    (g := fun randomness rows => transformRows input source target randomness
      (targetRandomness input source target hequal randomness) rows)
    (transformRows_joint_measurable input source target hequal)
    (Filter.Eventually.of_forall fun randomness =>
      (transformRows_law input source target randomness
        (targetRandomness input source target hequal randomness)).map_eq)

theorem coordinateChange_selected (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) (wire : BitIndex)
    (purpose : Purpose) (state : RowState) :
    selectedPad (inputBit input wire)
        (coordinateChange input source target rs rt wire purpose state) =
      selectedPad (inputBit input wire) state := by
  unfold coordinateChange
  split
  · rfl
  · split
    · rfl
    · exact rowTransport_selectedPad _ _ _ _ _

theorem transformRows_activeLabels (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) (rows : Rows) :
    activeLabels (rowPairs (transformRows input source target rs rt rows)) input =
      activeLabels (rowPairs rows) input := by
  funext wire purpose
  exact coordinateChange_selected input source target rs rt wire purpose (rows wire purpose)

@[simp] theorem pairsFor_tableWire (pairs : LabelPairs) (kind : CosetHintMap.TableKind)
    (row : HintAffineTable.RowIndex) (bit : Bool) :
    CosetHintMap.inputFor kind (xPairs pairs) (yPairs pairs) row bit =
      pairs (tableWire kind row) bit := by
  fin_cases kind <;> rfl

def garbleRows (hidden : Hidden) (randomness : Randomness hidden) (rows : Rows) :
    CosetScheme.Artifact := CosetScheme.garble hidden randomness (rowCoins rows) (rowPairs rows)

theorem garbleRows_table (hidden : Hidden) (randomness : Randomness hidden)
    (rows : Rows) (index : Fin 91) (kind : CosetHintMap.TableKind) :
    ((garbleRows hidden randomness rows).maps index).tables kind =
      tableFromState
        (mapParams hidden randomness index kind)
        (fun row => rows (tableWire kind row) (CosetHintMap.purpose index.val kind)) := by
  unfold garbleRows CosetScheme.garble CosetHintMap.garble
  dsimp only
  rw [HintAffineTablePrivacy.garble_eq_tableFromState]
  apply congrArg (tableFromState
    (mapParams hidden randomness index kind))
  funext row
  simp only [pairsFor_tableWire, rowPairs, Bool.false_eq_true, ↓reduceIte,
    tableCoins, rowCoins]

theorem transformRows_table (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) (rows : Rows)
    (index : Fin 91) (kind : CosetHintMap.TableKind) :
    (fun row => transformRows input source target rs rt rows
        (tableWire kind row) (CosetHintMap.purpose index.val kind)) =
      tableTransport
        (mapParams source rs index kind)
        (mapParams target rt index kind)
        (bitsFor kind input)
        (fun row => rows (tableWire kind row) (CosetHintMap.purpose index.val kind)) := by
  funext row
  simp only [transformRows, coordinateChange, tableOwner_purpose, tableIndex_tableWire,
    inputBit_tableWire]
  rfl

theorem garbleRows_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (rows : Rows) :
    garbleRows target (targetRandomness input source target hequal randomness)
        (transformRows input source target randomness
          (targetRandomness input source target hequal randomness) rows) =
      garbleRows source randomness rows := by
  apply CosetFamilyArtifact.Artifact.ext
  funext index
  apply CosetHintMap.Artifact.ext
  funext kind
  rw [garbleRows_table, garbleRows_table, transformRows_table]
  exact tableFromState_transport _ _ _
    (params_preserved input source target hequal randomness index kind) _

abbrev RowPrefix := BitIndex → Fin (8 * 91) → RowState

def rowPrefix (rows : Rows) : RowPrefix := fun wire purpose => rows wire purpose.val

def expandPrefix (rows : RowPrefix) : Rows :=
  fun wire purpose => if h : purpose < 8 * 91 then rows wire ⟨purpose, h⟩
    else ((Bytes.zero 32, ⟨0, by have := HintAffineTable.modulus_positive; omega⟩), Bytes.zero 32)

theorem purpose_lt (index : Fin 91) (kind : CosetHintMap.TableKind) :
    CosetHintMap.purpose index.val kind < 8 * 91 := by
  have hi := index.isLt
  have hk := kind.isLt
  unfold CosetHintMap.purpose
  change 8 * index.val + kind.val < 728
  omega

theorem garbleRows_prefix (hidden : Hidden) (randomness : Randomness hidden) (rows : Rows) :
    garbleRows hidden randomness (expandPrefix (rowPrefix rows)) =
      garbleRows hidden randomness rows := by
  apply CosetFamilyArtifact.Artifact.ext
  funext index
  apply CosetHintMap.Artifact.ext
  funext kind
  rw [garbleRows_table, garbleRows_table]
  apply congrArg (tableFromState _)
  funext row
  unfold expandPrefix rowPrefix
  rw [dif_pos (purpose_lt index kind)]

theorem productArtifactBytes_measurable (hidden : Hidden) :
    Measurable (fun state : Randomness hidden × Rows =>
      CosetFamilyArtifact.encode (garbleRows hidden state.1 state.2)) := by
  have hobservation : Measurable (fun state : Randomness hidden × Rows =>
      (state.1, rowPrefix state.2)) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro wire
    apply measurable_pi_lambda
    intro purpose
    exact measurable_pi_apply purpose.val |>.comp
      ((measurable_pi_apply wire).comp measurable_snd)
  have hgarble : Measurable (fun observation : Randomness hidden × RowPrefix =>
      CosetFamilyArtifact.encode (garbleRows hidden observation.1 (expandPrefix observation.2))) :=
    measurable_of_finite _
  convert hgarble.comp hobservation using 1
  funext state
  exact congrArg CosetFamilyArtifact.encode (garbleRows_prefix hidden state.1 state.2).symm

theorem rowPairs_measurable : Measurable rowPairs := by
  apply measurable_pi_lambda
  intro wire
  apply measurable_pi_lambda
  intro bit
  apply measurable_pi_lambda
  intro purpose
  cases bit <;> simp only [rowPairs, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

noncomputable def productView (hidden : Hidden) (input : Input)
    (state : Randomness hidden × Rows) : PublicView Profile :=
  (PublicView.measurableEquiv Profile).symm
    ((CosetFamilyArtifact.encode (garbleRows hidden state.1 state.2),
      activeLabels (rowPairs state.2) input),
      .ok (Profile.outputEquiv.symm (reference Profile hidden input)))

theorem productView_measurable (hidden : Hidden) (input : Input) :
    Measurable (productView hidden input) := by
  have hartifact := productArtifactBytes_measurable hidden
  have hlabels : Measurable (fun state : Randomness hidden × Rows =>
      activeLabels (rowPairs state.2) input) :=
    (activeLabels_measurable input).comp (rowPairs_measurable.comp measurable_snd)
  exact (PublicView.measurableEquiv Profile).symm.measurable.comp
    ((hartifact.prodMk hlabels).prodMk measurable_const)

theorem productView_productChange (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (state : Randomness source × Rows) :
    productView target input (productChange input source target hequal state) =
      productView source input state := by
  apply PublicView.ext
  · exact congrArg (fun artifact : CosetScheme.Artifact => CosetFamilyArtifact.encode artifact)
      (garbleRows_preserved input source target hequal state.1 state.2)
  · exact transformRows_activeLabels input source target state.1
      (targetRandomness input source target hequal state.1) state.2
  · exact congrArg (fun point => Except.ok (Profile.outputEquiv.symm point)) hequal.symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem stateView_eq_productView (hidden : Hidden) (input : Input) (state : HiddenState) :
    stateView CosetScheme.scheme hidden state input =
      productView hidden input (CosetRowLaw.derivedState hidden state) := by
  obtain ⟨output, hresult, hreference⟩ :=
    CosetScheme.correct hidden state.internalOracle state.pairs input
  have houtput : output = Profile.outputEquiv.symm (reference Profile hidden input) := by
    apply Profile.outputEquiv.injective
    simpa using hreference
  apply PublicView.ext
  · change CosetFamilyArtifact.encode (CosetScheme.garbleWithOracle hidden state.internalOracle state.pairs) = _
    rw [CosetScheme.garbleWithOracle_eq]
    simp only [productView, CosetRowLaw.derivedState, garbleRows,
      rowCoins_joinRows, rowPairs_joinRows]
    rfl
  · change activeLabels state.pairs input =
      activeLabels (rowPairs (joinRows (coinsFromOracle state.internalOracle, state.pairs))) input
    rw [rowPairs_joinRows]
  · unfold stateView publicView productView CosetRowLaw.derivedState
    dsimp only
    rw [hresult, houtput]
    rfl

set_option maxRecDepth 4096 in
theorem stateView_measurable (hidden : Hidden) (input : Input) :
    Measurable (fun state : HiddenState => stateView CosetScheme.scheme hidden state input) := by
  rw [show (fun state : HiddenState => stateView CosetScheme.scheme hidden state input) =
      productView hidden input ∘ CosetRowLaw.derivedState hidden by
    funext state
    exact stateView_eq_productView hidden input state]
  exact (productView_measurable hidden input).comp (derivedState_law hidden).measurable

set_option maxRecDepth 4096 in
theorem publicView_identDistrib (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    IdentDistrib
      (fun state => stateView CosetScheme.scheme source state input)
      (fun state => stateView CosetScheme.scheme target state input)
      hiddenStateLaw hiddenStateLaw := by
  refine ⟨(stateView_measurable source input).aemeasurable,
    (stateView_measurable target input).aemeasurable, ?_⟩
  rw [show (fun state : HiddenState => stateView CosetScheme.scheme source state input) =
      productView source input ∘ CosetRowLaw.derivedState source by
    funext state
    exact stateView_eq_productView source input state]
  rw [show (fun state : HiddenState => stateView CosetScheme.scheme target state input) =
      productView target input ∘ CosetRowLaw.derivedState target by
    funext state
    exact stateView_eq_productView target input state]
  rw [← Measure.map_map (productView_measurable source input) (derivedState_law source).measurable,
    ← Measure.map_map (productView_measurable target input) (derivedState_law target).measurable,
    (derivedState_law source).map_eq, (derivedState_law target).map_eq]
  rw [show productView source input =
      productView target input ∘ productChange input source target hequal by
    funext state
    exact (productView_productChange input source target hequal state).symm]
  rw [← Measure.map_map (productView_measurable target input)
    (productChange_law input source target hequal).measurable,
    (productChange_law input source target hequal).map_eq]

theorem functionPrivate : FunctionPrivate CosetScheme.scheme where
  stateView_measurable := stateView_measurable
  publicView_identDistrib := publicView_identDistrib

theorem valid : ValidCandidate CosetScheme.scheme CosetScheme.claimedBytes where
  correct := CosetScheme.correct
  function_private := functionPrivate
  codec := CosetScheme.codec
  artifact_bound := CosetScheme.artifactBoundOracle

end GarblingPrize.Submission.CosetPrivacy
