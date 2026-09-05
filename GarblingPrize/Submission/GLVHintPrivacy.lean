import GarblingPrize.Submission.GLVHintRowLaw

namespace GarblingPrize.Submission.GLVHintPrivacy

/-! Whole-view privacy follows from a skew product: the established GLV core
bijection preserves each selected affine output, and independent row
bijections preserve each serialized table and every selected label pad. -/

open GarblingPrize.Protected
open GLVCompactScheme GLVCompactOracleLaw GLVCompactPrivacy
open GLVHintScheme GLVHintOracleLaw GLVHintRowLaw HintAffineTablePrivacy
open MeasureTheory ProbabilityTheory

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

noncomputable def coordinateChange (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) (wire : BitIndex)
    (purpose : Purpose) : Equiv.Perm RowState :=
  match tableOwner purpose with
  | none => Equiv.refl _
  | some (index, kind) =>
    match tableIndex kind wire with
    | none => Equiv.refl _
    | some row => rowTransport
        ((mapHidden source rs.offsets rs.randomizers rs.chainMasks index).params kind)
        ((mapHidden target rt.offsets rt.randomizers rt.chainMasks index).params kind)
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

@[simp] theorem purpose_eq (index : Nat) (kind : GLVProjectiveMap.TableKind) :
    GLVHintProjectiveMap.purpose index kind = GLVProjectiveMap.purpose index kind := rfl

@[simp] theorem pairsFor_tableWire (pairs : LabelPairs) (kind : GLVProjectiveMap.TableKind)
    (row : HintAffineTable.RowIndex) (bit : Bool) :
    GLVHintProjectiveMap.pairsFor (xPairs pairs) (yPairs pairs) kind row bit =
      pairs (tableWire kind row) bit := by
  cases kind <;> rfl

def garbleRows (hidden : Hidden) (randomness : Randomness hidden) (rows : Rows) :
    GLVHintScheme.Artifact := GLVHintScheme.garble hidden randomness (rowCoins rows) (rowPairs rows)

theorem garbleRows_table (hidden : Hidden) (randomness : Randomness hidden)
    (rows : Rows) (index : Fin 91) (kind : GLVProjectiveMap.TableKind) :
    ((garbleRows hidden randomness rows).maps index).tables kind =
      tableFromState
        ((mapHidden hidden randomness.offsets randomness.randomizers randomness.chainMasks index).params kind)
        (fun row => rows (tableWire kind row) (GLVProjectiveMap.purpose index.val kind)) := by
  unfold garbleRows GLVHintScheme.garble GLVHintProjectiveMap.garble
  dsimp only
  rw [HintAffineTablePrivacy.garble_eq_tableFromState]
  apply congrArg (tableFromState
    ((mapHidden hidden randomness.offsets randomness.randomizers randomness.chainMasks index).params kind))
  funext row
  simp only [pairsFor_tableWire, rowPairs, Bool.false_eq_true, ↓reduceIte,
    tableCoins, rowCoins, purpose_eq]

theorem transformRows_table (input : Input) (source target : Hidden)
    (rs : Randomness source) (rt : Randomness target) (rows : Rows)
    (index : Fin 91) (kind : GLVProjectiveMap.TableKind) :
    (fun row => transformRows input source target rs rt rows
        (tableWire kind row) (GLVProjectiveMap.purpose index.val kind)) =
      tableTransport
        ((mapHidden source rs.offsets rs.randomizers rs.chainMasks index).params kind)
        ((mapHidden target rt.offsets rt.randomizers rt.chainMasks index).params kind)
        (bitsFor kind input)
        (fun row => rows (tableWire kind row) (GLVProjectiveMap.purpose index.val kind)) := by
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
  apply GLVHintFamilyArtifact.Artifact.ext
  funext index
  apply GLVHintProjectiveMap.Artifact.ext
  funext kind
  rw [garbleRows_table, garbleRows_table, transformRows_table]
  exact tableFromState_transport _ _ _
    (tableOutput_preserved input source target hequal randomness.offsets randomness.randomizers
      randomness.chainMasks index kind) _

abbrev RowPrefix := BitIndex → Fin (11 * 91) → RowState

def rowPrefix (rows : Rows) : RowPrefix := fun wire purpose => rows wire purpose.val

def expandPrefix (rows : RowPrefix) : Rows :=
  fun wire purpose => if h : purpose < 11 * 91 then rows wire ⟨purpose, h⟩
    else ((Bytes.zero 32, ⟨0, by have := HintAffineTable.modulus_positive; omega⟩), Bytes.zero 32)

theorem purpose_lt (index : Fin 91) (kind : GLVProjectiveMap.TableKind) :
    GLVProjectiveMap.purpose index.val kind < 11 * 91 := by
  have hi := index.isLt
  have hk : kind.index < 11 := by cases kind <;> decide
  unfold GLVProjectiveMap.purpose
  calc
    11 * index.val + kind.index < 11 * (index.val + 1) := by omega
    _ ≤ 11 * 91 := Nat.mul_le_mul_left 11 (by omega)

theorem garbleRows_prefix (hidden : Hidden) (randomness : Randomness hidden) (rows : Rows) :
    garbleRows hidden randomness (expandPrefix (rowPrefix rows)) =
      garbleRows hidden randomness rows := by
  apply GLVHintFamilyArtifact.Artifact.ext
  funext index
  apply GLVHintProjectiveMap.Artifact.ext
  funext kind
  rw [garbleRows_table, garbleRows_table]
  apply congrArg (tableFromState _)
  funext row
  unfold expandPrefix rowPrefix
  rw [dif_pos (purpose_lt index kind)]

theorem productArtifactBytes_measurable (hidden : Hidden) :
    Measurable (fun state : Randomness hidden × Rows =>
      GLVHintFamilyArtifact.encode (garbleRows hidden state.1 state.2)) := by
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
      GLVHintFamilyArtifact.encode (garbleRows hidden observation.1 (expandPrefix observation.2))) :=
    measurable_of_finite _
  convert hgarble.comp hobservation using 1
  funext state
  exact congrArg GLVHintFamilyArtifact.encode (garbleRows_prefix hidden state.1 state.2).symm

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
    ((GLVHintFamilyArtifact.encode (garbleRows hidden state.1 state.2),
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
  · exact congrArg (fun artifact : GLVHintScheme.Artifact => GLVHintFamilyArtifact.encode artifact)
      (garbleRows_preserved input source target hequal state.1 state.2)
  · exact transformRows_activeLabels input source target state.1
      (targetRandomness input source target hequal state.1) state.2
  · exact congrArg (fun point => Except.ok (Profile.outputEquiv.symm point)) hequal.symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem stateView_eq_productView (hidden : Hidden) (input : Input) (state : HiddenState) :
    stateView GLVHintScheme.scheme hidden state input =
      productView hidden input (GLVHintRowLaw.derivedState hidden state) := by
  obtain ⟨output, hresult, hreference⟩ :=
    GLVHintScheme.correct hidden state.internalOracle state.pairs input
  have houtput : output = Profile.outputEquiv.symm (reference Profile hidden input) := by
    apply Profile.outputEquiv.injective
    simpa using hreference
  apply PublicView.ext
  · change GLVHintFamilyArtifact.encode (GLVHintScheme.garbleWithOracle hidden state.internalOracle state.pairs) = _
    rw [GLVHintScheme.garbleWithOracle_eq]
    simp only [productView, GLVHintRowLaw.derivedState, garbleRows,
      rowCoins_joinRows, rowPairs_joinRows]
    rfl
  · change activeLabels state.pairs input =
      activeLabels (rowPairs (joinRows (coinsFromOracle state.internalOracle, state.pairs))) input
    rw [rowPairs_joinRows]
  · unfold stateView publicView productView GLVHintRowLaw.derivedState
    dsimp only
    rw [hresult, houtput]
    rfl

set_option maxRecDepth 4096 in
theorem stateView_measurable (hidden : Hidden) (input : Input) :
    Measurable (fun state : HiddenState => stateView GLVHintScheme.scheme hidden state input) := by
  rw [show (fun state : HiddenState => stateView GLVHintScheme.scheme hidden state input) =
      productView hidden input ∘ GLVHintRowLaw.derivedState hidden by
    funext state
    exact stateView_eq_productView hidden input state]
  exact (productView_measurable hidden input).comp (derivedState_law hidden).measurable

set_option maxRecDepth 4096 in
theorem publicView_identDistrib (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    IdentDistrib
      (fun state => stateView GLVHintScheme.scheme source state input)
      (fun state => stateView GLVHintScheme.scheme target state input)
      hiddenStateLaw hiddenStateLaw := by
  refine ⟨(stateView_measurable source input).aemeasurable,
    (stateView_measurable target input).aemeasurable, ?_⟩
  rw [show (fun state : HiddenState => stateView GLVHintScheme.scheme source state input) =
      productView source input ∘ GLVHintRowLaw.derivedState source by
    funext state
    exact stateView_eq_productView source input state]
  rw [show (fun state : HiddenState => stateView GLVHintScheme.scheme target state input) =
      productView target input ∘ GLVHintRowLaw.derivedState target by
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

theorem functionPrivate : FunctionPrivate GLVHintScheme.scheme where
  stateView_measurable := stateView_measurable
  publicView_identDistrib := publicView_identDistrib

theorem valid : ValidCandidate GLVHintScheme.scheme GLVHintScheme.claimedBytes where
  correct := GLVHintScheme.correct
  function_private := functionPrivate
  codec := GLVHintScheme.codec
  artifact_bound := GLVHintScheme.artifactBoundOracle

end GarblingPrize.Submission.GLVHintPrivacy
