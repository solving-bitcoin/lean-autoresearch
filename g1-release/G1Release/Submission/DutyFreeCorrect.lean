import G1Release.Submission.DutyFreeProgram

namespace G1Release.Submission.DutyFreeProgram
open SecretRelease G1Release.Protected GarblingPrize.Protected
open DutyFreeLayout GLVDigits CosetCoordinates FourAffineQuotient
open Scheme (runtimeOfGroup toPoint_runtimeOfGroup inputG1)
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem activeHot_correct (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) (side : Side) (chunk : Chunk) (cell : Cell)
    (h : cell ≠ inputCell input side chunk) :
    activeHot hash (garble hash hidden random keys hot) input
      (challenge.inputs.reveal hash keys input) (bridgeId side chunk) cell =
        hot (bridgeId side chunk) cell := by
  simp only [activeHot, activeHotStorage, Vector.get_ofFn, bridgeSide_id, bridgeChunk_id, if_neg h]
  rw [garble_bridge]
  simp only [garbleBridge, bridgeSide_id, bridgeChunk_id, unpack_pack_bridge]
  have hl : (fun bit => Scheme.readLabel (challenge.inputs.reveal hash keys input)
      (wire side chunk bit)) =
      (fun bit => bridgeKeys keys side chunk bit (DutyFreeBridge.bit (inputCell input side chunk) bit)) := by
    funext bit
    rw [Scheme.reveal_labels, ← bit_wire]
    rfl
  rw [hl]
  exact DutyFreeBridge.reveal_correct _ _ _ _ _ h

theorem evaluateTable_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) (table : Table) :
    evaluateTable hash (garble hash hidden random keys hot) input
      (activeHot hash (garble hash hidden random keys hot) input
        (challenge.inputs.reveal hash keys input)) table =
      some ((CosetScheme.mapParams hidden random (mapOf table) (kindOf table)).coefficient *
        ((coordinate input (sideFor table)).val : Word) +
        (CosetScheme.mapParams hidden random (mapOf table) (kindOf table)).constant) := by
  rw [evaluateTable_eq, garble_table]
  unfold garbleTable
  have hc : (((coordinate input (sideFor table)).val : Word)).val =
      (coordinate input (sideFor table)).val :=
    ZMod.val_cast_of_lt (coordinate input (sideFor table)).isLt
  have h := DutyFreeTables.correct (masks hash hot table)
    (available hash input (activeHot hash (garble hash hidden random keys hot) input
      (challenge.inputs.reveal hash keys input)) table)
    (CosetScheme.mapParams hidden random (mapOf table) (kindOf table)).coefficient
    (CosetScheme.mapParams hidden random (mapOf table) (kindOf table)).constant
    (((coordinate input (sideFor table)).val : Word))
  rw [hc] at h
  apply h
  intro chunk cell hcell
  change cell ≠ inputCell input (sideFor table) chunk at hcell
  simp only [available, if_neg hcell, masks]
  rw [activeHot_correct hash hidden random keys hot input _ _ _ hcell]

theorem evaluateTable_opened (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) (map : Fin 91) (kind : Fin 8) :
    evaluateTable hash (garble hash hidden random keys hot) input
      (activeHot hash (garble hash hidden random keys hot) input
        (challenge.inputs.reveal hash keys input)) (tableId map kind) =
      some (CosetHintMap.openedWords
        (opened (CosetScheme.mapBase hidden random map) (random.states map)
          (C (input.val.1.val : Word)) (C (input.val.2.val : Word))) kind) := by
  rw [evaluateTable_garble, mapOf_tableId, kindOf_tableId, field_coordinate]
  unfold CosetScheme.mapParams
  rw [CosetHintMap.params_opened]

theorem openings_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) (map : Fin 91) :
    openings hash (garble hash hidden random keys hot) input
      (activeHot hash (garble hash hidden random keys hot) input
        (challenge.inputs.reveal hash keys input)) map =
      some (opened (CosetScheme.mapBase hidden random map) (random.states map)
        (C (input.val.1.val : Word)) (C (input.val.2.val : Word))) := by
  simp only [openings, evaluateTable_opened, CosetHintMap.openedWords]
  rfl

theorem evaluateMap_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) (map : Fin 91) :
    evaluateMap hash (garble hash hidden random keys hot) input
      (activeHot hash (garble hash hidden random keys hot) input
        (challenge.inputs.reveal hash keys input)) map =
      some (runtimeOfGroup (EisensteinFullWidth.mapOutput (offsetAt random.offsets map)
        (digitAt hidden map) (-inputG1 input))) := by
  rw [evaluateMap, openings_garble]
  exact CosetGLV.decode_openings _ _ input (random.states map)

theorem evaluateMaps_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) (maps : List (Fin 91)) :
    evaluateMaps hash (garble hash hidden random keys hot) input
      (activeHot hash (garble hash hidden random keys hot) input
        (challenge.inputs.reveal hash keys input)) maps =
      some (maps.map fun map => runtimeOfGroup (EisensteinFullWidth.mapOutput
        (offsetAt random.offsets map) (digitAt hidden map) (-inputG1 input))) := by
  induction maps with
  | nil => rfl
  | cons map maps ih => rw [evaluateMaps, evaluateMap_garble, ih]; rfl

theorem evaluate_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) :
    evaluate hash (garble hash hidden random keys hot) input (challenge.inputs.reveal hash keys input) =
      some (encodeOutput (reference hidden input)) := by
  let points := (List.finRange 91).map fun map => runtimeOfGroup
    (EisensteinFullWidth.mapOutput (offsetAt random.offsets map) (digitAt hidden map) (-inputG1 input))
  obtain ⟨result, hresult, hvalue⟩ := RuntimeG1.recomposeAlpha_correct points
  unfold evaluate
  rw [Scheme.reveal_size]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  erw [evaluateMaps_garble]
  change (match RuntimeG1.recomposeAlpha points with
    | .error _ => none
    | .ok result => some (encodeOutput (RuntimeG1.toOutput result))) = _
  rw [hresult]
  apply congrArg some
  apply congrArg encodeOutput
  change RuntimeG1.toOutput result = BN254.CanonicalOutput.ofPoint
    (hidden.1.toPoint + hidden.2.val • inputG1 input)
  unfold RuntimeG1.toOutput
  apply congrArg BN254.CanonicalOutput.ofPoint
  rw [hvalue]
  have hp : points.map RuntimeG1.toPoint = (List.finRange 91).map fun map =>
      EisensteinFullWidth.mapOutput (offsetAt random.offsets map) (digitAt hidden map) (-inputG1 input) := by
    simp only [points, List.map_map, Function.comp_def, toPoint_runtimeOfGroup]
  rw [hp, CosetScheme.honest_recompose]

end G1Release.Submission.DutyFreeProgram
