import WotsLamport.Submission.LaneHorner
import WotsLamport.Submission.CachedSharing

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

theorem laneCoefficients_project (coins : ByteArray) (label : Label) (wire : Nat)
    (value : Bool) (limb : Fin 16) :
    (laneCoefficients coins label wire value).map (fun row => row.get limb) =
      machineCoefficients (machinePolynomial coins label wire limb.val value) := by
  simp only [laneCoefficients, machineCoefficients, machinePolynomial,
    List.map_map, ← List.map_reverse, Function.comp_def, HornerLanes.get_ofFn]

theorem laneEvaluate_project (coins : ByteArray) (label : Label) (wire : Nat)
    (value : Bool) (limb : Fin 16) (x : Nat) :
    ((laneEvaluate (laneCoefficients coins label wire value) x).get limb).toNat =
      evaluateMachinePolynomial
        (machineCoefficients (machinePolynomial coins label wire limb.val value)) x := by
  unfold laneEvaluate
  rw [lanesHorner_correspondence, laneCoefficients_project]
  have hz : (⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩ : HornerLanes).get limb = 0 := by
    rcases limb with ⟨limb,hl⟩
    interval_cases limb <;> rfl
  rw [hz]
  rfl

theorem laneShare_eq (coins : ByteArray) (label : Label) (wire : Nat)
    (value : Bool) (x : Nat) :
    laneShare (laneCoefficients coins label wire value) x =
      concatenate (((List.range 16).map fun limb =>
        machineCoefficients (machinePolynomial coins label wire limb value)).map fun p =>
          writeLE 3 (evaluateMachinePolynomial p x)) := by
  unfold laneShare
  rw [List.map_map]
  apply congrArg concatenate
  apply List.map_congr_left
  intro limb hl
  have bound := List.mem_range.mp hl
  rw [laneEvaluate_project]
  simp only [Nat.mod_eq_of_lt bound, Function.comp_def]

theorem laneLabelTable_eq (h : Hash) (coins pk nonce : ByteArray) (cache : PreparedChainCache)
    (i : Fin 256) (value : Bool) (label : Label) :
    laneLabelTable h coins pk nonce cache i value label =
      cachedLabelTable h coins pk nonce cache i value label := by
  simp only [laneLabelTable, cachedLabelTable, laneShare_eq]


theorem lanePrepare_eq (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : lanePrepare h coins keys labels = prepare h coins keys labels := by
  rw [← cachedPrepare_eq]
  simp only [lanePrepare, cachedPrepare, laneLabelTable_eq]

theorem laneConstruction_eq : laneConstruction = construction := by
  have hp : lanePrepare = prepare := by funext h coins keys labels; exact lanePrepare_eq h coins keys labels
  unfold laneConstruction construction
  rw [hp]


end WotsLamport.Submission
