import WotsLamport.Submission.MachineCoinRead
import WotsLamport.Submission.Layout

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Faster table generation has exactly the reference table bytes.
The selected cached implementation uses this checked correspondence. -/
theorem machineLabelTable_eq (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) :
    machineLabelTable h coins pk nonce keys i value label =
      labelTable h coins pk nonce keys i value label := by
  unfold machineLabelTable labelTable
  apply congrArg concatenate
  apply List.map_congr_left
  rintro ⟨⟨j,k⟩,index⟩ he
  have hi := (List.mem_zipIdx' he).1
  have hl : (slots i value).length ≤ 1984 := by
    rw [slots_length]
    cases value <;> decide
  have hp : index+1 ≤ 1984 := by omega
  simp only [List.map_map, Function.comp_def, machinePolynomial_eq,
    evaluateMachinePolynomial_eq _ _ hp]

theorem machinePrepare_eq (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : machinePrepare h coins keys labels = prepare h coins keys labels := by
  simp only [machinePrepare, prepare, machineLabelTable_eq]

/-- Equality of the entire construction, for every hash and every setup
input. This theorem cannot certify the original construction's security. -/
theorem machineConstruction_eq : machineConstruction = construction := by
  have hp : machinePrepare = prepare := by funext h coins keys labels; exact machinePrepare_eq h coins keys labels
  unfold machineConstruction construction
  rw [hp]

end WotsLamport.Submission
