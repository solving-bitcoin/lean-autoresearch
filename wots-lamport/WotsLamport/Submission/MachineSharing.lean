import WotsLamport.Submission.MachineHorner
import WotsLamport.Submission.Layout

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Proposed faster table generation. The candidate and diagnostic still use
`labelTable` until this module's correspondence proofs have been checked. -/
def machineLabelTable (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) : ByteArray :=
  let polys := (List.range 16).map fun limb =>
    machineCoefficients (polynomial coins label i.val limb value)
  concatenate ((slots i value).zipIdx.map fun ((j,k), index) =>
    let point := index+1
    let share := concatenate (polys.map fun p => writeLE 3 (evaluateMachinePolynomial p point))
    xorBytes share (mask h pk nonce i.val value point (chain h k (keys j))))

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
  simp only [List.map_map, Function.comp_def, evaluateMachinePolynomial_eq _ _ hp]

def machinePrepare (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : ByteArray :=
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  nonce ++ concatenate ((List.finRange 256).map fun i =>
    (ByteArray.mk (commitment h pk nonce i.val false ((labels i).get false)).toArray) ++
    (ByteArray.mk (commitment h pk nonce i.val true ((labels i).get true)).toArray)) ++
  concatenate ((List.finRange 256).map fun i =>
    machineLabelTable h coins pk nonce keys i false ((labels i).get false) ++
    machineLabelTable h coins pk nonce keys i true ((labels i).get true))

theorem machinePrepare_eq (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : machinePrepare h coins keys labels = prepare h coins keys labels := by
  simp only [machinePrepare, prepare, machineLabelTable_eq]

def machineConstruction : Construction := ⟨randomnessBytes, machinePrepare, expand⟩

/-- Equality of the entire construction, for every hash and every setup
input. This theorem cannot certify the original construction's security. -/
theorem machineConstruction_eq : machineConstruction = construction := by
  have hp : machinePrepare = prepare := by funext h coins keys labels; exact machinePrepare_eq h coins keys labels
  unfold machineConstruction construction
  rw [hp]

end WotsLamport.Submission
