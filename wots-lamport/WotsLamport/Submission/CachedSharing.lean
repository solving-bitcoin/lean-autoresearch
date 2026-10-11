import WotsLamport.Submission.MachineSharing

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

abbrev PreparedChainCache := Vector (Vector Label 16) 67

/-- Materialize the short chain prefixes once per setup. This proposed
optimization still calls the supplied hash; it does not substitute a backend. -/
def prepareChainCache (h : Hash) (keys : Keys) : PreparedChainCache :=
  Vector.ofFn fun j => Vector.ofFn fun k => chain h k.val (keys j)

def cachedChainNode (cache : PreparedChainCache) (j : Fin 67) (k : Nat) : Label :=
  cache[j.val][k]!

theorem cachedChainNode_eq (h : Hash) (keys : Keys) (j : Fin 67) (k : Nat)
    (hk : k < 16) : cachedChainNode (prepareChainCache h keys) j k = chain h k (keys j) := by
  simp only [cachedChainNode, getElem!_pos _ _ hk, prepareChainCache, Vector.getElem_ofFn]

theorem cached_slot_node_bound (i : Fin 256) (value : Bool) (entry : Fin 67 × Nat)
    (member : entry ∈ slots i value) : entry.2 < 16 := by
  unfold slots at member
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp member
  obtain ⟨k, hk, hentry⟩ := List.mem_flatMap.mp hj
  have he := List.eq_of_mem_replicate hentry
  have hk' := List.mem_range.mp hk
  have hm : maximum j ≤ 15 := by unfold maximum; split <;> omega
  rw [he]
  exact lt_of_lt_of_le hk' (by omega)

def cachedLabelTable (h : Hash) (coins pk nonce : ByteArray) (cache : PreparedChainCache)
    (i : Fin 256) (value : Bool) (label : Label) : ByteArray :=
  let polys := (List.range 16).map fun limb =>
    machineCoefficients (machinePolynomial coins label i.val limb value)
  concatenate ((slots i value).zipIdx.map fun ((j,k), index) =>
    let point := index+1
    let share := concatenate (polys.map fun p => writeLE 3 (evaluateMachinePolynomial p point))
    xorBytes share (mask h pk nonce i.val value point (cachedChainNode cache j k)))

theorem cachedLabelTable_eq (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) :
    cachedLabelTable h coins pk nonce (prepareChainCache h keys) i value label =
      machineLabelTable h coins pk nonce keys i value label := by
  unfold cachedLabelTable machineLabelTable
  apply congrArg concatenate
  apply List.map_congr_left
  rintro ⟨⟨j,k⟩,index⟩ he
  have hk := cached_slot_node_bound i value (j,k) (List.fst_mem_of_mem_zipIdx he)
  simp only [cachedChainNode_eq h keys j k hk]

def cachedPrepare (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : ByteArray :=
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  let cache := prepareChainCache h keys
  nonce ++ concatenate ((List.finRange 256).map fun i =>
    (ByteArray.mk (commitment h pk nonce i.val false ((labels i).get false)).toArray) ++
    (ByteArray.mk (commitment h pk nonce i.val true ((labels i).get true)).toArray)) ++
  concatenate ((List.finRange 256).map fun i =>
    cachedLabelTable h coins pk nonce cache i false ((labels i).get false) ++
    cachedLabelTable h coins pk nonce cache i true ((labels i).get true))

theorem cachedPrepare_eq (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : cachedPrepare h coins keys labels = prepare h coins keys labels := by
  change cachedPrepare h coins keys labels = _
  rw [← machinePrepare_eq]
  simp only [cachedPrepare, machinePrepare, cachedLabelTable_eq]

def cachedConstruction : Construction := ⟨randomnessBytes, cachedPrepare, expand⟩

/-- Full extensional equality, including every prepared artifact byte.
This candidate remains unused pending compilation and performance evidence. -/
theorem cachedConstruction_eq : cachedConstruction = construction := by
  have hp : cachedPrepare = prepare := by funext h coins keys labels; exact cachedPrepare_eq h coins keys labels
  unfold cachedConstruction construction
  rw [hp]

end WotsLamport.Submission
