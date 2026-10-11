import WotsLamport.Submission.CachedImplementation
import WotsLamport.Submission.MachineSharing

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Materialize the short chain prefixes once per setup. This proposed
optimization still calls the supplied hash; it does not substitute a backend. -/
theorem cachedChainNode_eq (h : Hash) (keys : Keys) (j : Fin 67) (k : Nat)
    (hk : k < 16) : cachedChainNode (prepareChainCache h keys) j k = chain h k (keys j) := by
  unfold cachedChainNode prepareChainCache
  rw [Vector.getElem_ofFn]
  rw [getElem!_pos (Vector.ofFn (fun depth : Fin 16 => chain h depth.val (keys j))) k hk]
  rw [Vector.getElem_ofFn]

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

theorem cachedPrepare_eq (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : cachedPrepare h coins keys labels = prepare h coins keys labels := by
  change cachedPrepare h coins keys labels = _
  rw [← machinePrepare_eq]
  simp only [cachedPrepare, machinePrepare, cachedLabelTable_eq]

/-- Full extensional equality, including every prepared artifact byte.
This candidate remains unused pending compilation and performance evidence. -/
theorem cachedConstruction_eq : cachedConstruction = construction := by
  have hp : cachedPrepare = prepare := by funext h coins keys labels; exact cachedPrepare_eq h coins keys labels
  unfold cachedConstruction construction
  rw [hp]

end WotsLamport.Submission
