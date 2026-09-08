import G1Release.Submission.LamportLaw
import G1Release.Submission.CosetQueryGuessing

set_option maxRecDepth 4096
set_option maxHeartbeats 100000

namespace G1Release.Submission.CosetKeyInverse
open SecretRelease G1Release.Protected LamportLaw CosetSlots CosetRealIdeal CosetQueryGuessing

theorem pair_inverse_active (b : Bool) (active : Label) (rank : Rank) :
    ((pairEquiv b).symm (active,rank)).get b = active := by cases b <;> rfl

theorem pair_inverse_opposite (b : Bool) (active : Label) (rank : Rank) :
    ((pairEquiv b).symm (active,rank)).get (!b) =
      ((complementEquiv active).symm rank).val := by cases b <;> rfl

noncomputable def keys (input : Input) (active : Fin 512 → Label) (ranks : Fin 512 → Rank) :
    Fin 512 → Pair := (keysEquiv (inputBits input)).symm (active,ranks)

theorem selected_keys (input : Input) (active : Fin 512 → Label) (ranks : Fin 512 → Rank) :
    selected (keys input active ranks) input = active := by
  funext i
  simp only [selected, keys, keysEquiv, Equiv.coe_fn_symm_mk]
  exact pair_inverse_active (inputBits input i) (active i) (ranks i)

theorem opposite_keys (input : Input) (active : Fin 512 → Label) (ranks : Fin 512 → Rank)
    (i : Fin 512) :
    (oppositeKeys (keys input active ranks) input i).val =
      (hiddenFromRanks active ranks i).val := by
  simp only [oppositeKeys, keys, keysEquiv, hiddenFromRanks, Equiv.coe_fn_symm_mk]
  exact pair_inverse_opposite (inputBits input i) (active i) (ranks i)

end G1Release.Submission.CosetKeyInverse
