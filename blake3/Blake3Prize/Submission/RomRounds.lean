import Blake3Prize.Submission.RomMix
import Blake3Prize.Submission.RomPermutation

set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace Blake3Prize.Submission.RomRounds
open RomOperations RomPermutation HalfGates

abbrev Indices := Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16

def tupleOp (indices : Indices) : Operation :=
  let (a,b,c,d,i,j) := indices
  RomMix.mix (low a) (low b) (low c) (low d) (high i) (high j)

def tupleRun (message : Vector (BitVec 32) 16) (state : Vector (BitVec 32) 16)
    (indices : Indices) : Vector (BitVec 32) 16 :=
  let (a,b,c,d,i,j) := indices
  WordProgram.mix RomWordSemantics.ops state a b c d (message.get i) (message.get j)

def Valid (indices : Indices) : Prop :=
  let (a,b,c,d,i,j) := indices
  [a.val,b.val,c.val,d.val,16+i.val,16+j.val].Nodup

theorem mixed_append (v m : Vector (BitVec 32) 16) (a b c d : Fin 16) (x y : BitVec 32) :
    RomMix.mixed (v ++ m) (low a) (low b) (low c) (low d) x y =
      WordProgram.mix RomWordSemantics.ops v a b c d x y ++ m := by
  have get (i : Fin 16) : (v ++ m).get (low i) = v.get i :=
    RomVector.append_get_left v m i
  simp only [RomMix.mixed,get a,get b,get c,get d]
  simp only [low]
  rw [Vector.set_append_left a.isLt,Vector.set_append_left b.isLt,
    Vector.set_append_left c.isLt,Vector.set_append_left d.isLt]
  rfl

theorem run_tuple (indices : Indices) (hv : Valid indices) (v m : Vector (BitVec 32) 16) :
    (tupleOp indices).run (v ++ m) = tupleRun m v indices ++ m := by
  rcases indices with ⟨a,b,c,d,i,j⟩
  change (RomMix.mix (low a) (low b) (low c) (low d) (high i) (high j)).run (v ++ m) = _
  rw [RomMix.run_mix (v ++ m) (low a) (low b) (low c) (low d) (high i) (high j) hv]
  have hi := RomVector.append_get_right v m i
  have hj := RomVector.append_get_right v m j
  change (v ++ m).get (high i) = m.get i at hi
  change (v ++ m).get (high j) = m.get j at hj
  rw [hi,hj,mixed_append]
  rfl

theorem valid_round (indices : Indices) (h : indices ∈ Specs.BLAKE3.roundConstants.toList) : Valid indices := by
  change indices ∈ [(0,4,8,12,0,1),(1,5,9,13,2,3),(2,6,10,14,4,5),(3,7,11,15,6,7),
    (0,5,10,15,8,9),(1,6,11,12,10,11),(2,7,8,13,12,13),(3,4,9,14,14,15)] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Valid <;> decide

theorem fold_tuples (indices : List Indices) (valid : ∀ x ∈ indices, Valid x)
    (v m : Vector (BitVec 32) 16) :
    indices.foldl (fun state ix => (tupleOp ix).run state) (v ++ m) =
      indices.foldl (tupleRun m) v ++ m := by
  induction indices generalizing v with
  | nil => rfl
  | cons ix tail ih =>
    simp only [List.foldl_cons]
    rw [run_tuple ix (valid ix (by simp))]
    exact ih (fun x hx => valid x (by simp [hx])) _

def round : Operation := RomOperations.sequence (Specs.BLAKE3.roundConstants.toList.map tupleOp)

theorem run_round (v m : Vector (BitVec 32) 16) :
    round.run (v ++ m) = WordProgram.round RomWordSemantics.ops v m ++ m := by
  rw [round,run_sequence,List.foldl_map,fold_tuples _ valid_round]
  rw [Vector.foldl_toList]
  rfl

theorem round_cost : round.cost = 8704 := rfl

def rounds : Operation := RomOperations.sequence [round,permuteMessage,round,permuteMessage,
  round,permuteMessage,round,permuteMessage,round,permuteMessage,round,permuteMessage,round]

def sixthMessage (m : Vector (BitVec 32) 16) : Vector (BitVec 32) 16 :=
  WordProgram.permute (WordProgram.permute (WordProgram.permute
    (WordProgram.permute (WordProgram.permute (WordProgram.permute m)))))

theorem run_rounds (v m : Vector (BitVec 32) 16) :
    rounds.run (v ++ m) = WordProgram.rounds RomWordSemantics.ops v m ++ sixthMessage m := by
  simp only [rounds,RomOperations.sequence,List.foldr_cons,List.foldr_nil,
    RomOperations.Operation.then,RomOperations.identity,run_round,run_permuteMessage,id_eq]
  rfl

theorem rounds_cost : rounds.cost = 60928 := rfl

end Blake3Prize.Submission.RomRounds
