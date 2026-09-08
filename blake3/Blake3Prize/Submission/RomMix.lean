import Blake3Prize.Submission.RomOperations

set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace Blake3Prize.Submission.RomMix
open RomOperations

def mix (a b c d mx my : Fin 32) : Operation := sequence [
  add a a b, add a a mx, xor d d a, rotate d d 16,
  add c c d, xor b b c, rotate b b 12,
  add a a b, add a a my, xor d d a, rotate d d 8,
  add c c d, xor b b c, rotate b b 7]

def mixed (state : RomRegisters.State) (a b c d : Fin 32) (mx my : BitVec 32) :
    RomRegisters.State :=
  let va := (state.get a + state.get b) + mx
  let vd := (state.get d ^^^ va).rotateRight 16
  let vc := state.get c + vd
  let vb := (state.get b ^^^ vc).rotateRight 12
  let va := (va + vb) + my
  let vd := (vd ^^^ va).rotateRight 8
  let vc := vc + vd
  let vb := (vb ^^^ vc).rotateRight 7
  state.set a va |>.set b vb |>.set c vc |>.set d vd

theorem run_mix (state : RomRegisters.State) (a b c d mx my : Fin 32)
    (hd : [a.val,b.val,c.val,d.val,mx.val,my.val].Nodup) :
    (mix a b c d mx my).run state = mixed state a b c d (state.get mx) (state.get my) := by
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or,
    List.not_mem_nil,not_false_eq_true,and_true] at hd
  rcases hd with ⟨⟨hab,hac,had,hax,hay⟩,⟨hbc,hbd,hbx,hby⟩,
    ⟨hcd,hcx,hcy⟩,⟨hdx,hdy⟩,hxy⟩
  simp only [mix,RomOperations.sequence,List.foldr_cons,List.foldr_nil,
    RomOperations.Operation.then,RomOperations.identity,RomOperations.add,
    RomOperations.xor,RomOperations.rotate,id_eq]
  apply Vector.ext
  intro i hi
  by_cases ha : i = a.val <;> by_cases hb : i = b.val <;>
    by_cases hc : i = c.val <;> by_cases he : i = d.val <;>
    simp_all [mixed,Vector.get_eq_getElem,Vector.getElem_set,eq_comm]

theorem mix_cost (a b c d mx my : Fin 32) : (mix a b c d mx my).cost = 1088 := rfl

end Blake3Prize.Submission.RomMix
