import Blake3Prize.Submission.RomOperations

set_option maxRecDepth 4096

namespace Blake3Prize.Submission.RomPermutation
open RomRegisters RomProgram RomOperations

def reorder (mapping : Fin 32 → Fin 32) : Operation where
  run state := Vector.ofFn fun i => state.get (mapping i)
  program := .done (Vector.ofFn fun i : Fin 1025 =>
    if h : i.val < 1024 then
      (word (mapping ⟨i.val/32,by omega⟩)).get ⟨i.val%32,by omega⟩
    else zero)
  correct state := by
    apply Vector.ext
    intro i hi
    by_cases h : i < 1024
    · have hw := congrArg (fun v : Vector Bool 32 => v.get ⟨i%32,by omega⟩)
        (encoding_word state (mapping ⟨i/32,by omega⟩))
      simp only [Vector.get_map] at hw
      simp only [RomProgram.Program.eval,Vector.getElem_map,Vector.getElem_ofFn,
        dif_pos h]
      rw [hw]
      simp [encoding,RomArithmetic.bits,RomArithmetic.slice,h,Vector.get_eq_getElem,
        BitVec.getLsbD_eq_getElem (by omega : i%32 < 32)]
    · simp [RomProgram.Program.eval,h,encoding,zero,Vector.get_eq_getElem]
  cost := 0
  count := rfl

def low (i : Fin 16) : Fin 32 := ⟨i.val,by omega⟩
def high (i : Fin 16) : Fin 32 := ⟨16+i.val,by omega⟩

def messageMap (i : Fin 32) : Fin 32 :=
  if h : i.val < 16 then i
  else high (Specs.BLAKE3.msgPermutation.get ⟨i.val-16,by omega⟩)

def permuteMessage : Operation := reorder messageMap

theorem run_permuteMessage (v m : Vector (BitVec 32) 16) :
    permuteMessage.run (v ++ m) = v ++ HalfGates.WordProgram.permute m := by
  apply Vector.ext
  intro i hi
  change ((Vector.ofFn fun j : Fin 32 => (v ++ m).get (messageMap j)))[i] = _
  simp only [Vector.getElem_ofFn]
  change (v ++ m).get (messageMap ⟨i,hi⟩) =
    (v ++ HalfGates.WordProgram.permute m).get ⟨i,hi⟩
  by_cases h : i < 16
  · simp only [messageMap,dif_pos h]
    rw [RomVector.append_get_left v m ⟨i,h⟩,
      RomVector.append_get_left v (HalfGates.WordProgram.permute m) ⟨i,h⟩]
  · simp only [messageMap,dif_neg h]
    calc
      _ = m.get (Specs.BLAKE3.msgPermutation.get ⟨i-16,by omega⟩) :=
        RomVector.append_get_right v m _
      _ = (HalfGates.WordProgram.permute m).get ⟨i-16,by omega⟩ := by
        simp [HalfGates.WordProgram.permute,Vector.get_eq_getElem]
      _ = (v ++ HalfGates.WordProgram.permute m).get ⟨16+(i-16),by omega⟩ :=
        (RomVector.append_get_right v (HalfGates.WordProgram.permute m) ⟨i-16,by omega⟩).symm
      _ = _ := congrArg (v ++ HalfGates.WordProgram.permute m).get
        (Fin.ext (by change 16+(i-16) = i; omega))

end Blake3Prize.Submission.RomPermutation
