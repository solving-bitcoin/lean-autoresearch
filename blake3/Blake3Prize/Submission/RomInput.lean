import Blake3Prize.Submission.RomRegisters

set_option maxRecDepth 4096

namespace Blake3Prize.Submission.RomInput
open Blake3Prize.Protected RomProgram

def bits (input : Input) : Vector Bool 512 := Vector.ofFn (inputBit input)
def known (input : Input) : Vector Bool 514 := ((bits input).push false).push true

theorem known_input (input : Input) (i : Fin 512) :
    (known input).get ⟨i.val,by omega⟩ = inputBit input i := by
  simp (disch := omega) [known,bits,Vector.get_eq_getElem]

theorem known_zero (input : Input) : (known input).get ⟨512,by decide⟩ = false := by
  simp [known,Vector.get_eq_getElem]

theorem known_one (input : Input) : (known input).get ⟨513,by decide⟩ = true := by
  simp [known,Vector.get_eq_getElem]

theorem message_bit (input : Input) (i : Fin 16) (j : Fin 32) :
    ((RomWordSemantics.message input).get i).getLsbD j.val =
      inputBit input ⟨32*i.val+j.val,by omega⟩ := by
  have h := congrArg (fun v : Vector Nat 16 => v.get i) (RomWordSemantics.message_nat input)
  simp only [Vector.get_map] at h
  change (((RomWordSemantics.message input).get i).toNat.testBit j.val) = _
  rw [h]
  delta inputWords
  simp only [Vector.get_ofFn]
  change (BitVec.ofBoolListLE ((Vector.ofFn fun k : Fin 32 =>
    inputBit input ⟨32*i.val+k.val,by omega⟩).toList)).getLsbD j.val = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem,Vector.get_eq_getElem,j.isLt]

def prepare : RomProgram.Program 514 1025 := .done (Vector.ofFn fun i : Fin 1025 =>
  if h : i.val < 512 then
    if (RomWordSemantics.initial.get ⟨i.val/32,by omega⟩).getLsbD (i.val%32)
    then ⟨513,by decide⟩ else ⟨512,by decide⟩
  else if h : i.val < 1024 then ⟨i.val-512,by omega⟩
  else ⟨512,by decide⟩)

theorem prepare_correct (input : Input) :
    prepare.eval (known input) =
      RomRegisters.encoding (RomWordSemantics.initial ++ RomWordSemantics.message input) := by
  apply Vector.ext
  intro i hi
  simp only [prepare,RomProgram.Program.eval,Vector.getElem_map,Vector.getElem_ofFn]
  by_cases h0 : i < 512
  · rw [dif_pos h0]
    have h1 : i < 1024 := by omega
    have hw : i/32 < 16 := by omega
    have hl := RomVector.append_get_left RomWordSemantics.initial
      (RomWordSemantics.message input) ⟨i/32,hw⟩
    simp only [RomRegisters.encoding,Vector.getElem_ofFn,dif_pos h1]
    rw [hl]
    split <;> simp_all only [known_one,known_zero,Bool.true_eq_false,Bool.false_eq_true,
      Bool.not_eq_true,Bool.not_eq_false]
  · rw [dif_neg h0]
    by_cases h1 : i < 1024
    · rw [dif_pos h1,known_input input ⟨i-512,by omega⟩]
      simp only [RomRegisters.encoding,Vector.getElem_ofFn,dif_pos h1]
      have hw : i/32-16 < 16 := by omega
      have he : (⟨i/32,by omega⟩ : Fin 32) = ⟨16+(i/32-16),by omega⟩ := by
        apply Fin.ext
        change i/32 = 16+(i/32-16)
        omega
      rw [he,RomVector.append_get_right RomWordSemantics.initial
        (RomWordSemantics.message input) ⟨i/32-16,hw⟩,
        message_bit input ⟨i/32-16,hw⟩ ⟨i%32,by omega⟩]
      congr 1
      apply Fin.ext
      change i-512 = 32*(i/32-16)+i%32
      omega
    · rw [dif_neg h1,known_zero]
      simp [RomRegisters.encoding,h1]

end Blake3Prize.Submission.RomInput
