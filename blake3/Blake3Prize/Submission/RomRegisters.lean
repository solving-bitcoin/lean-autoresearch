import Blake3Prize.Submission.RomWordSemantics
import Blake3Prize.Submission.RomParallel

set_option maxRecDepth 4096

/-! Thirty-two 32-bit registers plus a permanent zero wire. The first
sixteen registers hold the compression state; the last sixteen the message.
Each update retains the other registers through public wire references. -/
namespace Blake3Prize.Submission.RomRegisters
open RomProgram RomArithmetic

abbrev State := Vector (BitVec 32) 32
abbrev StateProgram := RomProgram.Program 1025 1025

def encoding (state : State) : Vector Bool 1025 :=
  Vector.ofFn fun i => if h : i.val < 1024 then
    (state.get ⟨i.val/32,by omega⟩).getLsbD (i.val%32) else false

def word (register : Fin 32) : Vector (Fin 1025) 32 :=
  Vector.ofFn fun i => ⟨32*register.val+i.val,by omega⟩

def zero : Fin 1025 := ⟨1024,by decide⟩

theorem encoding_word (state : State) (register : Fin 32) :
    (word register).map (encoding state).get = bits (state.get register) := by
  ext i hi
  have hlt : 32*register.val+i < 1024 := by omega
  have hd : (32*register.val+i)/32 = register.val := by omega
  have hm : (32*register.val+i)%32 = i := by omega
  simp [word,encoding,bits,slice,Vector.get_eq_getElem,hlt,hd,hm,BitVec.getLsbD_eq_getElem hi]

theorem encoding_zero (state : State) : (encoding state).get zero = false := by
  simp [encoding,zero]

def write (register : Fin 32) (program : RomProgram.Program 1025 32) : StateProgram :=
  (program.keep (Vector.finRange 1025)).comp <|
    .done (Vector.ofFn fun i : Fin 1025 =>
      if h : i.val < 1024 ∧ i.val/32 = register.val then
        (⟨1025+i.val%32,by omega⟩ : Fin (1025+32))
      else ⟨i.val,by omega⟩)

theorem eval_write (state : State) (register : Fin 32) (result : BitVec 32)
    (program : RomProgram.Program 1025 32) (hp : program.eval (encoding state) = bits result) :
    (write register program).eval (encoding state) = encoding (state.set register result) := by
  unfold write
  rw [eval_comp,eval_keep,hp]
  have he : (Vector.finRange 1025).map (encoding state).get = encoding state :=
    eval_identity (encoding state)
  rw [he]
  apply Vector.ext
  intro i hi
  simp only [RomProgram.Program.eval,Vector.getElem_map,Vector.getElem_ofFn]
  by_cases hb : i < 1024
  · by_cases hr : i/32 = register.val
    · rw [dif_pos (show i < 1024 ∧ i/32 = register.val from ⟨hb,hr⟩)]
      rw [RomVector.append_get_right (encoding state) (bits result) ⟨i%32,by omega⟩]
      simp [encoding,bits,slice,hb,hr,Vector.get_eq_getElem,
        BitVec.getLsbD_eq_getElem (by omega : i%32 < 32)]
    · rw [dif_neg (show ¬(i < 1024 ∧ i/32 = register.val) from fun h => hr h.2)]
      rw [RomVector.append_get_left (encoding state) (bits result) ⟨i,hi⟩]
      simp [encoding,hb,hr,Ne.symm hr,Vector.get_eq_getElem,Vector.getElem_set]
  · rw [dif_neg (show ¬(i < 1024 ∧ i/32 = register.val) from fun h => hb h.1)]
    rw [RomVector.append_get_left (encoding state) (bits result) ⟨i,hi⟩]
    simp [encoding,hb,Vector.get_eq_getElem]

def add (target left right : Fin 32) : StateProgram :=
  write target (RomAdder.ripple (word left) (word right) zero)

theorem eval_add (state : State) (target left right : Fin 32) :
    (add target left right).eval (encoding state) =
      encoding (state.set target (state.get left + state.get right)) := by
  apply eval_write
  rw [RomAdder.eval_ripple,encoding_word,encoding_word,encoding_zero,ripple_add]

def xor (target left right : Fin 32) : StateProgram :=
  write target (RomParallel.xorWords (word left) (word right))

theorem eval_xor (state : State) (target left right : Fin 32) :
    (xor target left right).eval (encoding state) =
      encoding (state.set target (state.get left ^^^ state.get right)) := by
  apply eval_write
  rw [RomParallel.eval_xorWords]
  have hl := encoding_word state left
  have hr := encoding_word state right
  apply Vector.ext
  intro i hi
  have hl' := congrArg (fun v : Vector Bool 32 => v.get ⟨i,hi⟩) hl
  have hr' := congrArg (fun v : Vector Bool 32 => v.get ⟨i,hi⟩) hr
  simp only [Vector.get_map] at hl' hr'
  simp only [Vector.getElem_ofFn]
  change ((encoding state).get ((word left).get ⟨i,hi⟩) ^^
    (encoding state).get ((word right).get ⟨i,hi⟩)) =
    (bits (state.get left ^^^ state.get right)).get ⟨i,hi⟩
  rw [hl',hr']
  simp [bits,slice]

def rotate (target source : Fin 32) (offset : Nat) : StateProgram :=
  write target (.done (Vector.ofFn fun i : Fin 32 =>
    (word source).get ⟨(i.val+offset%32)%32,by omega⟩))

theorem eval_rotate (state : State) (target source : Fin 32) (offset : Nat) :
    (rotate target source offset).eval (encoding state) =
      encoding (state.set target ((state.get source).rotateRight offset)) := by
  apply eval_write
  apply Vector.ext
  intro i hi
  have hr := congrArg (fun v : Vector Bool 32 => v.get ⟨(i+offset%32)%32,by omega⟩)
    (encoding_word state source)
  simp only [Vector.get_map] at hr
  simp only [RomProgram.Program.eval,Vector.getElem_map,Vector.getElem_ofFn]
  change (encoding state).get ((word source).get ⟨(i+offset%32)%32,by omega⟩) = _
  rw [hr]
  simp only [bits,slice,Vector.get_ofFn,Vector.getElem_ofFn,Nat.zero_add,
    BitVec.getLsbD_rotateRight]
  by_cases h : i < 32-offset%32
  · simp only [h,decide_true,Bool.cond_true]
    exact congrArg ((state.get source).getLsbD) (by omega : (i+offset%32)%32 = offset%32+i)
  · simp only [h,decide_false,Bool.cond_false,hi,decide_true,Bool.true_and]
    exact congrArg ((state.get source).getLsbD) (by omega : (i+offset%32)%32 = i-(32-offset%32))

end Blake3Prize.Submission.RomRegisters
