import Blake3Prize.Submission.RomAdder

/-! Bit-order and modular-addition bridge. The carry theorem used here is
Lean's proved bit-blasting theorem; no native decision procedure is used. -/
namespace Blake3Prize.Submission.RomArithmetic
open RomAdder

def slice (word : BitVec w) (start count : Nat) : Vector Bool count :=
  Vector.ofFn fun i => word.getLsbD (start+i.val)

@[simp] theorem slice_get (word : BitVec w) (start count : Nat) (i : Fin count) :
    (slice word start count).get i = word.getLsbD (start+i.val) := by simp [slice]

theorem slice_drop (word : BitVec w) (start count : Nat) :
    RomVector.drop (slice word start (count+1)) = slice word (start+1) count := by
  ext i hi
  simp [RomVector.drop,slice,Vector.get_eq_getElem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem slice_cons (word : BitVec w) (start count : Nat) :
    slice word start (count+1) =
      RomVector.cons (word.getLsbD start) (slice word (start+1) count) := by
  simpa only [slice_get,Fin.val_zero,Nat.add_zero,slice_drop] using
    (RomVector.cons_drop (slice word start (count+1))).symm

theorem ripple_slice (x y : BitVec w) (initial : Bool) (start count : Nat)
    (h : start+count ≤ w) :
    rippleValues (slice x start count) (slice y start count)
      (BitVec.carry start x y initial) =
        slice (x+y+BitVec.setWidth w (BitVec.ofBool initial)) start count := by
  induction count generalizing start with
  | zero => apply Vector.ext; intro i hi; omega
  | succ count ih =>
    rw [rippleValues]
    simp only [slice_get,Fin.val_zero,Nat.add_zero,slice_drop,carry_majority,
      ← BitVec.carry_succ]
    rw [ih (start+1) (by omega),slice_cons]
    congr 1
    exact (BitVec.getLsbD_add_add_bool (by omega : start < w) x y initial).symm

def bits (word : BitVec w) : Vector Bool w := slice word 0 w

theorem ripple_add (x y : BitVec w) :
    rippleValues (bits x) (bits y) false = bits (x+y) := by
  simpa [bits] using ripple_slice x y false 0 w (by omega)

end Blake3Prize.Submission.RomArithmetic
