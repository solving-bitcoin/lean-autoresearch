import Blake3Prize.Submission.RomProgram
import Mathlib.Data.BitVec

/-! The ripple adder uses one AND and four XOR gates per bit. Its carry is
((a XOR c) AND (b XOR c)) XOR c, the Boolean majority function. All gates
still receive ordinary four-row tables in this first certified construction. -/
namespace Blake3Prize.Submission.RomAdder
open RomCircuit RomProgram

def old (i : Fin n) (extra : Nat) : Fin (n+extra) := ⟨i.val,by omega⟩

def fullAdder (a b c : Fin n) : RomProgram.Program n (n+5) :=
  .step ⟨false,a,c⟩ <|
  .step ⟨false,old b 1,old c 1⟩ <|
  .step ⟨false,⟨n,by omega⟩,old b 2⟩ <|
  .step ⟨true,⟨n,by omega⟩,⟨n+1,by omega⟩⟩ <|
  .step ⟨false,⟨n+3,by omega⟩,old c 4⟩ <|
  identity (n+5)

def carry (a b c : Bool) : Bool := ((a ^^ c) && (b ^^ c)) ^^ c

theorem carry_majority (a b c : Bool) : carry a b c = Bool.atLeastTwo a b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem sum_reorder (a b c : Bool) : ((a ^^ c) ^^ b) = (a ^^ (b ^^ c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem fullAdder_eval (a b c : Fin n) (input : Vector Bool n) :
    (fullAdder a b c).eval input =
      ((((input.push (input.get a ^^ input.get c)).push
        (input.get b ^^ input.get c)).push
        ((input.get a ^^ input.get c) ^^ input.get b)).push
        ((input.get a ^^ input.get c) && (input.get b ^^ input.get c))).push
        (carry (input.get a) (input.get b) (input.get c)) := by
  simp (disch := omega) only [fullAdder,RomProgram.Program.eval,eval_identity,
    Gate.function,old,carry,Bool.false_eq_true,if_false,if_true,
    Vector.get_eq_getElem,Vector.getElem_push_lt,Vector.getElem_push_eq]

@[simp] theorem fullAdder_old (a b c i : Fin n) (input : Vector Bool n) :
    ((fullAdder a b c).eval input).get (old i 5) = input.get i := by
  rw [fullAdder_eval]
  simp (disch := omega) only [old,Vector.get_eq_getElem,Vector.getElem_push_lt]

@[simp] theorem fullAdder_sum (a b c : Fin n) (input : Vector Bool n) :
    ((fullAdder a b c).eval input).get ⟨n+2,by omega⟩ =
      (input.get a ^^ (input.get b ^^ input.get c)) := by
  rw [fullAdder_eval]
  simp (disch := omega) only [Vector.get_eq_getElem,Vector.getElem_push_lt,Vector.getElem_push_eq]
  exact sum_reorder _ _ _

@[simp] theorem fullAdder_carry (a b c : Fin n) (input : Vector Bool n) :
    ((fullAdder a b c).eval input).get ⟨n+4,by omega⟩ =
      carry (input.get a) (input.get b) (input.get c) := by
  rw [fullAdder_eval]
  simp only [Vector.get_eq_getElem,Vector.getElem_push_eq]

def ripple : {w : Nat} → Vector (Fin n) w → Vector (Fin n) w → Fin n → RomProgram.Program n w
  | 0, _, _, _ => .done #v[]
  | w+1, a, b, c =>
      (fullAdder (a.get 0) (b.get 0) c).comp
        ((ripple ((RomVector.drop a).map (fun i => old i 5))
          ((RomVector.drop b).map (fun i => old i 5)) ⟨n+4,by omega⟩).keepOne ⟨n+2,by omega⟩)

def rippleValues : {w : Nat} → Vector Bool w → Vector Bool w → Bool → Vector Bool w
  | 0, _, _, _ => #v[]
  | _+1, a, b, c => RomVector.cons (a.get 0 ^^ (b.get 0 ^^ c))
      (rippleValues (RomVector.drop a) (RomVector.drop b) (carry (a.get 0) (b.get 0) c))

theorem eval_ripple (a b : Vector (Fin n) w) (c : Fin n) (input : Vector Bool n) :
    (ripple a b c).eval input = rippleValues (a.map input.get) (b.map input.get) (input.get c) := by
  induction w generalizing n with
  | zero => simp [ripple,RomProgram.Program.eval,rippleValues]
  | succ w ih =>
    simp only [ripple,eval_comp,eval_keepOne,fullAdder_sum,ih,fullAdder_carry]
    have ha : (((RomVector.drop a).map (fun i => old i 5)).map
        ((fullAdder (a.get 0) (b.get 0) c).eval input).get) = (RomVector.drop a).map input.get := by
      ext i hi
      change (((RomVector.drop a).map (fun i => old i 5)).map
        ((fullAdder (a.get 0) (b.get 0) c).eval input).get).get ⟨i,hi⟩ =
        ((RomVector.drop a).map input.get).get ⟨i,hi⟩
      simp only [Vector.get_map,fullAdder_old]
    have hb : (((RomVector.drop b).map (fun i => old i 5)).map
        ((fullAdder (a.get 0) (b.get 0) c).eval input).get) = (RomVector.drop b).map input.get := by
      ext i hi
      change (((RomVector.drop b).map (fun i => old i 5)).map
        ((fullAdder (a.get 0) (b.get 0) c).eval input).get).get ⟨i,hi⟩ =
        ((RomVector.drop b).map input.get).get ⟨i,hi⟩
      simp only [Vector.get_map,fullAdder_old]
    rw [ha,hb]
    simp only [rippleValues,Vector.get_map,RomVector.drop_map]

end Blake3Prize.Submission.RomAdder
