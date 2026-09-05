import Blake3Prize.Protected.Reference
import Lean

namespace Blake3Prize.Protected

/-- Hash-cached syntax for bounded word expressions. It is interpreted as data,
never elaborated as Lean code. Every literal is reduced modulo 2^32. -/
structure WordExpr where
  term : Lean.Expr

namespace WordExpr

def literal (n : Nat) : WordExpr := ⟨.lit (.natVal n)⟩
def inputWord (i : Fin 16) : WordExpr :=
  ⟨Lean.mkApp (Lean.mkConst `Blake3Prize.inputWord) (.lit (.natVal i.val))⟩
def add (a b : WordExpr) : WordExpr :=
  ⟨Lean.mkApp2 (Lean.mkConst `Blake3Prize.addWord) a.term b.term⟩
def xor (a b : WordExpr) : WordExpr :=
  ⟨Lean.mkApp2 (Lean.mkConst `Blake3Prize.xorWord) a.term b.term⟩
def rotate (a : WordExpr) (n : Nat) : WordExpr :=
  ⟨Lean.mkApp2 (Lean.mkConst `Blake3Prize.rotateWord) a.term (.lit (.natVal n))⟩

def evalTerm (input : Input) : Lean.Expr → Nat
  | .lit (.natVal n) => n % 2^32
  | .app (.const name _) (.lit (.natVal i)) =>
      if name = `Blake3Prize.inputWord then (inputWords input)[i % 16] else 0
  | .app (.app (.const name _) a) b =>
      if name = `Blake3Prize.addWord then add32 (evalTerm input a) (evalTerm input b)
      else if name = `Blake3Prize.xorWord then (evalTerm input a) ^^^ (evalTerm input b)
      else if name = `Blake3Prize.rotateWord then
        match b with
        | .lit (.natVal n) => rotRight32 (evalTerm input a) n
        | _ => 0
      else 0
  | _ => 0

def eval (input : Input) (e : WordExpr) : Nat := evalTerm input e.term

@[simp] theorem eval_literal (input : Input) (n : Nat) :
    eval input (literal n) = n % 2^32 := rfl
@[simp] theorem eval_input (input : Input) (i : Fin 16) :
    eval input (inputWord i) = (inputWords input)[i] := by
  change (inputWords input)[i.val % 16] = (inputWords input)[i]
  simp [Nat.mod_eq_of_lt i.isLt]
@[simp] theorem eval_add (input : Input) (a b : WordExpr) :
    eval input (add a b) = add32 (eval input a) (eval input b) := rfl
@[simp] theorem eval_xor (input : Input) (a b : WordExpr) :
    eval input (xor a b) = eval input a ^^^ eval input b := rfl
@[simp] theorem eval_rotate (input : Input) (a : WordExpr) (n : Nat) :
    eval input (rotate a n) = rotRight32 (eval input a) n := rfl

def inputs : Vector WordExpr 16 := Vector.ofFn inputWord

end WordExpr
end Blake3Prize.Protected
