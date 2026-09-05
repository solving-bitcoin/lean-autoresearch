import Blake3Prize.Protected.WordExpression
import Lean

namespace Blake3Prize.Protected

/-- Boolean expressions use Lean's immutable, hash-cached syntax tree. Only
natural literals, Boolean operators, and word-bit projections are interpreted; other
nodes denote zero. This is data, never elaborated or executed as Lean code. -/
structure BitExpr where
  term : Lean.Expr

namespace BitExpr

def literal (n : Nat) : BitExpr := ⟨.lit (.natVal n)⟩
instance : Zero BitExpr := ⟨literal 0⟩
instance : One BitExpr := ⟨literal 1⟩
def inputExpr (i : Fin 512) : BitExpr := literal (i.val + 2)

def xor (a b : BitExpr) : BitExpr :=
  ⟨Lean.mkApp2 (Lean.mkConst `Blake3Prize.xorBit) a.term b.term⟩
def and (a b : BitExpr) : BitExpr :=
  ⟨Lean.mkApp2 (Lean.mkConst `Blake3Prize.andBit) a.term b.term⟩
instance : Add BitExpr := ⟨xor⟩
instance : Mul BitExpr := ⟨and⟩

def wordBit (word : WordExpr) (i : Fin 32) : BitExpr :=
  ⟨Lean.mkApp2 (Lean.mkConst `Blake3Prize.wordBit) word.term (.lit (.natVal i.val))⟩

def evalTerm (input : Input) : Lean.Expr → Bit
  | .lit (.natVal n) =>
      if n = 0 then 0 else if n = 1 then 1
      else input[(n - 2) % 512]'(Nat.mod_lt _ (by decide))
  | .app (.app (.const name _) a) b =>
      if name = `Blake3Prize.xorBit then evalTerm input a + evalTerm input b
      else if name = `Blake3Prize.andBit then evalTerm input a * evalTerm input b
      else if name = `Blake3Prize.wordBit then
        match b with
        | .lit (.natVal i) => bitOfBool ((WordExpr.evalTerm input a).testBit (i % 32))
        | _ => 0
      else 0
  | _ => 0

def eval (input : Input) (e : BitExpr) : Bit := evalTerm input e.term

@[simp] theorem eval_wordBit (input : Input) (word : WordExpr) (i : Fin 32) :
    eval input (wordBit word i) = bitOfBool ((WordExpr.eval input word).testBit i.val) := by
  change bitOfBool ((WordExpr.eval input word).testBit (i.val % 32)) = _
  rw [Nat.mod_eq_of_lt i.isLt]

@[simp] theorem eval_zero (input : Input) : eval input 0 = 0 := rfl
@[simp] theorem eval_one (input : Input) : eval input 1 = 1 := rfl
@[simp] theorem eval_add (input : Input) (a b : BitExpr) :
    eval input (a + b) = eval input a + eval input b := rfl
@[simp] theorem eval_mul (input : Input) (a b : BitExpr) :
    eval input (a * b) = eval input a * eval input b := rfl
@[simp] theorem eval_variable (input : Input) (i : Fin 512) :
    eval input (inputExpr i) = input[i] := by
  simp [eval, inputExpr, literal, evalTerm,
    Nat.mod_eq_of_lt i.isLt]

def inputs : Vector BitExpr 512 := Vector.ofFn inputExpr

end BitExpr
end Blake3Prize.Protected
