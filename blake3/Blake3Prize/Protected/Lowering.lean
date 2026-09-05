import Blake3Prize.Protected.Expression

namespace Blake3Prize.Protected

/-- Literals 0/1 are public constants. A wire i has literal 2*(i+1);
its complement is the next literal. Input wires occupy indices 0..511. -/
structure Gate where
  isAnd : Bool
  left : Nat
  right : Nat
  deriving Repr, Lean.ToJson

structure Circuit where
  gates : Array Gate
  outputs : Vector Nat 256

structure LowerState where
  gates : Array Gate := #[]
  terms : Std.HashMap Lean.ExprStructEq Nat := {}
  nodes : Std.HashMap (Bool × Nat × Nat) Nat := {}

namespace Lowering

def emit (isAnd : Bool) (a b : Nat) : StateM LowerState Nat := do
  let (a,b) := if a ≤ b then (a,b) else (b,a)
  if isAnd then
    if a = 0 then return 0
    if a = 1 then return b
    if a = b then return a
    if Nat.xor a 1 = b then return 0
  else
    if a = 0 then return b
    if a = 1 then return Nat.xor b 1
    if a = b then return 0
    if Nat.xor a 1 = b then return 1
  let state ← get
  let key := (isAnd, a, b)
  if let some wire := state.nodes[key]? then return wire
  let wire := 2 * (513 + state.gates.size)
  set { state with
    gates := state.gates.push ⟨isAnd, a, b⟩
    nodes := state.nodes.insert key wire }
  return wire

/-- Structural hash-consing uses exact Lean.Expr equality after hashing.
Hash collisions cannot identify unequal terms. Unsupported syntax denotes 0,
matching BitExpr.evalTerm; it is never executed as metaprogram code. -/
def term (e : Lean.Expr) : StateM LowerState Nat := do
  if let some wire := (← get).terms[Lean.ExprStructEq.mk e]? then return wire
  let wire ← match e with
    | .lit (.natVal n) => pure <|
        if n = 0 then 0 else if n = 1 then 1 else 2 * (((n-2) % 512) + 1)
    | .app (.app (.const name _) a) b => do
        if name = `Blake3Prize.xorBit then emit false (← term a) (← term b)
        else if name = `Blake3Prize.andBit then emit true (← term a) (← term b)
        else pure 0
    | _ => pure 0
  modify fun state => {state with terms := state.terms.insert (Lean.ExprStructEq.mk e) wire}
  return wire
termination_by e

def compile (expressions : Vector BitExpr 256) : Circuit :=
  let (outputs,state) := (expressions.mapM fun e => term e.term).run {}
  ⟨state.gates, outputs⟩

end Lowering

/-- The complete artifact contains one constant label, 512 adapters
(selector byte + two label blocks), two blocks per AND, and 256 output
translation tables of two blocks. XOR and complemented wires are free. -/
def artifactBytes (circuit : Circuit) : Nat :=
  32 + 512 * (1 + 2 * 32) + 64 * (circuit.gates.filter Gate.isAnd).size + 256 * 64

theorem artifactBytes_eq (circuit : Circuit) :
    artifactBytes circuit = 49696 + 64 * (circuit.gates.filter Gate.isAnd).size := by
  unfold artifactBytes
  omega

end Blake3Prize.Protected
