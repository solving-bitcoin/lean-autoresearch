import Blake3Prize.Baselines.HalfGates.Expression

namespace Blake3Prize.Baselines.HalfGates
open Blake3Prize.Protected

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
  words : Std.HashMap Lean.ExprStructEq (Vector Nat 32) := {}
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

/-- The characteristic-two majority carry uses one AND per bit:
c' = ((x XOR c) AND (y XOR c)) XOR c. The final carry is discarded. -/
def addWords (a b : Vector Nat 32) : StateM LowerState (Vector Nat 32) := do
  let mut carry := 0
  let mut result := Vector.replicate 32 0
  for i in (Vector.finRange 32).toList do
    let ac ← emit false a[i] carry
    let bc ← emit false b[i] carry
    result := result.set i (← emit false ac b[i])
    if i.val < 31 then carry ← emit false (← emit true ac bc) carry
  return result

def wordTerm (e : Lean.Expr) : StateM LowerState (Vector Nat 32) := do
  if let some value := (← get).words[Lean.ExprStructEq.mk e]? then return value
  let value ← match e with
    | .lit (.natVal n) => pure <| Vector.ofFn fun i => if n.testBit i.val then 1 else 0
    | .app (.const name _) (.lit (.natVal i)) =>
        pure <| if name = `Blake3Prize.inputWord then
          Vector.ofFn fun j => 2 * (32*(i % 16) + j.val + 1)
        else Vector.replicate 32 0
    | .app (.app (.const name _) a) b => do
        if name = `Blake3Prize.addWord then addWords (← wordTerm a) (← wordTerm b)
        else if name = `Blake3Prize.xorWord then
          let av ← wordTerm a
          let bv ← wordTerm b
          (Vector.finRange 32).mapM fun i => emit false av[i] bv[i]
        else if name = `Blake3Prize.rotateWord then
          match b with
          | .lit (.natVal n) =>
              let av ← wordTerm a
              pure <| Vector.ofFn fun i => av[(i.val + n % 32) % 32]
          | _ => pure (Vector.replicate 32 0)
        else pure (Vector.replicate 32 0)
    | _ => pure (Vector.replicate 32 0)
  modify fun state => { state with words := state.words.insert (Lean.ExprStructEq.mk e) value }
  return value
termination_by e

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
        else if name = `Blake3Prize.wordBit then
          match b with
          | .lit (.natVal i) =>
              let av ← wordTerm a
              pure av[i % 32]
          | _ => pure 0
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

end Blake3Prize.Baselines.HalfGates
