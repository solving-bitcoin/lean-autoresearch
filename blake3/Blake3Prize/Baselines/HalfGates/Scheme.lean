import Blake3Prize.Protected.Target
import Blake3Prize.Baselines.HalfGates.Morphism
import Blake3Prize.Baselines.HalfGates.Lowering

/-! Executable port of examples/half_gates/garble.py. This is a runnable
candidate, not a finite-key ROM certificate. The common contract does not
import this module or require any of its circuit/half-gate machinery. -/
namespace Blake3Prize.Baselines.HalfGates.Executable
open Blake3Prize.Protected

private instance : Inhabited Gate := ⟨⟨false,0,0⟩⟩

private def circuit : Circuit := Lowering.compile referenceExpressions
private def block (value : Nat) : ByteArray :=
  ⟨(Vector.ofFn fun i : Fin 32 => UInt8.ofNat (value >>> (8*i.val))).toArray⟩
private def readBlock (bytes : ByteArray) (offset : Nat) : Nat := Id.run do
  let mut value := 0
  for i in [:32] do value := value ||| (bytes[offset+i]!.toNat <<< (8*i))
  return value
private def number (key : Label) : Nat := readBlock ⟨key.toArray⟩ 0
private def pad (hash : SecretRelease.Hash) (role index key : Nat) : Nat :=
  number (hash ("blake3-64-garbling/half-gates/v1".toUTF8 ++ ⟨#[0,UInt8.ofNat role]⟩ ++
    ⟨(Vector.ofFn fun i : Fin 8 => UInt8.ofNat (index >>> (8*i.val))).toArray⟩ ++ block key))
private def selected (b : Bool) (n : Nat) : Nat := if b then n else 0
private def zero (constant delta : Nat) (wires : Array Nat) (lit : Nat) : Nat :=
  (if lit < 2 then constant else wires[lit/2-1]!) ^^^ selected (lit.testBit 0) delta
private def active (constant : Nat) (wires : Array Nat) (lit : Nat) : Nat :=
  if lit < 2 then constant else wires[lit/2-1]!

/-- Independent coins for delta, the constant wire, and each input's zero wire. -/
def scheme : SecretRelease.Scheme challenge where
  Artifact := ByteArray
  randomnessBytes := 514*32
  garble := fun hash coins _ inputs outputs => Id.run do
    let raw : ByteArray := ⟨coins.toArray⟩
    let delta := readBlock raw 0 ||| 1
    let constant := readBlock raw 32
    let mut wires := (List.range 512).toArray.map fun i => readBlock raw (64+32*i)
    let mut result := block constant
    for i in (List.finRange 512) do
      let k0 := number ((inputs i).get false)
      let k1 := number ((inputs i).get true)
      let selector := (k0 ^^^ k1).log2
      let r0 := wires[i.val]! ^^^ pad hash 0 i.val k0
      let r1 := wires[i.val]! ^^^ delta ^^^ pad hash 0 i.val k1
      result := result ++ ⟨#[UInt8.ofNat selector]⟩ ++
        (if k0.testBit selector then block r1 ++ block r0 else block r0 ++ block r1)
    for i in [:circuit.gates.size] do
      let gate := circuit.gates[i]!
      let a0 := zero constant delta wires gate.left
      let b0 := zero constant delta wires gate.right
      if gate.isAnd then
        let ha0 := pad hash 1 i a0
        let ha1 := pad hash 1 i (a0 ^^^ delta)
        let hb0 := pad hash 2 i b0
        let hb1 := pad hash 2 i (b0 ^^^ delta)
        let tg := ha0 ^^^ ha1 ^^^ selected (b0.testBit 0) delta
        let te := hb0 ^^^ hb1 ^^^ a0
        let c0 := ha0 ^^^ selected (a0.testBit 0) tg ^^^ hb0 ^^^ selected (b0.testBit 0) (te ^^^ a0)
        wires := wires.push c0
        result := result ++ block tg ++ block te
      else wires := wires.push (a0 ^^^ b0)
    for i in (List.finRange 256) do
      let k0 := zero constant delta wires circuit.outputs[i.val]
      let k1 := k0 ^^^ delta
      let r0 := number ((outputs i).get false) ^^^ pad hash 3 i.val k0
      let r1 := number ((outputs i).get true) ^^^ pad hash 3 i.val k1
      result := result ++ (if k0.testBit 0 then block r1 ++ block r0 else block r0 ++ block r1)
    return result
  encode := id
  decode := fun bytes => if bytes.size = artifactBytes circuit then some bytes else none
  evaluate := fun hash bytes _ labels => Id.run do
    if labels.size != 512*32 then return none
    let constant := readBlock bytes 0
    let mut cursor := 32
    let mut wires : Array Nat := #[]
    for i in [:512] do
      let key := readBlock labels (32*i)
      let selector := bytes[cursor]!.toNat
      cursor := cursor+1
      let row := readBlock bytes (cursor + if key.testBit selector then 32 else 0)
      cursor := cursor+64
      wires := wires.push (row ^^^ pad hash 0 i key)
    for i in [:circuit.gates.size] do
      let gate := circuit.gates[i]!
      let a := active constant wires gate.left
      let b := active constant wires gate.right
      if gate.isAnd then
        let tg := readBlock bytes cursor
        let te := readBlock bytes (cursor+32)
        cursor := cursor+64
        wires := wires.push (pad hash 1 i a ^^^ selected (a.testBit 0) tg ^^^
          pad hash 2 i b ^^^ selected (b.testBit 0) (te ^^^ a))
      else wires := wires.push (a ^^^ b)
    let mut result := ByteArray.empty
    for i in (List.finRange 256) do
      let key := active constant wires circuit.outputs[i.val]
      let row := readBlock bytes (cursor + if key.testBit 0 then 32 else 0)
      cursor := cursor+64
      result := result ++ block (row ^^^ pad hash 3 i.val key)
    return some result

/-- Explicitly uncertified: size is measured; no proof field is fabricated. -/
def candidate : SecretRelease.Candidate challenge := ⟨scheme, 707680, none⟩
end Blake3Prize.Baselines.HalfGates.Executable
