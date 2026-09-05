import Clean.Specs.BLAKE3
import Mathlib.Data.ZMod.Basic

namespace Blake3Prize.Protected

abbrev Bit := ZMod 2
abbrev Input := Vector Bit 512
abbrev Output := Vector Bit 256
abbrev InputIndex := Fin 512
abbrev OutputIndex := Fin 256
abbrev Label := Vector UInt8 32
abbrev InputLabelPairs := InputIndex → Bool → Label
abbrev OutputLabelPairs := OutputIndex → Bool → Label
abbrev ActiveInputLabels := Vector Label 512
abbrev ActiveOutputLabels := Vector Label 256

def bitOfBool (b : Bool) : Bit := if b then 1 else 0

def inputBit (input : Input) (i : InputIndex) : Bool := input[i].val = 1

/-- Pack the label interface's little-endian bits into Clean's 16 words.
BitVec provides a bounded 32-bit representation before conversion to Nat. -/
def inputWords (input : Input) : Vector Nat 16 :=
  Vector.ofFn fun i =>
    (BitVec.ofBoolListLE ((Vector.ofFn fun j : Fin 32 =>
      inputBit input ⟨32*i.val+j.val, by omega⟩).toList)).toNat

def outputBits (words : Vector Nat 8) : Output :=
  Vector.ofFn fun i => bitOfBool (words[i.val / 32].testBit (i.val % 32))

def chainingValue : Vector Nat 8 := Specs.BLAKE3.iv.map UInt32.toNat

/-- Clean's MIT-licensed compression, specialized to the ordinary 64-byte
unkeyed hash. CHUNK_START | CHUNK_END | ROOT = 11; this is a single root block. -/
def referenceWords (message : Vector Nat 16) : Vector Nat 8 :=
  (Specs.BLAKE3.compress chainingValue message 0 64 11).take 8

def reference (input : Input) : Output := outputBits (referenceWords (inputWords input))

/-- Byte-oriented specialization using Clean's own little-endian packing. -/
def referenceBytes (input : Vector UInt8 64) : Vector Nat 32 :=
  let words := referenceWords (Specs.BLAKE3.bytesToWords (input.toList.map UInt8.toNat))
  Vector.ofFn fun i => (words[i.val / 4] / 2^(8*(i.val % 4))) % 256

def activeInput (pairs : InputLabelPairs) (input : Input) : ActiveInputLabels :=
  Vector.ofFn fun i => pairs i (inputBit input i)

def activeOutput (pairs : OutputLabelPairs) (output : Output) : ActiveOutputLabels :=
  Vector.ofFn fun i => pairs i (output[i].val = 1)

/-- No correlation or selector-bit convention is imposed on external pairs. -/
def DistinctPairs {n : Nat} (pairs : Fin n → Bool → Label) : Prop :=
  ∀ i, pairs i false ≠ pairs i true

/-- Public plaintext input supplied to evaluation, byte-major and LSB-first. -/
def inputFromBytes (message : Vector UInt8 64) : Input :=
  Vector.ofFn fun i => bitOfBool (message[i.val / 8].toNat.testBit (i.val % 8))

end Blake3Prize.Protected
