import Challenge.Instances.Blake3CompressGF2Canonical.Spec

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

open Challenge.Instances.Blake3CompressGF2Canonical.Interface

/-- Full 64-byte unkeyed hash: CV=IV, counter=0, blockLen=64,
CHUNK_START|CHUNK_END|ROOT=11. Bit 8*i+j is bit j of byte i. -/
def hashWords {α : Type} [Zero α] [One α] (input : Vector α 512) :
    Vector (Blake3Bits.Word α) 28 :=
  Vector.ofFn fun i =>
    if h : i.val < 8 then Blake3Bits.constWord (Specs.Blake3.iv[i.val])
    else if h : i.val < 24 then
      (Blake3Bits.splitWords 16 input)[i.val - 8]'(by omega)
    else Blake3Bits.constWord (if i.val = 26 then 64 else if i.val = 27 then 11 else 0)

/-- Specialization of the frozen zk.golf GF(2) compression specification. -/
def reference (input : Input) : Output :=
  let all := Blake3Bits.compressState (hashWords input)
  Vector.ofFn fun i => all[i.val]'(by omega)

/-- The upstream natural-number specification is also available to proofs. -/
def referenceBytes (input : Vector UInt8 64) : Vector Nat 32 :=
  Specs.Blake3.blake3 (input.map UInt8.toNat)

def inputBit (input : Input) (i : InputIndex) : Bool := input[i].val = 1

def activeInput (pairs : InputLabelPairs) (input : Input) : ActiveInputLabels :=
  Vector.ofFn fun i => pairs i (inputBit input i)

def activeOutput (pairs : OutputLabelPairs) (output : Output) : ActiveOutputLabels :=
  Vector.ofFn fun i => pairs i (output[i].val = 1)

/-- Distinct external labels are necessary for universal correctness. No
correlation or selector-bit convention is imposed on caller-supplied pairs. -/
def DistinctPairs {n : Nat} (pairs : Fin n → Bool → Label) : Prop :=
  ∀ i, pairs i false ≠ pairs i true

end Blake3Prize.Protected
