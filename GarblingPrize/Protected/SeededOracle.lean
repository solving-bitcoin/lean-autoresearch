import Mathlib.Data.Nat.Digits.Defs
import GarblingPrize.Protected.Codec
import GarblingPrize.Protected.Target
import GarblingPrize.Protected.SHA256

namespace GarblingPrize.Protected

/-!
# Protected seeded internal oracle

The ideal theorem samples `InternalOracle` directly. This module is the only
executable seed-to-internal-oracle implementation. It assumes HMAC-SHA256 is a
secure PRF and uses native exact rejection sampling; neither assumption is a
Lean theorem.

Input-label derivation is deliberately absent from the production API. The
small `TestLabelOracle` namespace at the end of this file exists only for the
CLI and regression harness until the external Rust label provider is added.
-/

abbrev MasterSeed := Bytes 32

namespace SeededInternalOracle

def domain : String := "g1-q-plus-rA/internal-uniform/v1"

/-- Self-delimiting, unbounded little-endian base-256 encoding. Each digit is
prefixed by `1` and the sequence ends in `0`. -/
def encodeNat (value : Nat) : ByteArray :=
  ((Nat.digits 256 value).foldl
    (fun output digit => (output.push 1).push (UInt8.ofNat digit))
    ByteArray.empty).push 0

/-- The native sampler receives a fixed 385-byte little-endian modulus. This
represents every positive value through `2^3072`, including the upper bound
itself. It returns the exact residue at the selected SHA-256 block width:
32 bytes for the BN254 moduli and at most 384 bytes in general. -/
@[extern "lean_g1_uniform_below"]
opaque uniformBelowArray : ByteArray → ByteArray → ByteArray → ByteArray

/-- Exact native sampler result as a natural.  The executable returns `none`
only for an invalid native boundary result.  The transparent body is the same
byte-level specification used before the direct native `Nat` conversion. -/
@[extern "lean_g1_uniform_below_nat"]
def uniformBelowNat? (seed : ByteArray) (modulus : ByteArray)
    (purpose : ByteArray) : Option Nat :=
  let raw := uniformBelowArray seed modulus purpose
  if _hsize : 0 < raw.size ∧ raw.size ≤ 384 ∧ raw.size % 32 = 0 then
    some (Codec.decodeNatLE
      (show Bytes raw.size from ⟨raw.data, rfl⟩))
  else
    none

private def modulusBytesUncached (value : Nat) : ByteArray :=
  (Codec.natLE 385 value).toByteArray

/-! The official construction makes hundreds of thousands of requests at
these three BN254 moduli. Closed values are initialized once by the compiled
runtime, avoiding repeated 385-byte `Nat` serialization without changing the
oracle address or its result. -/
private def baseModulusBytes : ByteArray :=
  modulusBytesUncached baseFieldModulus

private def baseUnitsModulusBytes : ByteArray :=
  modulusBytesUncached (baseFieldModulus - 1)

private def scalarModulusBytes : ByteArray :=
  modulusBytesUncached scalarFieldModulus

def modulusBytes (modulus : SamplingModulus) : ByteArray :=
  if modulus.value = baseFieldModulus then baseModulusBytes
  else if modulus.value = baseFieldModulus - 1 then baseUnitsModulusBytes
  else if modulus.value = scalarFieldModulus then scalarModulusBytes
  else
    modulusBytesUncached modulus.value

def sample (seed : MasterSeed) (modulus : SamplingModulus)
    (purpose : Purpose) : Fin modulus.value :=
  match uniformBelowNat? seed.toByteArray (modulusBytes modulus)
      (encodeNat purpose) with
  | some value =>
    if hvalue : value < modulus.value then
      ⟨value, hvalue⟩
    else
      ⟨0, modulus.positive⟩
  | none =>
    ⟨0, modulus.positive⟩

/-- The protected deterministic executable instantiation of `InternalOracle`.
Submissions receive the resulting typed oracle, never its seed or its native
implementation boundary. -/
def ofSeed (seed : MasterSeed) : InternalOracle :=
  fun modulus purpose => sample seed modulus purpose

end SeededInternalOracle

namespace TestLabelOracle

/-! This provider is test-only. Production callers supply `LabelPairs`
directly, after deriving them outside Lean with an independent label key. -/

def domain : String := "g1-q-plus-rA/test-label-pad/v1"

def address (wire : BitIndex) (value : Bool) (purpose : Purpose) : ByteArray :=
  SeededInternalOracle.encodeNat wire.val ++
    (ByteArray.empty.push (if value then 1 else 0)) ++
    SeededInternalOracle.encodeNat purpose

def pad (seed : MasterSeed) (wire : BitIndex) (value : Bool)
    (purpose : Purpose) : SeedLabel :=
  HMACSHA256.hash seed (domain.toUTF8 ++ address wire value purpose)

def labelPairs (seed : MasterSeed) : LabelPairs :=
  fun wire value purpose => pad seed wire value purpose

@[simp] theorem labelPairs_apply (seed : MasterSeed) (wire : BitIndex)
    (value : Bool) (purpose : Purpose) :
    labelPairs seed wire value purpose = pad seed wire value purpose := rfl

end TestLabelOracle

end GarblingPrize.Protected
