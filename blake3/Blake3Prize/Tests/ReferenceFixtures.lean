import Blake3Prize.Protected.Reference

namespace Blake3Prize.Tests
open Blake3Prize.Protected

/-- Byte-oriented specialization using Clean's own little-endian packing. -/
def referenceBytes (input : Vector UInt8 64) : Vector Nat 32 :=
  let words := referenceWords (Specs.BLAKE3.bytesToWords (input.toList.map UInt8.toNat))
  Vector.ofFn fun i => (words[i.val / 4] / 2^(8*(i.val % 4))) % 256

/-- Public plaintext input supplied to evaluation, byte-major and LSB-first. -/
def inputFromBytes (message : Vector UInt8 64) : Input :=
  Vector.ofFn fun i => bitOfBool (message[i.val / 8].toNat.testBit (i.val % 8))

end Blake3Prize.Tests
