import Clean.Specs.BLAKE3
import SecretRelease.Encoding

namespace Blake3Prize.Protected

abbrev Input := SecretRelease.Bytes 64
abbrev Output := SecretRelease.Bytes 32

/-- Clean's little-endian parser, specialized to exactly one full block. -/
def inputWords (input : Input) : Vector Nat 16 :=
  Specs.BLAKE3.bytesToWords (input.toList.map UInt8.toNat)

def chainingValue : Vector Nat 8 := Specs.BLAKE3.iv.map UInt32.toNat

/-- Ordinary unkeyed 64-byte hash: CHUNK_START | CHUNK_END | ROOT = 11. -/
def referenceWords (message : Vector Nat 16) : Vector Nat 8 :=
  (Specs.BLAKE3.compress chainingValue message 0 64 11).take 8

def wordsToBytes (words : Vector Nat 8) : Output :=
  Vector.ofFn fun i => UInt8.ofNat (words[i.val / 4] >>> (8*(i.val % 4)))

def reference (input : Input) : Output := wordsToBytes (referenceWords (inputWords input))

end Blake3Prize.Protected
