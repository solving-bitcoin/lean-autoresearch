import WotsLamport.Protected.ScriptRelation
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

namespace WotsLamport.Protected
open SecretRelease

/-- Author-owned numerical TARGET, not a claimed reduction. A 2^32 honest-query
budget and a 2^20 multi-target margin are explicit. A certificate must prove
this bound, including setup, chain collisions, masks and coefficient bias. -/
def romTarget : ClassicalBoundedQueryROM where
  maxQueries := 2^48
  error := fun q => (2^20 : ℚ≥0) * (q + 2^32 + 1)^2 / 2^256
  nontrivial := by
    intro q hq
    have hq' : (q : ℚ≥0) ≤ (2^48 : ℚ≥0) := by exact_mod_cast hq
    calc
      (2^20 : ℚ≥0) * (q + 2^32 + 1)^2 / 2^256 ≤
          2^20 * (2^48 + 2^32 + 1)^2 / 2^256 := by gcongr
      _ < 1 := by norm_num

def challenge : SecretRelease.Challenge where
  Private := Unit
  Input := Message
  Output := Message
  privateCodec := privateCodec
  inputCodec := inputCodec
  inputs := wotsDisclosure
  outputs := Lamport outputCodec
  reference := fun _ m => m
  Claim := Fin 256 × Label
  wins := fun _ _ m _ labels claim =>
    claim.2 = (labels claim.1).get (!(outputCodec.encode m)[claim.1.val])
  withholding := some fun _ _ _ _ labels claim =>
    claim.2 = (labels claim.1).get false ∨ claim.2 = (labels claim.1).get true
  rom := romTarget

/-- The only admitted construction interface. The author wrapper exposes the
actual WOTS pk as the first 2,144 scored bytes before AND after release. -/
structure Construction where
  randomnessBytes : Nat
  prepare : Hash → Bytes randomnessBytes → Keys → challenge.outputs.Keys → ByteArray
  expand : Hash → PublicKey → ByteArray → Message → Signature → Option ByteArray

def wrapped (s : Construction) : Scheme challenge where
  Artifact := ByteArray
  randomnessBytes := s.randomnessBytes
  garble := fun h coins _ keys labels => keyCodec.encode (publicKey h keys) ++ s.prepare h coins keys labels
  encode := id
  decode := some
  evaluate := fun h bytes m active => do
    let pk ← keyCodec.decode (bytes.extract 0 2144)
    let sig ← keyCodec.decode active
    if verifies h pk (encodeWord m) sig then
      s.expand h pk (bytes.extract 2144 bytes.size) m sig
    else none

theorem publicKey_visible (s : Construction) (h : Hash) (coins : Bytes s.randomnessBytes)
    (keys : Keys) (labels : challenge.outputs.Keys) :
    ∃ body, (wrapped s).garbleBytes h coins () keys labels = keyCodec.encode (publicKey h keys) ++ body :=
  ⟨s.prepare h coins keys labels, rfl⟩

theorem wrapped_decode_encode (s : Construction) (a : ByteArray) :
    (wrapped s).decode ((wrapped s).encode a) = some a := rfl

theorem wrapped_encode_decode (s : Construction) (b a : ByteArray)
    (h : (wrapped s).decode b = some a) : (wrapped s).encode a = b :=
  (Option.some.inj h).symm

structure Entry where
  construction : Construction
  maxBytes : Nat
  certificate : Option (Certificate (wrapped construction) maxBytes) := none

def Entry.candidate (e : Entry) : Candidate challenge :=
  ⟨wrapped e.construction, e.maxBytes, e.certificate⟩

end WotsLamport.Protected
