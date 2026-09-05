import Blake3Prize.Protected.Reference

namespace Blake3Prize.Protected

/-- An optional public primitive. This is an ordinary function in correctness
statements; a security profile specifies its law or computational assumptions. -/
abbrev PublicHash := ByteArray → Label
abbrev Randomness (n : Nat) := Vector UInt8 n

/-- A submission owns the construction, evaluator, and complete serialization.
The public hash is available, but using it is not mandatory. The only public
instance data outside the scored bytes are the fixed message and active labels. -/
structure Scheme where
  Artifact : Type
  randomnessBytes : Nat
  garble : PublicHash → Randomness randomnessBytes →
    InputLabelPairs → OutputLabelPairs → Artifact
  encode : Artifact → ByteArray
  decode : ByteArray → Option Artifact
  evaluate : PublicHash → Artifact → Input → ActiveInputLabels → Option ActiveOutputLabels

namespace Scheme

def garbleBytes (s : Scheme) (hash : PublicHash) (coins : Randomness s.randomnessBytes)
    (inputs : InputLabelPairs) (outputs : OutputLabelPairs) : ByteArray :=
  s.encode (s.garble hash coins inputs outputs)

def evaluateBytes (s : Scheme) (hash : PublicHash) (bytes : ByteArray)
    (input : Input) (active : ActiveInputLabels) : Option ActiveOutputLabels :=
  (s.decode bytes).bind fun artifact => s.evaluate hash artifact input active

end Scheme

/-- Correctness is about the serialized transport path actually executed by
CI, for every message, all coins, all distinct caller label pairs, and every
interpretation of the optional public primitive. -/
def Correct (s : Scheme) : Prop :=
  ∀ hash coins inputs outputs input,
    DistinctPairs inputs → DistinctPairs outputs →
    s.evaluateBytes hash (s.garbleBytes hash coins inputs outputs)
      input (activeInput inputs input) = some (activeOutput outputs (reference input))

structure CodecLaws (s : Scheme) : Prop where
  decode_encode : ∀ a, s.decode (s.encode a) = some a
  encode_decode : ∀ bytes a, s.decode bytes = some a → s.encode a = bytes

/-- Every byte of instance-dependent public state must be returned by encode.
Fixed public program code and the fixed active-label channels are not scored. -/
def ArtifactBound (s : Scheme) (maxBytes : Nat) : Prop :=
  ∀ hash coins inputs outputs,
    (s.garbleBytes hash coins inputs outputs).size ≤ maxBytes

end Blake3Prize.Protected
