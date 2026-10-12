import WotsLamport.Protected.Disclosure

namespace WotsLamport.Protected
open SecretRelease

/-- Typed semantic relation for the strict full-width exact-hash profile.
The equivalence with actual Bitcoin Script execution is an OPEN obligation.
No raw-witness security theorem follows merely from this definition. -/
structure SemanticWitness where
  word : Word
  nodes : Signature

def AcceptedWitness (h : Hash) (pk : PublicKey) (w : SemanticWitness) : Prop :=
  verifies h pk w.word w.nodes

def extract (w : SemanticWitness) : Option Message := decodeWord w.word
def canonicalSign (h : Hash) (keys : Keys) (m : Message) : SemanticWitness :=
  ⟨encodeWord m, sign h keys m⟩

theorem extract_sign (h : Hash) (keys : Keys) (m : Message) :
    extract (canonicalSign h keys m) = some m := decode_encode m

/-- A raw stack is kept distinct, even if several byte strings normalize to
the same semantic word. Interpreter equivalence must include flags/ScriptNum. -/
abbrev RawWitness := List ByteArray

end WotsLamport.Protected
