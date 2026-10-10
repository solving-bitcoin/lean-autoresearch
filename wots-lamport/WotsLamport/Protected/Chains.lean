import WotsLamport.Protected.Encoding

namespace WotsLamport.Protected
open SecretRelease

/-- Independent seeds; the shared game's uniform distribution is on this finite
space, NOT on a single upstream deterministic master seed. -/
abbrev Keys := Fin 67 → Label
abbrev PublicKey := Fin 67 → Label
abbrev Signature := Fin 67 → Label

def chain (h : Hash) : Nat → Label → Label
  | 0, x => x
  | n+1, x => h ⟨(chain h n x).toArray⟩

theorem chain_add (h : Hash) (a b : Nat) (x : Label) :
    chain h (a+b) x = chain h b (chain h a x) := by
  induction b with
  | zero => simp [chain]
  | succ b ih => simp [chain, ih, Nat.add_succ]

def publicKey (h : Hash) (keys : Keys) : PublicKey := fun i => chain h (maximum i) (keys i)
def sign (h : Hash) (keys : Keys) (m : Message) : Signature :=
  fun i => chain h (encodeWord m i) (keys i)

def verifies (h : Hash) (pk : PublicKey) (w : Word) (sig : Signature) : Prop :=
  (∀ i, w i ≤ maximum i) ∧ decodeWord w = some (parseWord w) ∧
    ∀ i, chain h (maximum i - w i) (sig i) = pk i

instance (h : Hash) (pk : PublicKey) (w : Word) (sig : Signature) :
    Decidable (verifies h pk w sig) := by unfold verifies; infer_instance

theorem sign_verifies (h : Hash) (keys : Keys) (m : Message) :
    verifies h (publicKey h keys) (encodeWord m) (sign h keys m) := by
  refine ⟨encodeWord_le m, ?_, ?_⟩
  · simp [decode_encode, parse_encode]
  · intro i
    rw [sign, ← chain_add, Nat.add_sub_of_le (encodeWord_le m i)]
    rfl

def keyCodec : ByteCodec Keys := (Codec.pi 67 (Codec.byteVector 32)).bytes
def signatureBytes (sig : Signature) : ByteArray := keyCodec.encode sig

/-- Anyone can compute every later chain node; an Expand guard cannot erase it. -/
theorem forward_closure (h : Hash) (keys : Keys) (m : Message)
    (i : Fin 67) (d : Nat) (hd : encodeWord m i ≤ d) :
    chain h (d - encodeWord m i) (sign h keys m i) = chain h d (keys i) := by
  rw [sign, ← chain_add, Nat.add_sub_of_le hd]

end WotsLamport.Protected
