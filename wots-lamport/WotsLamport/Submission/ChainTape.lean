import WotsLamport.Submission.OraclePrograms

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

abbrev ChainPosition := (j : Fin 67) × Fin (maximum j+1)
abbrev ChainTape := ChainPosition → Label
abbrev ChainEdge := {position : ChainPosition // position.2.val < maximum position.1}

def edgeNext (edge : ChainEdge) : ChainPosition :=
  ⟨edge.val.1, ⟨edge.val.2.val+1, Nat.succ_lt_succ edge.property⟩⟩

def tapeKeys (tape : ChainTape) : Keys := fun j => tape ⟨j, 0⟩
def tapePublicKey (tape : ChainTape) : PublicKey :=
  fun j => tape ⟨j, ⟨maximum j, Nat.lt_succ_self _⟩⟩
def tapeSignature (tape : ChainTape) (m : Message) : Signature :=
  fun j => tape ⟨j, ⟨encodeWord m j, Nat.lt_succ_of_le (encodeWord_le m j)⟩⟩

def actualChainTape (h : Hash) (keys : Keys) : ChainTape :=
  fun position => chain h position.2.val (keys position.1)

def TapeConsistent (h : Hash) (tape : ChainTape) : Prop :=
  ∀ edge : ChainEdge, h (ByteArray.mk (tape edge.val).toArray) = tape (edgeNext edge)

theorem actualChainTape_consistent (h : Hash) (keys : Keys) :
    TapeConsistent h (actualChainTape h keys) := by
  intro edge
  rfl

theorem chain_tape (h : Hash) (tape : ChainTape) (consistent : TapeConsistent h tape)
    (j : Fin 67) (n : Nat) (bound : n ≤ maximum j) :
    chain h n (tapeKeys tape j) = tape ⟨j, ⟨n, Nat.lt_succ_of_le bound⟩⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n < maximum j := by omega
    rw [chain, ih (by omega)]
    exact consistent ⟨⟨j, ⟨n, by omega⟩⟩, hn⟩

theorem publicKey_tape (h : Hash) (tape : ChainTape) (consistent : TapeConsistent h tape) :
    publicKey h (tapeKeys tape) = tapePublicKey tape := by
  funext j
  exact chain_tape h tape consistent j (maximum j) le_rfl

theorem sign_tape (h : Hash) (tape : ChainTape) (consistent : TapeConsistent h tape)
    (m : Message) : sign h (tapeKeys tape) m = tapeSignature tape m := by
  funext j
  exact chain_tape h tape consistent j (encodeWord m j) (encodeWord_le m j)

/-- Program the chain edges of a presampled node tape. The probability that
this programmed oracle has the real distribution is a separate coupling
obligation; this definition alone makes no ROM security claim. -/
noncomputable def programChainOracle (baseline : Hash) (tape : ChainTape) : Hash := by
  classical
  exact fun input => if found : ∃ edge : ChainEdge,
      ByteArray.mk (tape edge.val).toArray = input then
    tape (edgeNext (Classical.choose found)) else baseline input

theorem programChainOracle_off_tape (baseline : Hash) (tape : ChainTape) (input : ByteArray)
    (missing : ∀ edge : ChainEdge, ByteArray.mk (tape edge.val).toArray ≠ input) :
    programChainOracle baseline tape input = baseline input := by
  have hn : ¬∃ edge : ChainEdge, ByteArray.mk (tape edge.val).toArray = input := by
    intro found
    obtain ⟨edge, he⟩ := found
    exact missing edge he
  simp only [programChainOracle, dif_neg hn]

/-- If the sampled chain nodes do not collide, every programmed edge points
to its exact successor, hence signing and public keys agree with the tape. -/
theorem programChainOracle_consistent (baseline : Hash) (tape : ChainTape)
    (distinct : Function.Injective tape) : TapeConsistent (programChainOracle baseline tape) tape := by
  classical
  intro edge
  have found : ∃ other : ChainEdge,
      ByteArray.mk (tape other.val).toArray = ByteArray.mk (tape edge.val).toArray :=
    ⟨edge, rfl⟩
  unfold programChainOracle
  rw [dif_pos found]
  have he := Classical.choose_spec found
  have hv := Vector.toArray_inj.mp (congrArg ByteArray.data he)
  have hc : Classical.choose found = edge := Subtype.ext (distinct hv)
  rw [hc]

end WotsLamport.Submission
