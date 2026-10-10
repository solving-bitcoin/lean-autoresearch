import WotsLamport.Submission.OracleSupport
import WotsLamport.Submission.DomainSeparation

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected OracleSpec OracleComp

@[simp] theorem run_pure {A : Type} (h : Hash) (a : A) :
    ROM.run h (pure a : Program A) = a := rfl

@[simp] theorem run_bind {A B : Type} (h : Hash) (p : Program A) (next : A → Program B) :
    ROM.run h (p >>= next) = ROM.run h (next (ROM.run h p)) := by
  exact evalWithAnswerFn_bind (QueryImpl.ofFn h) p next

@[simp] theorem run_query (h : Hash) (input : ByteArray) :
    ROM.run h (oracleQuery input : Program Label) = h input := by
  exact evalWithAnswerFn_query (QueryImpl.ofFn h) input

theorem run_listMapM {A B : Type} (h : Hash) (xs : List A) (f : A → Program B) :
    ROM.run h (xs.mapM f) = xs.map (fun x => ROM.run h (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

def sequenceFin {A : Type} : (n : Nat) → (Fin n → Program A) → Program (Fin n → A)
  | 0, _ => pure Fin.elim0
  | n+1, f => do
    let head ← f 0
    let tail ← sequenceFin n (fun i => f i.succ)
    pure (Fin.cases head tail)

theorem run_sequenceFin {A : Type} (h : Hash) (n : Nat) (f : Fin n → Program A) :
    ROM.run h (sequenceFin n f) = fun i => ROM.run h (f i) := by
  induction n generalizing f with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [sequenceFin, run_bind, run_pure, ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def chainProgram : Nat → Label → Program Label
  | 0, seed => pure seed
  | n+1, seed => do
    let node ← chainProgram n seed
    oracleQuery (ByteArray.mk node.toArray)

theorem run_chainProgram (h : Hash) (n : Nat) (seed : Label) :
    ROM.run h (chainProgram n seed) = chain h n seed := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chainProgram, chain, ih]

def publicKeyProgram (keys : Keys) : Program PublicKey :=
  sequenceFin 67 (fun i => chainProgram (maximum i) (keys i))

def signProgram (keys : Keys) (m : Message) : Program Signature :=
  sequenceFin 67 (fun i => chainProgram (encodeWord m i) (keys i))

theorem run_publicKeyProgram (h : Hash) (keys : Keys) :
    ROM.run h (publicKeyProgram keys) = publicKey h keys := by
  simp [publicKeyProgram, run_sequenceFin, run_chainProgram, publicKey]

theorem run_signProgram (h : Hash) (keys : Keys) (m : Message) :
    ROM.run h (signProgram keys m) = sign h keys m := by
  simp [signProgram, run_sequenceFin, run_chainProgram, sign]

def maskProgram (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) : Program ByteArray := do
  let first ← oracleQuery (maskQuery pk nonce wire value point node 0)
  let second ← oracleQuery (maskQuery pk nonce wire value point node 1)
  pure (ByteArray.mk first.toArray ++ (ByteArray.mk second.toArray).extract 0 16)

theorem run_maskProgram (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) :
    ROM.run h (maskProgram pk nonce wire value point node) = mask h pk nonce wire value point node := by
  simp [maskProgram, mask_as_queries]

def labelTableProgram (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) : Program ByteArray := do
  let polys := (List.range 16).map fun limb => polynomial coins label i.val limb value
  let rows ← (slots i value).zipIdx.mapM fun ((j,k), index) => do
    let node ← chainProgram k (keys j)
    let pad ← maskProgram pk nonce i.val value (index+1) node
    let share := concatenate (polys.map fun p => writeLE 3 (evaluatePolynomial p (index+1)))
    pure (xorBytes share pad)
  pure (concatenate rows)

theorem run_labelTableProgram (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) :
    ROM.run h (labelTableProgram coins pk nonce keys i value label) =
      labelTable h coins pk nonce keys i value label := by
  simp only [labelTableProgram, run_bind, run_pure, run_listMapM]
  unfold labelTable
  congr 1
  apply List.map_congr_left
  rintro ⟨⟨j,k⟩,index⟩ _
  simp only [run_bind, run_pure, run_chainProgram, run_maskProgram]

def prepareProgram (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair) : Program ByteArray := do
  let publicKeyValue ← publicKeyProgram keys
  let pk := keyCodec.encode publicKeyValue
  let nonce := coins.extract 0 32
  let commitments ← (List.finRange 256).mapM fun i => do
    let left ← oracleQuery (commitmentQuery pk nonce i.val false ((labels i).get false))
    let right ← oracleQuery (commitmentQuery pk nonce i.val true ((labels i).get true))
    pure (ByteArray.mk left.toArray ++ ByteArray.mk right.toArray)
  let tables ← (List.finRange 256).mapM fun i => do
    let left ← labelTableProgram coins pk nonce keys i false ((labels i).get false)
    let right ← labelTableProgram coins pk nonce keys i true ((labels i).get true)
    pure (left ++ right)
  pure (nonce ++ concatenate commitments ++ concatenate tables)

theorem run_prepareProgram (h : Hash) (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair) :
    ROM.run h (prepareProgram coins keys labels) = prepare h coins keys labels := by
  simp only [prepareProgram, run_bind, run_pure, run_publicKeyProgram, run_listMapM,
    run_query, run_labelTableProgram, prepare, commitment_as_query]

/-- Reification exposes the actual honest oracle calls to query accounting.
It is an equality for every oracle, not an assumed random-oracle reduction. -/
def wrappedPrepareProgram (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair) :
    Program ByteArray := do
  let publicKeyValue ← publicKeyProgram keys
  let body ← prepareProgram coins keys labels
  pure (keyCodec.encode publicKeyValue ++ body)

theorem run_wrappedPrepareProgram (h : Hash) (coins : Bytes randomnessBytes)
    (keys : Keys) (labels : Fin 256 → Pair) :
    ROM.run h (wrappedPrepareProgram (ByteArray.mk coins.toArray) keys labels) =
      (wrapped construction).garbleBytes h coins () keys labels := by
  simp only [wrappedPrepareProgram, run_bind, run_pure, run_publicKeyProgram, run_prepareProgram]
  rfl

end WotsLamport.Submission
