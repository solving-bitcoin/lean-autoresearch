import G1Release.Submission.CoinSampler
import G1Release.Submission.FastPacking

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

/-! Extensional caching for the executable construction. Each ciphertext and
each table is computed once, rather than once for every serialized byte.
Every optimization is equality-preserving, including for arbitrary hashes. -/
namespace G1Release.Submission.FastGarble
open SecretRelease G1Release.Protected Randomized

/-- Powers of two are formed as integers and reduced once. The zero branch
is already the mask, so it needs no field exponentiation or multiplication. -/
def share (params : AffineTable.Params) (mask : Word) (index : Fin 254) (bit : Bool) : Word :=
  if bit then ((2^index.val : Nat) : Word) * params.coefficient + mask else mask

theorem share_eq (params : AffineTable.Params) (mask : Word) (index : Fin 254) (bit : Bool) :
    share params mask index bit = AffineTable.share params mask index bit := by
  cases bit <;> simp [share, AffineTable.share, AffineTable.weight, AffineTable.bitWord]

def ciphertextAt (hash : Hash) (purpose : Nat) (pairs : Fin 254 → Bool → Label)
    (params : AffineTable.Params) (masks : AffineTable.MaskFiber params.constant)
    (index : Fin 254) (bit : Bool) : AffineTable.WordBytes :=
  FastPacking.encrypt (share params (masks.1 index) index bit).val
    (AffineTable.pad hash (pairs index bit) purpose index.val)

theorem ciphertextAt_eq (hash : Hash) (purpose : Nat) (pairs : Fin 254 → Bool → Label)
    (params : AffineTable.Params) (masks : AffineTable.MaskFiber params.constant)
    (index : Fin 254) (bit : Bool) :
    ciphertextAt hash purpose pairs params masks index bit =
      AffineTable.ciphertextAt hash purpose pairs params masks index bit := by
  simp only [ciphertextAt, AffineTable.ciphertextAt, share_eq, FastPacking.encrypt_eq,
    AffineTable.encrypt, AffineTable.encodeWord, AffineTable.xorBytes]

def table (hash : Hash) (purpose : Nat) (pairs : Fin 254 → Bool → Label)
    (params : AffineTable.Params) (masks : AffineTable.MaskFiber params.constant) : AffineTable.Table :=
  let rows := Vector.ofFn fun index : Fin 254 =>
    (ciphertextAt hash purpose pairs params masks index false,
      ciphertextAt hash purpose pairs params masks index true)
  GarblingPrize.Protected.Bytes.ofFn fun k =>
    let index : Fin 254 := ⟨k.val / 64, by omega⟩
    let bit : Bool := decide (32 ≤ k.val % 64)
    let j : Fin 32 := ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
    (if bit then (rows.get index).2 else (rows.get index).1).get j

theorem table_eq (hash : Hash) (purpose : Nat) (pairs : Fin 254 → Bool → Label)
    (params : AffineTable.Params) (masks : AffineTable.MaskFiber params.constant) :
    table hash purpose pairs params masks = AffineTable.garble hash purpose pairs params masks := by
  apply Vector.ext
  intro i hi
  simp only [table, AffineTable.garble, GarblingPrize.Protected.Bytes.ofFn,
    Vector.getElem_ofFn, Vector.get_ofFn, ciphertextAt_eq]
  cases hb : decide (32 ≤ i % 64) <;> simp [hb]

/-- Serialization consumes stored tables directly; an artifact whose only
field is a function can otherwise be eta-expanded by the Lean compiler. -/
def encodeMap (hash : Hash) (index : Nat) (xPairs yPairs : Fin 254 → Bool → Label)
    (hidden : ProjectiveMap.Hidden)
    (masks : (kind : ProjectiveMap.TableKind) → AffineTable.MaskFiber (hidden.params kind).constant) : ByteArray :=
  let tables := Vector.ofFn fun i : Fin 11 =>
    let kind := ProjectiveMap.tableKindAt i
    table hash (ProjectiveMap.purpose index kind) (ProjectiveMap.pairsFor xPairs yPairs kind)
      (hidden.params kind) (masks kind)
  GarblingPrize.Protected.Bytes.toByteArray (GarblingPrize.Protected.Bytes.ofFn fun k : Fin 178816 =>
    let ti : Fin 11 := ⟨k.val / 16256, by omega⟩
    let off : Fin 16256 := ⟨k.val % 16256, Nat.mod_lt _ (by decide)⟩
    (tables.get ti).get off)

theorem encodeMap_eq (hash : Hash) (index : Nat) (xPairs yPairs : Fin 254 → Bool → Label)
    (hidden : ProjectiveMap.Hidden)
    (masks : (kind : ProjectiveMap.TableKind) → AffineTable.MaskFiber (hidden.params kind).constant) :
    encodeMap hash index xPairs yPairs hidden masks =
      ProjectiveMap.encode (ProjectiveMap.garble hash index xPairs yPairs hidden masks) := by
  unfold encodeMap ProjectiveMap.encode ProjectiveMap.encodeVec ProjectiveMap.garble
  simp only [Vector.get_ofFn, table_eq]

def encodeFrom (maps : Fin 161 → ByteArray) : (n : Nat) → n ≤ 161 → ByteArray
  | 0, _ => ByteArray.empty
  | n+1, hn => encodeFrom maps n (Nat.le_of_succ_le hn) ++ maps ⟨n,hn⟩

theorem encodeFrom_eq (maps : Fin 161 → ByteArray) (original : Fin 161 → ProjectiveMap.Artifact)
    (hm : ∀ i, maps i = ProjectiveMap.encode (original i)) (n : Nat) (hn : n ≤ 161) :
    encodeFrom maps n hn = Scheme.encodeFrom original n hn := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodeFrom, Scheme.encodeFrom, ih, hm]

def mapBytes (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (i : Fin 161) : ByteArray :=
  encodeMap hash i.val (Scheme.xPairs keys) (Scheme.yPairs keys)
    (mapHidden hidden random.offsets random.scales random.chains i) (random.masks i)

theorem mapBytes_eq (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (i : Fin 161) :
    mapBytes hash hidden random keys i = ProjectiveMap.encode (Randomized.maps hash hidden random keys i) :=
  encodeMap_eq _ _ _ _ _ _

def garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) : Scheme.Artifact :=
  ⟨encodeFrom (mapBytes hash hidden random keys) 161 (Nat.le_refl 161), by
    rw [encodeFrom_eq _ _ (mapBytes_eq hash hidden random keys)]
    simpa [Scheme.claimedBytes] using
      Scheme.encodeFrom_size (Randomized.maps hash hidden random keys) 161 (Nat.le_refl 161)⟩

theorem garble_eq (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) : garble hash hidden random keys = Randomized.garble hash hidden random keys := by
  unfold garble Randomized.garble
  simp only [encodeFrom_eq _ _ (mapBytes_eq hash hidden random keys)]

end G1Release.Submission.FastGarble
