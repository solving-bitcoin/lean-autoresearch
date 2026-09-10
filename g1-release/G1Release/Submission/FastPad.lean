import G1Release.Submission.FastGarble

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.FastPad
open SecretRelease G1Release.Protected Randomized

/-- These 254 public suffixes are shared across every map and both branches. -/
def rowBytes : Vector ByteArray 254 :=
  Vector.ofFn fun i => ByteArray.mk (AffineTable.natLE8 i.val)

def pad (hash : Hash) (label purposeBytes : ByteArray) (row : Fin 254) : Label :=
  hash (label ++ purposeBytes ++ rowBytes.get row)

theorem pad_eq (hash : Hash) (label : Label) (purpose : Nat) (row : Fin 254) :
    pad hash ⟨label.toArray⟩ ⟨AffineTable.natLE8 purpose⟩ row =
      AffineTable.pad hash label purpose row.val := by
  apply congrArg hash
  apply ByteArray.ext
  simp only [pad,rowBytes,Vector.get_ofFn,ByteArray.data_append]

def table (hash : Hash) (purpose : Nat) (packed : Fin 254 → Bool → ByteArray)
    (params : AffineTable.Params) (masks : AffineTable.MaskFiber params.constant) : AffineTable.Table :=
  let purposeBytes := ByteArray.mk (AffineTable.natLE8 purpose)
  let rows := Vector.ofFn fun index : Fin 254 =>
    (FastPacking.encrypt (FastGarble.share params (masks.1 index) index false).val (pad hash (packed index false) purposeBytes index),
     FastPacking.encrypt (FastGarble.share params (masks.1 index) index true).val (pad hash (packed index true) purposeBytes index))
  G1Release.Math.Bytes.ofFn fun k =>
    let index : Fin 254 := ⟨k.val/64,by omega⟩
    let bit := decide (32 ≤ k.val%64)
    let j : Fin 32 := ⟨k.val%32,Nat.mod_lt _ (by decide)⟩
    (if bit then (rows.get index).2 else (rows.get index).1).get j

theorem table_eq (hash : Hash) (purpose : Nat) (packed : Fin 254 → Bool → ByteArray)
    (pairs : Fin 254 → Bool → Label) (hp : ∀ i b, packed i b = ByteArray.mk ((pairs i b).toArray))
    (params : AffineTable.Params) (masks : AffineTable.MaskFiber params.constant) :
    table hash purpose packed params masks = FastGarble.table hash purpose pairs params masks := by
  simp only [table,FastGarble.table,FastGarble.ciphertextAt,hp,pad_eq]

def inputIndex (kind : ProjectiveMap.TableKind) (row : Fin 254) : Fin 512 :=
  match kind with
  | .xYY | .xCorrection | .zCorrection => ⟨256+row.val,by omega⟩
  | _ => ⟨row.val,by omega⟩

theorem packed_forKind (keys : Fin 512 → Pair) (packed : Fin 512 → Bool → ByteArray)
    (hp : ∀ i b, packed i b = ByteArray.mk (((keys i).get b).toArray))
    (kind : ProjectiveMap.TableKind) (row : Fin 254) (bit : Bool) :
    packed (inputIndex kind row) bit =
      ByteArray.mk ((ProjectiveMap.pairsFor (Scheme.xPairs keys) (Scheme.yPairs keys) kind row bit).toArray) := by
  cases kind <;> simp only [inputIndex,ProjectiveMap.pairsFor,Scheme.xPairs,Scheme.yPairs,hp]

def encodeMap (hash : Hash) (index : Nat) (packed : Fin 512 → Bool → ByteArray)
    (hidden : ProjectiveMap.Hidden)
    (masks : (kind : ProjectiveMap.TableKind) → AffineTable.MaskFiber (hidden.params kind).constant) : ByteArray :=
  let tables := Vector.ofFn fun i : Fin 11 =>
    let kind := ProjectiveMap.tableKindAt i
    table hash (ProjectiveMap.purpose index kind) (fun row b => packed (inputIndex kind row) b)
      (hidden.params kind) (masks kind)
  G1Release.Math.Bytes.toByteArray (G1Release.Math.Bytes.ofFn fun k : Fin 178816 =>
    let ti : Fin 11 := ⟨k.val/16256,by omega⟩
    let off : Fin 16256 := ⟨k.val%16256,Nat.mod_lt _ (by decide)⟩
    (tables.get ti).get off)

theorem encodeMap_eq (hash : Hash) (index : Nat) (keys : Fin 512 → Pair)
    (packed : Fin 512 → Bool → ByteArray) (hp : ∀ i b, packed i b = ByteArray.mk (((keys i).get b).toArray))
    (hidden : ProjectiveMap.Hidden)
    (masks : (kind : ProjectiveMap.TableKind) → AffineTable.MaskFiber (hidden.params kind).constant) :
    encodeMap hash index packed hidden masks =
      FastGarble.encodeMap hash index (Scheme.xPairs keys) (Scheme.yPairs keys) hidden masks := by
  have h (kind : ProjectiveMap.TableKind) := table_eq hash (ProjectiveMap.purpose index kind)
    (fun row b => packed (inputIndex kind row) b)
    (ProjectiveMap.pairsFor (Scheme.xPairs keys) (Scheme.yPairs keys) kind)
    (packed_forKind keys packed hp kind) (hidden.params kind) (masks kind)
  simp only [encodeMap,FastGarble.encodeMap,h]

def keyBytes (keys : Fin 512 → Pair) : Vector (ByteArray × ByteArray) 512 :=
  Vector.ofFn fun i => (ByteArray.mk (((keys i).get false).toArray), ByteArray.mk (((keys i).get true).toArray))

def packedKeys (values : Vector (ByteArray × ByteArray) 512) (i : Fin 512) (bit : Bool) : ByteArray :=
  if bit then (values.get i).2 else (values.get i).1

theorem packedKeys_eq (keys : Fin 512 → Pair) (i : Fin 512) (bit : Bool) :
    packedKeys (keyBytes keys) i bit = ByteArray.mk (((keys i).get bit).toArray) := by
  cases bit <;> simp only [packedKeys,keyBytes,Vector.get_ofFn] <;> rfl

def mapBytes (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (packed : Fin 512 → Bool → ByteArray) (i : Fin 161) : ByteArray :=
  encodeMap hash i.val packed (mapHidden hidden random.offsets random.scales random.chains i) (random.masks i)

theorem mapBytes_eq (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (packed : Fin 512 → Bool → ByteArray)
    (hp : ∀ i b, packed i b = ByteArray.mk (((keys i).get b).toArray)) (i : Fin 161) :
    mapBytes hash hidden random packed i = FastGarble.mapBytes hash hidden random keys i :=
  encodeMap_eq hash i.val keys packed hp _ _

def garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden) (keys : Fin 512 → Pair) : Scheme.Artifact :=
  let values := keyBytes keys
  let maps := mapBytes hash hidden random (packedKeys values)
  ⟨FastGarble.encodeFrom maps 161 (Nat.le_refl 161),by
    have hm : maps = FastGarble.mapBytes hash hidden random keys :=
      funext fun i => mapBytes_eq hash hidden random keys (packedKeys values) (packedKeys_eq keys) i
    rw [hm]
    exact (FastGarble.garble hash hidden random keys).2⟩

theorem artifact_ext {left right : Scheme.Artifact} (h : left.bytes = right.bytes) : left = right := by
  cases left
  cases right
  cases h
  rfl

theorem garble_eq (hash : Hash) (hidden : Hidden) (random : Randomness hidden) (keys : Fin 512 → Pair) :
    garble hash hidden random keys = FastGarble.garble hash hidden random keys := by
  apply artifact_ext
  change FastGarble.encodeFrom (mapBytes hash hidden random (packedKeys (keyBytes keys))) 161 _ =
    FastGarble.encodeFrom (FastGarble.mapBytes hash hidden random keys) 161 _
  apply congrArg (fun maps : Fin 161 → ByteArray => FastGarble.encodeFrom maps 161 (Nat.le_refl 161))
  funext i
  exact mapBytes_eq hash hidden random keys _ (packedKeys_eq keys) i

end G1Release.Submission.FastPad
