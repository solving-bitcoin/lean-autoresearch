import Blake3Prize.Submission.RomBytes

namespace Blake3Prize.Submission.RomPacking
open SecretRelease

/-- A fixed-width label read; malformed buffers have a deterministic default. -/
def readLabel (bytes : ByteArray) (index : Nat) : Label :=
  let part := bytes.extract (32*index) (32*index+32)
  if h : part.size = 32 then ⟨part.data,h⟩ else RomBytes.zero 32

theorem packFold_append (acc : Array UInt8) (ls : List Label) :
    ls.foldl (fun acc label => acc ++ label.toArray) acc =
      acc ++ ls.foldl (fun acc label => acc ++ label.toArray) #[] := by
  induction ls generalizing acc with
  | nil => simp
  | cons l ls ih =>
      simp [List.foldl_cons]
      rw [ih (acc ++ l.toArray), ih l.toArray, Array.append_assoc]

theorem pack_cons (l : Label) (ls : List Label) :
    pack (l :: ls) = ByteArray.mk l.toArray ++ pack ls := by
  unfold pack
  simp only [List.foldl_cons]
  have h := packFold_append (l.toArray) ls
  apply ByteArray.ext
  simpa using h

theorem pack_length (ls : List Label) : (pack ls).size = 32 * ls.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      rw [pack_cons, ByteArray.size_append, ih]
      have hl : (ByteArray.mk l.toArray).size = 32 := l.size_toArray
      rw [hl]
      simp [List.length_cons]
      omega

theorem pack_extract_head (l : Label) (ls : List Label) :
    (pack (l :: ls)).extract 0 32 = ByteArray.mk l.toArray := by
  rw [pack_cons]
  have hsz : (ByteArray.mk l.toArray).size = 32 := l.size_toArray
  exact ByteArray.extract_append_eq_left hsz.symm

theorem pack_extract_tail (l : Label) (ls : List Label) (start stop : Nat) :
    (pack (l :: ls)).extract (32 + start) (32 + stop) =
      (pack ls).extract start stop := by
  rw [pack_cons]
  have hsz : (ByteArray.mk l.toArray).size = 32 := l.size_toArray
  have := ByteArray.extract_append_size_add (a := ByteArray.mk l.toArray)
    (b := pack ls) (i := start) (j := stop)
  convert this <;> rw [hsz]

theorem pack_extract_index (ls : List Label) (i : Nat) (hi : i < ls.length) :
    (pack ls).extract (32 * i) (32 * i + 32) =
      ByteArray.mk (ls.get ⟨i, hi⟩).toArray := by
  induction ls generalizing i with
  | nil => cases hi
  | cons l ls ih =>
      cases i with
      | zero => exact pack_extract_head l ls
      | succ i =>
          have hi' : i < ls.length := Nat.lt_of_succ_lt_succ hi
          have htail := pack_extract_tail l ls (32 * i) (32 * i + 32)
          have hih := ih i hi'
          have hex : (pack (l :: ls)).extract (32 + 32 * i) (32 + (32 * i + 32)) =
              ByteArray.mk (ls.get ⟨i, hi'⟩).toArray := htail.trans hih
          convert hex using 2 <;> first | omega | simp

theorem readLabel_pack (labels : List Label) (i : Nat) (hi : i < labels.length) :
    readLabel (pack labels) i = labels.get ⟨i,hi⟩ := by
  unfold readLabel
  have he := pack_extract_index labels i hi
  have hs : ((pack labels).extract (32*i) (32*i+32)).size = 32 := by
    rw [he]
    exact (labels.get ⟨i,hi⟩).size_toArray
  rw [dif_pos hs]
  apply Vector.ext
  intro j hj
  simp [he]

def unpack (n : Nat) (bytes : ByteArray) : Vector Label n :=
  Vector.ofFn fun i => readLabel bytes i.val

theorem unpack_pack (labels : List Label) :
    (unpack labels.length (pack labels)).toList = labels := by
  apply List.ext_get
  · simp [unpack]
  · intro i hi hj
    simp only [List.get_eq_getElem,Vector.getElem_toList,unpack,Vector.getElem_ofFn]
    exact readLabel_pack labels i hj

theorem unpack_pack_of_length (labels : List Label) (h : labels.length = n) :
    (unpack n (pack labels)).toList = labels := by
  subst n
  exact unpack_pack labels

def fixed (labels : List Label) (h : labels.length = n) : Bytes (32*n) :=
  ⟨(pack labels).data,(pack_length labels).trans (congrArg (32*·) h)⟩

theorem fixed_encode (labels : List Label) (h : labels.length = n) :
    RomBytes.encode (fixed labels h) = pack labels := ByteArray.ext rfl

end Blake3Prize.Submission.RomPacking
