import WotsLamport.Submission.Layout
import WotsLamport.Submission.FieldBridge

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

theorem writeLE_get (length n j : Nat) (hj : j < length) :
    (writeLE length n)[j]! = UInt8.ofNat (n / 256^j) := by
  rw [getElem!_pos (writeLE length n) j (by simpa using hj)]
  simp [writeLE, ByteArray.getElem_eq_getElem_data]

theorem xorBytes_get (a b : ByteArray) (j : Nat) (hj : j < a.size) :
    (xorBytes a b)[j]! = a[j]! ^^^ b[j]! := by
  rw [getElem!_pos (xorBytes a b) j (by simpa using hj)]
  simp [xorBytes, ByteArray.getElem_eq_getElem_data]

/-- Applying the same byte mask twice recovers the original bytes. The mask
need not have a particular length: the executable default reads cancel too. -/
theorem xorBytes_cancel (a b : ByteArray) : xorBytes (xorBytes a b) b = a := by
  apply ByteArray.ext_getElem (by simp)
  intro j hleft hright
  rw [← getElem!_pos (xorBytes (xorBytes a b) b) j hleft,
    ← getElem!_pos a j hright]
  rw [xorBytes_get _ _ j (by simpa using hright), xorBytes_get a b j hright]
  apply UInt8.toBitVec_inj.mp
  simp

theorem readLE_two_lt (bytes : ByteArray) (start : Nat) :
    readLE bytes start 2 < 65536 := by
  have h0 := UInt8.toNat_lt_size bytes[start]!
  have h1 := UInt8.toNat_lt_size bytes[start+1]!
  have h : bytes[start]!.toNat + 256 * bytes[start+1]!.toNat < 65536 := by
    change bytes[start]!.toNat < 256 at h0
    change bytes[start+1]!.toNat < 256 at h1
    omega
  simpa [readLE, List.range_succ] using h

/-- The field-share codec preserves every canonical field value, including
65536; the final two-byte label codec has the stricter 65536 bound. -/
theorem read_writeLE_field (n : Nat) (hn : n < prime) :
    readLE (writeLE 3 n) 0 3 = n := by
  have hn' : n < 65537 := hn
  simp [readLE, List.range_succ, writeLE_get, UInt8.toNat_ofNat']
  omega

theorem append_fold_prefix (parts : List ByteArray) (a b : ByteArray) :
    parts.foldl (fun acc part => acc ++ part) (a ++ b) =
      a ++ parts.foldl (fun acc part => acc ++ part) b := by
  induction parts generalizing b with
  | nil => rfl
  | cons part rest ih =>
    simp only [List.foldl_cons, ByteArray.append_assoc]
    exact ih (b ++ part)

theorem concatenate_cons (part : ByteArray) (rest : List ByteArray) :
    concatenate (part :: rest) = part ++ concatenate rest := by
  simpa only [concatenate, List.foldl_cons, ByteArray.empty_append, ByteArray.append_empty] using
    append_fold_prefix rest part ByteArray.empty

/-- Extracting an indexed fixed-width block recovers exactly that block from
the executable concatenation, including its full contents and order. -/
theorem concatenate_extract (parts : List ByteArray) (width : Nat)
    (sizes : ∀ part ∈ parts, part.size = width) (i : Nat) (hi : i < parts.length) :
    (concatenate parts).extract (i*width) ((i+1)*width) = parts[i] := by
  induction parts generalizing i with
  | nil => simp at hi
  | cons part rest ih =>
    have hp := sizes part (by simp)
    have hr : ∀ p ∈ rest, p.size = width := fun p h => sizes p (by simp [h])
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul, List.getElem_cons_zero, concatenate_cons]
      exact ByteArray.extract_append_eq_left hp.symm
    | succ i =>
      have hs : (i+1)*width = part.size+i*width := by simp [hp, Nat.add_mul, Nat.add_comm]
      have ht : (i+1+1)*width = part.size+(i+1)*width := by
        simp [hp, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      simp only [concatenate_cons, List.getElem_cons_succ]
      rw [hs, ht, ByteArray.extract_append_size_add]
      exact ih hr i (by simpa using hi)

theorem readLE_extract (bytes : ByteArray) (start length : Nat)
    (fits : start+length ≤ bytes.size) :
    readLE (bytes.extract start (start+length)) 0 length = readLE bytes start length := by
  have hs : (bytes.extract start (start+length)).size = length := by
    rw [ByteArray.size_extract]
    omega
  unfold readLE
  apply List.foldr_rel (r := Eq) rfl
  intro j hj a b hab
  have hj' : j < length := List.mem_range.mp hj
  have hg : (bytes.extract start (start+length))[j]! = bytes[start+j]! := by
    rw [getElem!_pos (bytes.extract start (start+length)) j (by rw [hs]; exact hj'),
      ByteArray.getElem_extract,
      getElem!_pos bytes (start+j) (by omega)]
  simpa only [Nat.zero_add, hg, hab]

theorem labelTable_extract (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label)
    (index : Nat) (hi : index < (slots i value).length) :
    (labelTable h coins pk nonce keys i value label).extract (index*48) ((index+1)*48) =
      xorBytes
        (concatenate ((List.range 16).map fun limb =>
          writeLE 3 (evaluatePolynomial (polynomial coins label i.val limb value) (index+1))))
        (mask h pk nonce i.val value (index+1)
          (chain h ((slots i value)[index]).2 (keys ((slots i value)[index]).1))) := by
  unfold labelTable
  rw [concatenate_extract _ 48 (by
    intro part hp
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hp
    rw [xorBytes_size, concatenate_map_size _ _ 3]
    · simp
    · intro p _; exact writeLE_size _ _
  ) index (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
    List.map_map, Function.comp_apply]

/-- Decryption of each stored share is an exact byte identity for every hash,
coin string and key; it does not assume pseudorandom masks. -/
theorem labelTable_decrypt (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label)
    (index : Nat) (hi : index < (slots i value).length) :
    xorBytes ((labelTable h coins pk nonce keys i value label).extract
      (index*48) ((index+1)*48))
      (mask h pk nonce i.val value (index+1)
        (chain h ((slots i value)[index]).2 (keys ((slots i value)[index]).1))) =
      concatenate ((List.range 16).map fun limb =>
        writeLE 3 (evaluatePolynomial (polynomial coins label i.val limb value) (index+1))) := by
  rw [labelTable_extract h coins pk nonce keys i value label index hi, xorBytes_cancel]

/-- Reading one limb from the packed share returns the actual modular Horner
evaluation, with no truncation and no noncanonical field representative. -/
theorem read_share_limb (coefficients : Nat → List Nat) (point limb : Nat)
    (hl : limb < 16) :
    readLE (concatenate ((List.range 16).map fun j =>
      writeLE 3 (evaluatePolynomial (coefficients j) point))) (3*limb) 3 =
      evaluatePolynomial (coefficients limb) point := by
  let parts := (List.range 16).map fun j => writeLE 3 (evaluatePolynomial (coefficients j) point)
  have hs : ∀ part ∈ parts, part.size = 3 := by
    intro part hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    exact writeLE_size _ _
  have hsize : (concatenate parts).size = 48 := by
    exact concatenate_map_size _ _ 3 (by intro j _; exact writeLE_size _ _)
  have he := concatenate_extract parts 3 hs limb (by simpa [parts] using hl)
  simp only [parts, List.getElem_map, List.getElem_range] at he
  have hind : 3*limb = limb*3 := Nat.mul_comm _ _
  have hend : (limb+1)*3 = limb*3+3 := by omega
  change readLE (concatenate parts) (3*limb) 3 = _
  rw [hind, ← readLE_extract _ _ _ (by rw [hsize]; omega), ← hend, he]
  exact read_writeLE_field _ (evaluatePolynomial_lt _ _)

end WotsLamport.Submission
