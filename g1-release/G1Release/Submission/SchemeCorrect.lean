import G1Release.Submission.SchemeAlgebra

namespace G1Release.Submission.Scheme
open SecretRelease
open G1Release.Protected

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

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

theorem readLabel_pack (ls : List Label) (i : Nat)
    (hi : i < ls.length) (hi512 : i < 512) :
    readLabel (pack ls) ⟨i, hi512⟩ = ls.get ⟨i, hi⟩ := by
  unfold readLabel
  have hex := pack_extract_index ls i hi
  have hsz : ((pack ls).extract (32 * i) (32 * i + 32)).size = 32 := by
    rw [hex]; exact (ls.get ⟨i, hi⟩).size_toArray
  rw [dif_pos hsz]
  apply Vector.ext
  intro j hj
  simp [hex]

theorem reveal_eq (hash : Hash) (keys : Fin 512 → Pair) (input : Input) :
    challenge.inputs.reveal hash keys input =
      pack ((List.finRange 512).map fun j =>
        (keys j).get (inputCodec.encode input)[j.val]) := rfl

theorem reveal_size (hash : Hash) (keys : Fin 512 → Pair) (input : Input) :
    (challenge.inputs.reveal hash keys input).size = 16384 := by
  rw [reveal_eq, pack_length]
  simp

theorem reveal_labels (hash : Hash) (keys : Fin 512 → Pair) (input : Input)
    (i : Fin 512) :
    readLabel (challenge.inputs.reveal hash keys input) i =
      (keys i).get (inputCodec.encode input)[i.val] := by
  rw [reveal_eq]
  have := readLabel_pack ((List.finRange 512).map fun j =>
      (keys j).get (inputCodec.encode input)[j.val]) i.val (by simp) i.isLt
  rw [this]
  simp

theorem encodeInput_bit_x (input : Input) (i : Fin 254) :
    (inputCodec.encode input)[i.val] = xBits input i := by
  have hi : i.val < 256 := Nat.lt_trans i.isLt (by decide)
  simp [inputCodec, checkedCodec, encodeInput, xBits, hi]

theorem encodeInput_bit_y (input : Input) (i : Fin 254) :
    (inputCodec.encode input)[256 + i.val] = yBits input i := by
  have hi : ¬ (256 + i.val < 256) := by omega
  simp [inputCodec, checkedCodec, encodeInput, yBits, hi]

theorem evalXLabels_reveal (hash : Hash) (keys : Fin 512 → Pair) (input : Input)
    (i : Fin 254) :
    evalXLabels (challenge.inputs.reveal hash keys input) i =
      xLabels keys input i := by
  unfold evalXLabels xLabels xPairs
  rw [reveal_labels]
  rw [encodeInput_bit_x]

theorem evalYLabels_reveal (hash : Hash) (keys : Fin 512 → Pair) (input : Input)
    (i : Fin 254) :
    evalYLabels (challenge.inputs.reveal hash keys input) i =
      yLabels keys input i := by
  unfold evalYLabels yLabels yPairs
  rw [reveal_labels]
  rw [encodeInput_bit_y]

theorem evalXLabels_reveal_eq (hash : Hash) (keys : Fin 512 → Pair) (input : Input) :
    evalXLabels (challenge.inputs.reveal hash keys input) =
      xLabels keys input := funext (evalXLabels_reveal hash keys input)

theorem evalYLabels_reveal_eq (hash : Hash) (keys : Fin 512 → Pair) (input : Input) :
    evalYLabels (challenge.inputs.reveal hash keys input) =
      yLabels keys input := funext (evalYLabels_reveal hash keys input)

theorem evaluateMap_of_labels (hash : Hash) (hidden : Hidden)
    (keys : Fin 512 → Pair) (input : Input) (index : Fin 161)
    (active : ByteArray)
    (hx : evalXLabels active = xLabels keys input)
    (hy : evalYLabels active = yLabels keys input) :
    evaluateMap hash index (garbleMaps hash hidden keys index) input active =
      match RuntimeG1.normalize
          (rawMap (offsetAt (OffsetFamily.canonical hidden) index)
            (digitAt hidden index) input) with
      | .ok p => some p
      | .error _ => none := by
  have hxlab : xLabels keys input = fun i => xPairs keys i (xBits input i) := rfl
  have hylab : yLabels keys input = fun i => yPairs keys i (yBits input i) := rfl
  have hev :=
    evaluate_garble_mapHidden hash hidden (OffsetFamily.canonical hidden)
      keys input index
  have hfin := congrArg finish hev
  calc
    evaluateMap hash index (garbleMaps hash hidden keys index) input active =
        finish (ProjectiveMap.evaluate hash index.val
          (garbleMaps hash hidden keys index)
          (input.val.1.val : Word) (input.val.2.val : Word)
          (xBits input) (yBits input)
          (evalXLabels active) (evalYLabels active)) := rfl
    _ = finish (ProjectiveMap.evaluate hash index.val
          (ProjectiveMap.garble hash index.val (xPairs keys) (yPairs keys)
            (mapHidden hidden (OffsetFamily.canonical hidden) index)
            (mapMasks hidden (OffsetFamily.canonical hidden) index))
          (AffineTable.decodeBits (xBits input))
          (AffineTable.decodeBits (yBits input))
          (xBits input) (yBits input)
          (fun i => xPairs keys i (xBits input i))
          (fun i => yPairs keys i (yBits input i))) := by
            simp [garbleMaps, hx, hy, hxlab, hylab, decodeBits_xBits,
              decodeBits_yBits]
    _ = finish (some (ProjectiveMap.polynomial
          (mapHidden hidden (OffsetFamily.canonical hidden) index).coefficients
          (AffineTable.decodeBits (xBits input))
          (AffineTable.decodeBits (yBits input)))) := hfin
    _ = finish (some (ProjectiveMap.polynomial
          (mapHidden hidden (OffsetFamily.canonical hidden) index).coefficients
          (input.val.1.val : Word) (input.val.2.val : Word))) := by
            simp [decodeBits_xBits, decodeBits_yBits]
    _ = finish (some (ProjectiveMap.Coordinates.ofHomogeneous
          (rawMap (offsetAt (OffsetFamily.canonical hidden) index)
            (digitAt hidden index) input))) := by
            rw [polynomial_mapHidden]
    _ = match RuntimeG1.normalize
          (rawMap (offsetAt (OffsetFamily.canonical hidden) index)
            (digitAt hidden index) input) with
        | .ok p => some p
        | .error _ => none := finish_ofHomogeneous _

theorem evaluateMap_garbleMaps (hash : Hash) (hidden : Hidden)
    (keys : Fin 512 → Pair) (input : Input) (index : Fin 161) :
    ∃ result : Point,
      evaluateMap hash index (garbleMaps hash hidden keys index) input
          (challenge.inputs.reveal hash keys input) =
        some result ∧
        RuntimeG1.toPoint result =
          offsetAt (OffsetFamily.canonical hidden) index +
            (digitAt hidden index).value • inputG1 input := by
  have hx := evalXLabels_reveal_eq hash keys input
  have hy := evalYLabels_reveal_eq hash keys input
  have hvalid := rawMap_valid (offsetAt (OffsetFamily.canonical hidden) index)
    (digitAt hidden index) input
  obtain ⟨result, hnorm, hpt⟩ :=
    RuntimeG1.normalize_of_valid
      (rawMap (offsetAt (OffsetFamily.canonical hidden) index)
        (digitAt hidden index) input) hvalid
  refine ⟨result, ?eval, ?pt⟩
  · rw [evaluateMap_of_labels hash hidden keys input index _ hx hy, hnorm]
  · rw [hpt, decode_rawMap]

end G1Release.Submission.Scheme
