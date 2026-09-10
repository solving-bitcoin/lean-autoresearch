import G1Release.Submission.Scheme

namespace G1Release.Submission.Scheme
open G1Release.Math
open G1Release.Protected
open G1Release.Submission.BalancedTernary

local instance : AddCommGroup BN254.G1 := inferInstance

theorem map_finRange_offsetAt (hidden : Hidden)
    (offsets : OffsetFamily.Fiber hidden) :
    (List.finRange 161).map (offsetAt offsets) = offsets.values := by
  apply List.ext_getElem
  · simp [offsets.length_eq]
  · intro i hi hi'
    simp [offsetAt, List.get_eq_getElem]

theorem map_finRange_digitAt (hidden : Hidden) :
    (List.finRange 161).map (digitAt hidden) =
      (OffsetFamily.digits hidden).values := by
  apply List.ext_getElem
  · simp [(OffsetFamily.digits hidden).length_eq]
  · intro i hi hi'
    simp [digitAt, Digits.get, List.get_eq_getElem]

theorem recompose_map_add {ι G : Type*} [AddCommGroup G]
    (xs : List ι) (f g : ι → G) :
    TernaryFullWidth.recompose (xs.map fun i => f i + g i) =
      TernaryFullWidth.recompose (xs.map f) +
        TernaryFullWidth.recompose (xs.map g) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [TernaryFullWidth.recompose_cons, ih, nsmul_add]
      abel

theorem recompose_map_zsmul {ι G : Type*} [AddCommGroup G]
    (xs : List ι) (d : ι → Digit) (point : G) :
    TernaryFullWidth.recompose (xs.map fun i => (d i).value • point) =
      TernaryFullWidth.signedRecompositionList (xs.map d) point := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [TernaryFullWidth.recompose_cons,
        TernaryFullWidth.signedRecompositionList,
        TernaryFullWidth.digitTerm, ih]

theorem honest_recompose (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (input : Input) :
    TernaryFullWidth.recompose
        ((List.finRange 161).map fun index =>
          offsetAt offsets index +
            (digitAt hidden index).value • inputG1 input) =
      OffsetFamily.qPoint hidden + hidden.2.val • inputG1 input := by
  rw [recompose_map_add]
  have hoffset :
      TernaryFullWidth.recompose
          ((List.finRange 161).map (offsetAt offsets)) =
        OffsetFamily.qPoint hidden := by
    rw [map_finRange_offsetAt]
    exact offsets.total_eq
  have hdigit :
      TernaryFullWidth.recompose
          ((List.finRange 161).map fun index =>
            (digitAt hidden index).value • inputG1 input) =
        hidden.2.val • inputG1 input := by
    rw [recompose_map_zsmul, map_finRange_digitAt]
    rw [TernaryFullWidth.signedRecompositionList_eq]
    have hdecode := decode_encodeScalar hidden.2
    simpa [OffsetFamily.digits, Digits.decode] using
      congrArg (fun n : ℤ => n • inputG1 input) hdecode
  rw [hoffset, hdigit]

end G1Release.Submission.Scheme
