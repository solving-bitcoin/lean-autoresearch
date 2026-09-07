import G1Release.Submission.GLVDigits

namespace G1Release.Submission.GLVDigits
open GarblingPrize.Protected G1Release.Protected
open Scheme (inputG1)

theorem map_get_finRange {α : Type*} (values : List α) (h : values.length = count) :
    (List.finRange count).map (fun i => values.get ⟨i.val, by rw [h]; exact i.isLt⟩) = values := by
  apply List.ext_getElem
  · simp [h]
  · intro i hl hr
    simp

private theorem map_finRange_offsetAt (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden) :
    (List.finRange 91).map (offsetAt offsets) = offsets.values := by
  exact map_get_finRange offsets.values offsets.length_eq

private theorem map_finRange_digitAt (hidden : Hidden) :
    (List.finRange 91).map (digitAt hidden) =
      GLVOffsetFamily.digits hidden := by
  exact map_get_finRange (GLVOffsetFamily.digits hidden)
    (GLVOffsetFamily.digits_length hidden)

private theorem zipWith_map_same {Index Left Right Result : Type*}
    (combine : Left → Right → Result) (left : Index → Left)
    (right : Index → Right) (indices : List Index) :
    List.zipWith combine (indices.map left) (indices.map right) =
      indices.map fun index => combine (left index) (right index) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [ih]

theorem fullMapOutputs (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden) (input : Input) :
    (List.finRange 91).map (fun index =>
        EisensteinFullWidth.mapOutput (offsetAt offsets index)
          (digitAt hidden index) (-inputG1 input)) =
      EisensteinFullWidth.mapOutputs offsets.values
        (GLVOffsetFamily.digits hidden) (-inputG1 input) := by
  unfold EisensteinFullWidth.mapOutputs
  rw [← zipWith_map_same
    (fun offset digit => EisensteinFullWidth.mapOutput offset digit
      (-inputG1 input)) (offsetAt offsets) (digitAt hidden)]
  rw [map_finRange_offsetAt, map_finRange_digitAt]

theorem pointwise_of_finRange_map_eq {Value : Type*}
    (left right : Fin count → Value)
    (equality : (List.finRange count).map left =
      (List.finRange count).map right) (index : Fin count) :
    left index = right index := by
  have atIndex := congrArg (fun values => values[index.val]?) equality
  simpa using atIndex

def targetOffsets (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (offsets : GLVOffsetFamily.Fiber source) : GLVOffsetFamily.Fiber target :=
  GLVOffsetFamily.equiv input source target hequal offsets

theorem mapOutput_preserved (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91) :
    EisensteinFullWidth.mapOutput (offsetAt (targetOffsets input source target
        hequal offsets) index) (digitAt target index) (-inputG1 input) =
      EisensteinFullWidth.mapOutput (offsetAt offsets index)
        (digitAt source index) (-inputG1 input) := by
  have family := GLVOffsetFamily.selectedOutputs_preserved input source target
    hequal offsets
  have indexed :
      (List.finRange 91).map (fun index =>
          EisensteinFullWidth.mapOutput
            (offsetAt (targetOffsets input source target hequal offsets) index)
            (digitAt target index) (-inputG1 input)) =
        (List.finRange 91).map (fun index =>
          EisensteinFullWidth.mapOutput (offsetAt offsets index)
            (digitAt source index) (-inputG1 input)) := by
    rw [fullMapOutputs, fullMapOutputs]
    change EisensteinFullWidth.mapOutputs
        (targetOffsets input source target hequal offsets).values
        (GLVOffsetFamily.digits target) (-inputG1 input) =
      EisensteinFullWidth.mapOutputs offsets.values
        (GLVOffsetFamily.digits source) (-inputG1 input)
    exact family
  exact pointwise_of_finRange_map_eq _ _ indexed index


end G1Release.Submission.GLVDigits
