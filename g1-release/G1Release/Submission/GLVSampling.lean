import G1Release.Submission.GLVOffsetFamily
import G1Release.Submission.SamplingEquivalences

namespace G1Release.Submission.GLVSampling
open GarblingPrize.Protected
abbrev Hidden := G1Release.Protected.Private
def offsetAlpha (point : BN254.G1) : BN254.G1 :=
  3 • point + G1Endomorphism.phi point

theorem offsetAlpha_eq (point : BN254.G1) :
    offsetAlpha point = EisensteinFullWidth.alphaPoint point :=
  (EisensteinFullWidth.alphaPoint_eq_three_add_phi point).symm

/-- Horner recomposition used to solve the leading offset from 90 free offsets. -/
def offsetRecompose : List BN254.G1 → BN254.G1
  | [] => 0
  | head :: tail => head + offsetAlpha (offsetRecompose tail)

theorem offsetRecompose_eq (points : List BN254.G1) :
    offsetRecompose points = EisensteinFullWidth.recompose points := by
  induction points with
  | nil => rfl
  | cons head tail ih =>
      simp only [offsetRecompose, EisensteinFullWidth.recompose_cons, ih,
        offsetAlpha_eq]

abbrev OffsetTail := { values : List GLVOffsetFamily.Point // values.length = 90 }

def offsetTailEquiv : (Fin 90 → GLVOffsetFamily.Point) ≃ OffsetTail where
  toFun values := ⟨List.ofFn values, List.length_ofFn⟩
  invFun values := fun index => values.1.get ⟨index.val, by
    rw [values.2]
    exact index.isLt⟩
  left_inv values := by
    funext index
    change (List.ofFn values).get _ = values index
    rw [List.get_ofFn]
    congr
  right_inv values := by
    apply Subtype.ext
    apply List.ext_get
    · rw [List.length_ofFn, values.2]
    · intro index hleft hright
      rw [List.get_ofFn]
      congr

def offsetsFromTail (hidden : Hidden) (tail : OffsetTail) :
    GLVOffsetFamily.Fiber hidden :=
  let values := tail.1
  { values := (GLVOffsetFamily.qPoint hidden -
        offsetAlpha (offsetRecompose values)) :: values
    length_eq := by rw [List.length_cons, tail.2]
    total_eq := by
      change (GLVOffsetFamily.qPoint hidden -
        offsetAlpha (offsetRecompose values)) +
          EisensteinFullWidth.alphaPoint
            (EisensteinFullWidth.recompose values) = GLVOffsetFamily.qPoint hidden
      rw [offsetRecompose_eq, offsetAlpha_eq]
      abel }


def tailFromOffsets {hidden : Hidden} (offsets : GLVOffsetFamily.Fiber hidden) :
    OffsetTail :=
  ⟨offsets.values.tail, by rw [List.length_tail, offsets.length_eq]⟩

@[simp] theorem tailFromOffsets_offsetsFromTail (hidden : Hidden)
    (tail : OffsetTail) :
    tailFromOffsets (offsetsFromTail hidden tail) = tail := by
  apply Subtype.ext
  rfl

theorem offsetsFromTail_tailFromOffsets (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden) :
    offsetsFromTail hidden (tailFromOffsets offsets) = offsets := by
  apply GLVOffsetFamily.Fiber.ext
  change (GLVOffsetFamily.qPoint hidden -
        offsetAlpha (offsetRecompose offsets.values.tail)) ::
      offsets.values.tail = offsets.values
  cases hvalues : offsets.values with
  | nil =>
      have hlength := offsets.length_eq
      rw [hvalues] at hlength
      simp at hlength
  | cons head tail =>
      have htotal := offsets.total_eq
      rw [hvalues] at htotal
      simp only [EisensteinFullWidth.offsetTotal,
        EisensteinFullWidth.recompose_cons] at htotal
      simp only [hvalues, List.tail_cons]
      congr 1
      change GLVOffsetFamily.qPoint hidden -
          offsetAlpha (offsetRecompose tail) = head
      rw [offsetRecompose_eq, offsetAlpha_eq, ← htotal]
      abel

noncomputable def offsetsEquiv (hidden : Hidden) :
    OffsetTail ≃ GLVOffsetFamily.Fiber hidden where
  toFun := offsetsFromTail hidden
  invFun := tailFromOffsets
  left_inv := tailFromOffsets_offsetsFromTail hidden
  right_inv := offsetsFromTail_tailFromOffsets hidden


instance (hidden : Hidden) : Finite (GLVOffsetFamily.Fiber hidden) :=
  ((offsetTailEquiv.trans (offsetsEquiv hidden)).finite_iff).mp inferInstance
instance (hidden : Hidden) : MeasurableSpace (GLVOffsetFamily.Fiber hidden) := ⊤
instance (hidden : Hidden) : DiscreteMeasurableSpace (GLVOffsetFamily.Fiber hidden) where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top

noncomputable def offsetSampleEquiv (hidden : Hidden) :
    (Fin 90 → Fin scalarFieldModulus) ≃ GLVOffsetFamily.Fiber hidden :=
  ((Equiv.piCongrRight fun _ => Randomized.generatorEquiv).trans
    offsetTailEquiv).trans (offsetsEquiv hidden)

end G1Release.Submission.GLVSampling
