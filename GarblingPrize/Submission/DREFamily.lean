import GarblingPrize.Submission.DREKernel

namespace GarblingPrize.Submission.DRE

/-! # Monomial rows and independent DRE families

This file specializes the finite weighted-sum kernel to coefficient rows evaluated
at public basis values, then takes a dependent product over independently owned
row-mask fibers.
-/

section MonomialRow

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The unmasked component at `i` is its coefficient times its public basis value. -/
def monomialUnmasked (coefficients basis : ι → R) : ι → R :=
  fun i => coefficients i * basis i

/-- Evaluation of a coefficient row at fixed public basis values and weights. -/
def rowEvaluation (weights basis coefficients : ι → R) : R :=
  weightedSum weights (monomialUnmasked coefficients basis)

/-- The complete active view of a coefficient row, inherited from the weighted-sum kernel. -/
def monomialCompleteActiveView (weights basis coefficients : ι → R)
    (mask : WeightedZeroMask weights) : ActiveView ι R :=
  completeActiveView weights (monomialUnmasked coefficients basis) mask

/-- Equal row evaluations induce the kernel's explicit equivalence of mask fibers. -/
def rowMaskEquiv (weights basis source target : ι → R)
    (h : rowEvaluation weights basis source = rowEvaluation weights basis target) :
    WeightedZeroMask weights ≃ WeightedZeroMask weights :=
  weightedZeroMaskEquiv weights (monomialUnmasked source basis)
    (monomialUnmasked target basis) h

/-- Forward then reverse row translation is the identity. -/
theorem rowMaskEquiv_source_target_source
    (weights basis source target : ι → R)
    (h : rowEvaluation weights basis source = rowEvaluation weights basis target)
    (mask : WeightedZeroMask weights) :
    rowMaskEquiv weights basis target source h.symm
      (rowMaskEquiv weights basis source target h mask) = mask := by
  exact translateMask_source_target_source weights
    (monomialUnmasked source basis) (monomialUnmasked target basis) h mask

/-- Reverse then forward row translation is the identity. -/
theorem rowMaskEquiv_target_source_target
    (weights basis source target : ι → R)
    (h : rowEvaluation weights basis source = rowEvaluation weights basis target)
    (mask : WeightedZeroMask weights) :
    rowMaskEquiv weights basis source target h
      (rowMaskEquiv weights basis target source h.symm mask) = mask := by
  exact translateMask_target_source_target weights
    (monomialUnmasked source basis) (monomialUnmasked target basis) h mask

/-- Row translation makes every target decoded component equal its source component. -/
theorem monomial_decodedComponents_rowMaskEquiv
    (weights basis source target : ι → R)
    (h : rowEvaluation weights basis source = rowEvaluation weights basis target)
    (mask : WeightedZeroMask weights) :
    decodedComponents weights (monomialUnmasked target basis)
        (rowMaskEquiv weights basis source target h mask) =
      decodedComponents weights (monomialUnmasked source basis) mask := by
  exact decodedComponents_translateMask weights
    (monomialUnmasked source basis) (monomialUnmasked target basis) h mask

/-- Row translation preserves the complete active-view record. -/
theorem monomialCompleteActiveView_rowMaskEquiv
    (weights basis source target : ι → R)
    (h : rowEvaluation weights basis source = rowEvaluation weights basis target)
    (mask : WeightedZeroMask weights) :
    monomialCompleteActiveView weights basis target
        (rowMaskEquiv weights basis source target h mask) =
      monomialCompleteActiveView weights basis source mask := by
  exact completeActiveView_weightedZeroMaskEquiv weights
    (monomialUnmasked source basis) (monomialUnmasked target basis) h mask

end MonomialRow

section IndependentFamily

variable {ρ R : Type*} [Fintype ρ] [CommRing R]
variable (ι : ρ → Type*) [∀ r, Fintype (ι r)]

/-- One independently owned weighted-zero hidden-mask coordinate per row. -/
def FamilyHiddenMasks (weights : ∀ r, ι r → R) : Type _ :=
  ∀ r, WeightedZeroMask (weights r)

/-- The dependent product of complete active views, one for each row. -/
def FamilyActiveViews : Type _ :=
  ∀ r, ActiveView (ι r) R

/-- Pointwise family translation; each row uses only its own mask coordinate. -/
def familyTransform
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r))
    (masks : FamilyHiddenMasks ι weights) : FamilyHiddenMasks ι weights :=
  fun r => rowMaskEquiv (weights r) (basis r) (source r) (target r) (h r) (masks r)

/-- Every transformed coordinate remains in its row's declared weighted-zero fiber. -/
theorem familyTransform_mem
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r))
    (masks : FamilyHiddenMasks ι weights) (r : ρ) :
    weightedSum (weights r) ((familyTransform ι weights basis source target h masks r).1) = 0 := by
  exact (familyTransform ι weights basis source target h masks r).property

/-- Reverse family translation after forward translation is the identity. -/
theorem familyTransform_source_target_source
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r))
    (masks : FamilyHiddenMasks ι weights) :
    familyTransform ι weights basis target source (fun r => (h r).symm)
        (familyTransform ι weights basis source target h masks) = masks := by
  funext r
  exact rowMaskEquiv_source_target_source (weights r) (basis r)
    (source r) (target r) (h r) (masks r)

/-- Forward family translation after reverse translation is the identity. -/
theorem familyTransform_target_source_target
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r))
    (masks : FamilyHiddenMasks ι weights) :
    familyTransform ι weights basis source target h
        (familyTransform ι weights basis target source (fun r => (h r).symm) masks) = masks := by
  funext r
  exact rowMaskEquiv_target_source_target (weights r) (basis r)
    (source r) (target r) (h r) (masks r)

/-- Explicit equivalence between the independent dependent-family hidden states. -/
def familyMaskEquiv
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r)) :
    FamilyHiddenMasks ι weights ≃ FamilyHiddenMasks ι weights where
  toFun := familyTransform ι weights basis source target h
  invFun := familyTransform ι weights basis target source (fun r => (h r).symm)
  left_inv := familyTransform_source_target_source ι weights basis source target h
  right_inv := familyTransform_target_source_target ι weights basis source target h

/-- Applying the inverse family equivalence is exactly the same construction
with source and target coefficient families swapped. -/
theorem familyMaskEquiv_symm_apply_eq_swapped
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r))
    (masks : FamilyHiddenMasks ι weights) :
    (familyMaskEquiv ι weights basis source target h).symm masks =
      familyMaskEquiv ι weights basis target source (fun r => (h r).symm)
        masks := by
  rfl

/-- The complete active view of every row is preserved by family translation. -/
theorem familyCompleteActiveView_row
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r))
    (masks : FamilyHiddenMasks ι weights) (r : ρ) :
    monomialCompleteActiveView (weights r) (basis r) (target r)
        (familyTransform ι weights basis source target h masks r) =
      monomialCompleteActiveView (weights r) (basis r) (source r) (masks r) := by
  exact monomialCompleteActiveView_rowMaskEquiv (weights r) (basis r)
    (source r) (target r) (h r) (masks r)

/-- The entire dependent family active view is preserved as one function. -/
theorem familyCompleteActiveView
    (weights basis source target : ∀ r, ι r → R)
    (h : ∀ r, rowEvaluation (weights r) (basis r) (source r) =
      rowEvaluation (weights r) (basis r) (target r))
    (masks : FamilyHiddenMasks ι weights) :
    (fun r => monomialCompleteActiveView (weights r) (basis r) (target r)
      (familyTransform ι weights basis source target h masks r) : FamilyActiveViews ι) =
    (fun r => monomialCompleteActiveView (weights r) (basis r) (source r) (masks r) :
      FamilyActiveViews ι) := by
  funext r
  exact familyCompleteActiveView_row ι weights basis source target h masks r

end IndependentFamily

end GarblingPrize.Submission.DRE
