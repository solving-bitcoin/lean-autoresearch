import GarblingPrize.Submission.HintAffineTablePrivacy

namespace GarblingPrize.Submission.FourAffineQuotient

/-!
A quadratic-in-x, linear-in-y numerator divided by the square of an affine
x denominator admits four affine openings over any field. Two independent
additive masks hide its Horner stages, and a nonzero multiplicative mask
randomizes the denominator. A triangular equivalence identifies the entire
state with the denominator and the first two openings. Equal quotient
outputs then force the remaining opening to agree.

Applied over the quadratic extension in CosetCoordinates, four extension
openings cost eight base-field affine tables. The equal-output bijection is
exact; it uses no statistical approximation or cryptographic assumption.
-/

variable {F : Type*} [Field F]

@[ext] structure Base (F : Type*) where
  x2 : F
  x1 : F
  y1 : F
  constant : F
  denominatorX : F
  denominatorConstant : F

def numerator (base : Base F) (x y : F) : F :=
  base.x2 * x ^ 2 + base.x1 * x + base.y1 * y + base.constant

def denominator (base : Base F) (x : F) : F :=
  base.denominatorX * x + base.denominatorConstant

def value (base : Base F) (x y : F) : F :=
  numerator base x y / denominator base x ^ 2

abbrev State (F : Type*) [Field F] := Fˣ × (F × F)

@[ext] structure Opened (F : Type*) where
  quadratic : F
  linear : F
  y : F
  denominator : F

def opened (base : Base F) (state : State F) (x y : F) : Opened F :=
  let r := (state.1 : F)
  { quadratic := r ^ 2 * base.x2 * x + state.2.1
    linear := (r ^ 2 * base.x1 - state.2.1) * x + state.2.2
    y := r ^ 2 * base.y1 * y + r ^ 2 * base.constant - state.2.2
    denominator := r * base.denominatorX * x + r * base.denominatorConstant }

def reconstruct (values : Opened F) (x : F) : F :=
  (values.quadratic * x + values.linear + values.y) / values.denominator ^ 2

theorem opened_numerator (base : Base F) (state : State F) (x y : F) :
    (opened base state x y).quadratic * x + (opened base state x y).linear +
      (opened base state x y).y = (state.1 : F) ^ 2 * numerator base x y := by
  simp only [opened, numerator]
  ring

theorem opened_denominator (base : Base F) (state : State F) (x y : F) :
    (opened base state x y).denominator = (state.1 : F) * denominator base x := by
  simp only [opened, denominator]
  ring

theorem opened_denominator_ne_zero (base : Base F) (state : State F) (x y : F)
    (hd : denominator base x ≠ 0) : (opened base state x y).denominator ≠ 0 := by
  rw [opened_denominator]
  exact mul_ne_zero (Units.ne_zero _) hd

theorem reconstruct_opened (base : Base F) (state : State F) (x y : F)
    (hd : denominator base x ≠ 0) :
    reconstruct (opened base state x y) x = value base x y := by
  unfold reconstruct
  rw [opened_numerator, opened_denominator]
  unfold value
  field_simp

/-- The first two openings form a triangular change of the two additive masks. -/
def maskEquiv (base : Base F) (r x : F) : (F × F) ≃ (F × F) where
  toFun masks := (r ^ 2 * base.x2 * x + masks.1,
    (r ^ 2 * base.x1 - masks.1) * x + masks.2)
  invFun values := (values.1 - r ^ 2 * base.x2 * x,
    values.2 - (r ^ 2 * base.x1 - (values.1 - r ^ 2 * base.x2 * x)) * x)
  left_inv := by rintro ⟨m, n⟩; apply Prod.ext <;> dsimp <;> ring
  right_inv := by rintro ⟨u, v⟩; apply Prod.ext <;> dsimp <;> ring

/-- Coordinates for the state fiber: the nonzero denominator and two openings. -/
def pivotEquiv (base : Base F) (x : F) (hd : denominator base x ≠ 0) :
    State F ≃ State F :=
  (Equiv.prodCongrRight (fun r : Fˣ => maskEquiv base (r : F) x)).trans
    (Equiv.prodCongr (Equiv.mulRight (Units.mk0 (denominator base x) hd)) (Equiv.refl _))

theorem pivotEquiv_apply (base : Base F) (x : F) (hd : denominator base x ≠ 0)
    (state : State F) :
    pivotEquiv base x hd state =
      (state.1 * Units.mk0 (denominator base x) hd,
        ((state.1 : F) ^ 2 * base.x2 * x + state.2.1,
          ((state.1 : F) ^ 2 * base.x1 - state.2.1) * x + state.2.2)) := rfl

def stateEquiv (source target : Base F) (x : F)
    (hs : denominator source x ≠ 0) (ht : denominator target x ≠ 0) :
    State F ≃ State F :=
  (pivotEquiv source x hs).trans (pivotEquiv target x ht).symm

theorem pivot_stateEquiv (source target : Base F) (x : F)
    (hs : denominator source x ≠ 0) (ht : denominator target x ≠ 0)
    (state : State F) :
    pivotEquiv target x ht (stateEquiv source target x hs ht state) =
      pivotEquiv source x hs state := by
  exact (pivotEquiv target x ht).apply_symm_apply _

/-- Equal quotient outputs preserve all four selected openings after transport. -/
theorem opened_stateEquiv (source target : Base F) (x y : F)
    (hs : denominator source x ≠ 0) (ht : denominator target x ≠ 0)
    (hequal : value source x y = value target x y) (state : State F) :
    opened target (stateEquiv source target x hs ht state) x y =
      opened source state x y := by
  let transported := stateEquiv source target x hs ht state
  have hp := pivot_stateEquiv source target x hs ht state
  rw [pivotEquiv_apply, pivotEquiv_apply] at hp
  have hq : (opened target transported x y).quadratic =
      (opened source state x y).quadratic := congrArg (fun v => v.2.1) hp
  have hl : (opened target transported x y).linear =
      (opened source state x y).linear := congrArg (fun v => v.2.2) hp
  have hd : (opened target transported x y).denominator =
      (opened source state x y).denominator := by
    rw [opened_denominator, opened_denominator]
    exact congrArg (fun v : State F => (v.1 : F)) hp
  have ho : reconstruct (opened target transported x y) x =
      reconstruct (opened source state x y) x := by
    rw [reconstruct_opened _ _ _ _ ht, reconstruct_opened _ _ _ _ hs, hequal]
  have hn := opened_denominator_ne_zero source state x y hs
  apply Opened.ext
  · exact hq
  · exact hl
  · dsimp [reconstruct] at ho
    rw [hq, hl, hd] at ho
    field_simp at ho
    linear_combination ho
  · exact hd

theorem stateEquiv_preserves_uniform [Finite F]
    [MeasurableSpace (State F)] [DiscreteMeasurableSpace (State F)]
    (source target : Base F) (x : F)
    (hs : denominator source x ≠ 0) (ht : denominator target x ≠ 0) :
    MeasureTheory.MeasurePreserving (stateEquiv source target x hs ht)
      (ProbabilityTheory.uniformOn Set.univ) (ProbabilityTheory.uniformOn Set.univ) := by
  exact GarblingPrize.Protected.measurePreserving_uniformOfFiniteEquiv _

end GarblingPrize.Submission.FourAffineQuotient
