import GarblingPrize.Submission.CosetGroupLaw

namespace GarblingPrize.Submission.CosetAffineMap

/-!
The translated GLV map needs a quadratic x numerator, a linear y term,
and an affine x denominator. FourAffineQuotient encodes it with four K
openings, hence eight Fp affine tables. Zero digits use a constant numerator
and denominator one; nonzero digits substitute (k*x,e*y), k³=e²=1.

This is an algebraic candidate foundation, not a replacement ValidCandidate.
At 91 maps its eight-table budget is 5,940,480 bytes, still above 4.1 MB.
-/

open GarblingPrize.Protected
open CosetCoordinates FourAffineQuotient

def base (offset : Point) (selected : Bool) (scale sign : Word) : Base K :=
  if selected then
    { x2 := encode offset * C scale ^ 2
      x1 := encode offset ^ 2 * C scale
      y1 := -2 * shiftedY offset * C sign
      constant := 6
      denominatorX := C scale
      denominatorConstant := -encode offset }
  else
    { x2 := 0, x1 := 0, y1 := 0, constant := encode offset
      denominatorX := 0, denominatorConstant := 1 }

def transformed (scale sign : Word) (input : Affine) : Affine :=
  ⟨scale * input.x, sign * input.y⟩

theorem transformed_onCurve (scale sign : Word) (input : Affine)
    (hscale : scale ^ 3 = 1) (hsign : sign ^ 2 = 1)
    (hinput : HomogeneousRCBG1GroupLaw.AffineOnCurve input) :
    HomogeneousRCBG1GroupLaw.AffineOnCurve (transformed scale sign input) := by
  change (scale * input.x) ^ 3 + 3 = (sign * input.y) ^ 2
  rw [mul_pow, mul_pow, hscale, hsign, one_mul, one_mul]
  exact hinput

theorem denominator_ne_zero (offset : Point) (selected : Bool) (scale sign : Word)
    (input : Affine) (hscale : scale ^ 3 = 1)
    (hinput : HomogeneousRCBG1GroupLaw.AffineOnCurve input) :
    denominator (base offset selected scale sign) (C input.x) ≠ 0 := by
  cases selected with
  | false => simp [base, denominator]
  | true =>
    have hk : scale ≠ 0 := by intro h; simp [h] at hscale
    have hd := base_abscissa_ne offset (scale * input.x)
      (mul_ne_zero hk (affine_x_ne_zero input hinput))
    simpa [base, denominator, map_mul, sub_eq_add_neg] using hd

@[simp] theorem value_base_false (offset : Point) (scale sign x y : Word) :
    value (base offset false scale sign) (C x) (C y) = encode offset := by
  simp [value, numerator, denominator, base]

theorem value_base_true (offset result : Point) (scale sign : Word) (input : Affine)
    (hscale : scale ^ 3 = 1) (hsign : sign ^ 2 = 1)
    (hinput : HomogeneousRCBG1GroupLaw.AffineOnCurve input)
    (hsum : RuntimeG1.toPoint result = RuntimeG1.toPoint offset +
      RuntimeG1.toPoint (RuntimeG1.ofAffine (transformed scale sign input)
        (transformed_onCurve scale sign input hscale hsign hinput))) :
    value (base offset true scale sign) (C input.x) (C input.y) = encode result := by
  rw [← CosetGroupLaw.quotient_encodes_sum offset result
    (transformed scale sign input) (transformed_onCurve scale sign input hscale hsign hinput) hsum]
  simp only [value, numerator, denominator, base, ↓reduceIte, transformed, map_mul]
  ring

theorem decode_opened_true (offset result : Point) (scale sign : Word) (input : Affine)
    (hscale : scale ^ 3 = 1) (hsign : sign ^ 2 = 1)
    (hinput : HomogeneousRCBG1GroupLaw.AffineOnCurve input)
    (hsum : RuntimeG1.toPoint result = RuntimeG1.toPoint offset +
      RuntimeG1.toPoint (RuntimeG1.ofAffine (transformed scale sign input)
        (transformed_onCurve scale sign input hscale hsign hinput))) (state : State K) :
    decode (reconstruct (opened (base offset true scale sign) state
      (C input.x) (C input.y)) (C input.x)) = some result := by
  rw [reconstruct_opened _ _ _ _ (denominator_ne_zero offset true scale sign input hscale hinput),
    value_base_true offset result scale sign input hscale hsign hinput hsum, decode_encode]

theorem decode_opened_false (offset : Point) (scale sign : Word) (input : Affine)
    (state : State K) :
    decode (reconstruct (opened (base offset false scale sign) state
      (C input.x) (C input.y)) (C input.x)) = some offset := by
  rw [reconstruct_opened _ _ _ _ (by simp [denominator, base]),
    value_base_false, decode_encode]

theorem eight_table_budget : 91 * 8 * HintAffineTable.tableByteCount = 5940480 := by decide

theorem eight_table_above_goal : 4100000 < 91 * 8 * HintAffineTable.tableByteCount := by decide

end GarblingPrize.Submission.CosetAffineMap
