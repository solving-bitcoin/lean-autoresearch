import GarblingPrize.Submission.RuntimeG1
import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace GarblingPrize.Submission.CosetCoordinates

/-!
Translate a BN254 point by the non-rational point S=(0,s), where s²=3.
For a finite base-field point (x,y), the translated x-coordinate is

  -2*s*x/(y+s) = 6/x² - (2*y/x²)*s.

Consequently it retains both original coordinates: for u+v*s ≠ 0,
y=-3*v/u and x=u*(y²-3)/6. Infinity is represented by zero. Unlike the
ordinary x-coordinate, this encoding has no sign ambiguity on the coset
S+G1. The imaginary part of a finite point's encoding is nonzero, which
also rules out every distinct-abscissa exception when adding a base-field
input to a translated offset.

These lemmas support an eight-base-field-table candidate. They do not yet
replace the ranked scheme or claim the 4.1 MB target.
-/

open GarblingPrize.Protected
open scoped QuadraticAlgebra

abbrev Word := BN254.Fq
abbrev Affine := RuntimeG1.Affine
abbrev Point := RuntimeG1.Point

instance quadraticIrreducible : Fact (∀ r : Word, r ^ 2 ≠ 3 + 0 * r) :=
  ⟨by intro r; simpa using HomogeneousRCBG1GroupLaw.three_not_square r⟩

abbrev K := QuadraticAlgebra Word 3 0

def C : Word →+* K := algebraMap Word K

def sqrtThree : K := ⟨0, 1⟩

@[simp] theorem C_re (value : Word) : (C value).re = value := rfl
@[simp] theorem C_im (value : Word) : (C value).im = 0 := rfl
@[simp] theorem sqrtThree_re : sqrtThree.re = 0 := rfl
@[simp] theorem sqrtThree_im : sqrtThree.im = 1 := rfl

@[simp] theorem sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  change sqrtThree * sqrtThree = (⟨3, 0⟩ : K)
  ext <;> norm_num [sqrtThree, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul]

theorem affine_x_ne_zero (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) : point.x ≠ 0 := by
  intro hx
  apply HomogeneousRCBG1GroupLaw.three_not_square point.y
  simpa [HomogeneousRCBG1GroupLaw.AffineOnCurve, hx] using hpoint.symm

theorem affine_y_ne_zero (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) : point.y ≠ 0 := by
  intro hy
  apply HomogeneousRCBG1GroupLaw.neg_three_not_cube point.x
  dsimp [HomogeneousRCBG1GroupLaw.AffineOnCurve] at hpoint
  rw [hy] at hpoint
  linear_combination hpoint

/-- Explicit base-field components of x(S+P). -/
def encodeAffine (point : Affine) : K :=
  ⟨6 / point.x ^ 2, -2 * point.y / point.x ^ 2⟩

/-- Explicit base-field components of y(S+P). -/
def shiftedYAffine (point : Affine) : K :=
  ⟨-12 * point.y / point.x ^ 3, 1 + 12 / point.x ^ 3⟩

def encode (point : Point) : K :=
  match point.1 with
  | none => 0
  | some affine => encodeAffine affine

def shiftedY (point : Point) : K :=
  match point.1 with
  | none => sqrtThree
  | some affine => shiftedYAffine affine

theorem C_add_sqrtThree_ne_zero (y : Word) : C y + sqrtThree ≠ 0 := by
  intro h
  have hi := congrArg QuadraticAlgebra.im h
  simpa using hi

theorem encodeAffine_formula (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    encodeAffine point = -2 * sqrtThree * C point.x / (C point.y + sqrtThree) := by
  apply (eq_div_iff (C_add_sqrtThree_ne_zero point.y)).mpr
  have hx := affine_x_ne_zero point hpoint
  dsimp [HomogeneousRCBG1GroupLaw.AffineOnCurve] at hpoint
  ext <;> simp [encodeAffine, sqrtThree, C, QuadraticAlgebra.algebraMap_eq] <;>
    field_simp
  · ring
  · linear_combination 2 * hpoint

theorem shiftedYAffine_formula (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    shiftedYAffine point = sqrtThree * (C point.y - 3 * sqrtThree) /
      (C point.y + sqrtThree) := by
  apply (eq_div_iff (C_add_sqrtThree_ne_zero point.y)).mpr
  have hx := affine_x_ne_zero point hpoint
  dsimp [HomogeneousRCBG1GroupLaw.AffineOnCurve] at hpoint
  ext <;> simp [shiftedYAffine, sqrtThree, C, QuadraticAlgebra.algebraMap_eq] <;>
    field_simp
  · linear_combination 12 * hpoint
  · ring

theorem translated_formula_onCurve {L : Type*} [Field L] (s x y : L)
    (hs : s ^ 2 = 3) (hp : y ^ 2 = x ^ 3 + 3) (hd : y + s ≠ 0) :
    (s * (y - 3 * s) / (y + s)) ^ 2 =
      (-2 * s * x / (y + s)) ^ 3 + 3 := by
  field_simp
  linear_combination -8 * s ^ 3 * hp + (3 * s + y) * (3 * s ^ 2 + y ^ 2) * hs

theorem affine_mapped_onCurve (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    C point.y ^ 2 = C point.x ^ 3 + 3 := by
  have h := congrArg C hpoint.symm
  have hc : C (3 : Word) = (3 : K) := by
    ext <;> norm_num [C, QuadraticAlgebra.algebraMap_eq]
  simpa only [map_pow, map_add, HomogeneousRCBG1GroupLaw.curveB, hc] using h

theorem shiftedAffine_onCurve (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    shiftedYAffine point ^ 2 = encodeAffine point ^ 3 + 3 := by
  rw [shiftedYAffine_formula point hpoint, encodeAffine_formula point hpoint]
  apply translated_formula_onCurve sqrtThree (C point.x) (C point.y) sqrtThree_sq
  · exact affine_mapped_onCurve point hpoint
  · exact C_add_sqrtThree_ne_zero point.y

theorem shifted_onCurve (point : Point) :
    shiftedY point ^ 2 = encode point ^ 3 + 3 := by
  rcases point with ⟨point, hpoint⟩
  cases point with
  | none => simp [shiftedY, encode]
  | some point => exact shiftedAffine_onCurve point hpoint

theorem encodeAffine_re_ne_zero (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    (encodeAffine point).re ≠ 0 := by
  exact div_ne_zero (by decide) (pow_ne_zero _ (affine_x_ne_zero point hpoint))

theorem encodeAffine_im_ne_zero (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    (encodeAffine point).im ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (by decide) (affine_y_ne_zero point hpoint))
    (pow_ne_zero _ (affine_x_ne_zero point hpoint))

def decodeAffine (value : K) : Affine :=
  let y := -3 * value.im / value.re
  ⟨value.re * (y ^ 2 - 3) / 6, y⟩

theorem decodeAffine_encodeAffine (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    decodeAffine (encodeAffine point) = point := by
  have hx := affine_x_ne_zero point hpoint
  have hsix : (6 : Word) ≠ 0 := by decide
  have hy : -3 * (encodeAffine point).im / (encodeAffine point).re = point.y := by
    dsimp [encodeAffine]
    field_simp
    ring
  apply HomogeneousRCBG1GroupLaw.Affine.ext
  · change (encodeAffine point).re *
      ((-3 * (encodeAffine point).im / (encodeAffine point).re) ^ 2 - 3) / 6 = point.x
    rw [hy]
    dsimp [encodeAffine]
    dsimp [HomogeneousRCBG1GroupLaw.AffineOnCurve] at hpoint
    field_simp
    linear_combination -hpoint
  · exact hy

/-- The curve check keeps decoding total on arbitrary artifact values. -/
def decode (value : K) : Option Point :=
  if value = 0 then some RuntimeG1.infinity
  else
    let affine := decodeAffine value
    if hcurve : HomogeneousRCBG1GroupLaw.AffineOnCurve affine then
      some (RuntimeG1.ofAffine affine hcurve)
    else none

@[simp] theorem decode_encode (point : Point) : decode (encode point) = some point := by
  rcases point with ⟨point, hpoint⟩
  cases point with
  | none => rfl
  | some point =>
    change HomogeneousRCBG1GroupLaw.AffineOnCurve point at hpoint
    have hn : encodeAffine point ≠ 0 := by
      intro heq
      exact encodeAffine_re_ne_zero point hpoint (congrArg QuadraticAlgebra.re heq)
    have hd := decodeAffine_encodeAffine point hpoint
    simp only [encode, decode, hn, ↓reduceIte, hd]
    split
    · rfl
    · rename_i h
      exact False.elim (h hpoint)

theorem encode_injective : Function.Injective encode := by
  intro left right heq
  have h := congrArg decode heq
  simpa using h

theorem base_abscissa_ne (offset : Point) (x : Word) (hx : x ≠ 0) :
    C x - encode offset ≠ 0 := by
  rcases offset with ⟨point, hpoint⟩
  cases point with
  | none =>
    intro heq
    apply hx
    simpa [encode] using congrArg QuadraticAlgebra.re heq
  | some point =>
    intro heq
    have hi := congrArg QuadraticAlgebra.im heq
    simp only [QuadraticAlgebra.im_sub, C_im, encode,
      QuadraticAlgebra.im_zero, zero_sub, neg_eq_zero] at hi
    exact encodeAffine_im_ne_zero point hpoint hi

end GarblingPrize.Submission.CosetCoordinates
