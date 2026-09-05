import GarblingPrize.Submission.HomogeneousRCB

namespace GarblingPrize.Submission.RCBMatrixEncoding

/-!
Structural lemmas for reducing the current eleven-table addition encoding.

The RCB output is a cross product of two vectors.  Mixing the two rows by
a matrix of nonzero determinant scales the output by that determinant, so
it preserves the represented point.  This opens a different privacy route:
randomize a basis of the plane perpendicular to the output, rather than
masking three coordinate polynomials independently.

These lemmas are a research foundation, not a smaller ranked candidate.
An encoding must still hide the individual affine openings, prove its exact
oracle-induced distribution, and preserve completeness before replacing the
current construction.  At the current 91 maps, five ordinary affine tables
per map would occupy 7,338,695 bytes, below the 8,200,000-byte goal.  Six
ordinary tables would occupy 8,806,434 bytes and would not suffice.
-/

open HomogeneousRCB

variable {F : Type*} [CommRing F]

def cross (left right : Point F) : Point F where
  x := left.y * right.z - left.z * right.y
  y := left.z * right.x - left.x * right.z
  z := left.x * right.y - left.y * right.x

def dot (left right : Point F) : F :=
  left.x * right.x + left.y * right.y + left.z * right.z

def combine (s t : F) (left right : Point F) : Point F where
  x := s * left.x + t * right.x
  y := s * left.y + t * right.y
  z := s * left.z + t * right.z

/-- The first row of the complete RCB matrix. -/
def firstRow (c : F) (left right : Point F) : Point F where
  x := 3 * left.x * right.x
  y := left.y * right.z + right.y * left.z
  z := c * left.z * right.z - left.y * right.y

/-- The second row of the complete RCB matrix. -/
def secondRow (c : F) (left right : Point F) : Point F where
  x := -(left.y * right.y + c * left.z * right.z)
  y := left.x * right.y + right.x * left.y
  z := -c * (left.x * right.z + right.x * left.z)

/-- This is a polynomial identity over every commutative ring, and therefore
includes the zero selector, arbitrary projective offsets, and infinity. -/
theorem cross_rows (c : F) (left right : Point F) :
    cross (firstRow c left right) (secondRow c left right) =
      formula c left right := by
  apply Point.ext <;> simp [cross, firstRow, secondRow, formula] <;> ring

theorem dot_left_cross (left right : Point F) :
    dot left (cross left right) = 0 := by
  simp [dot, cross]
  ring

theorem dot_right_cross (left right : Point F) :
    dot right (cross left right) = 0 := by
  simp [dot, cross]
  ring

theorem firstRow_annihilates (c : F) (left right : Point F) :
    dot (firstRow c left right) (formula c left right) = 0 := by
  rw [← cross_rows]
  exact dot_left_cross _ _

theorem secondRow_annihilates (c : F) (left right : Point F) :
    dot (secondRow c left right) (formula c left right) = 0 := by
  rw [← cross_rows]
  exact dot_right_cross _ _

/-- A row-basis change multiplies every output coordinate by its determinant. -/
theorem cross_combine (s t u v : F) (left right : Point F) :
    cross (combine s t left right) (combine u v left right) =
      randomize (s * v - t * u) (cross left right) := by
  apply Point.ext <;> simp [cross, combine, randomize] <;> ring

theorem mixed_rows (c s t u v : F) (left right : Point F) :
    cross (combine s t (firstRow c left right) (secondRow c left right))
        (combine u v (firstRow c left right) (secondRow c left right)) =
      randomize (s * v - t * u) (formula c left right) := by
  rw [cross_combine, cross_rows]

/-- A cyclic coordinate permutation preserves the orientation of a cross
product and lets the basis argument select any nonzero minor. -/
def rotate (point : Point F) : Point F := ⟨point.y, point.z, point.x⟩

theorem rotate_cross (left right : Point F) :
    rotate (cross left right) = cross (rotate left) (rotate right) := by
  rfl

theorem rotate_combine (s t : F) (left right : Point F) :
    rotate (combine s t left right) = combine s t (rotate left) (rotate right) := by
  rfl

omit [CommRing F] in
theorem rotate_injective : Function.Injective (rotate : Point F → Point F) := by
  intro left right hequal
  apply Point.ext
  · exact congrArg Point.z hequal
  · exact congrArg Point.x hequal
  · exact congrArg Point.y hequal

/-- Affine specialization of the two matrix rows.  The unmasked matrix is
small, but its individual rows cannot be released without a privacy proof. -/
theorem rows_affine (c a b x y : F) :
    firstRow c ⟨a, b, 1⟩ ⟨x, y, 1⟩ = ⟨3 * a * x, b + y, c - b * y⟩ ∧
      secondRow c ⟨a, b, 1⟩ ⟨x, y, 1⟩ =
        ⟨-(b * y + c), a * y + x * b, -c * (a + x)⟩ := by
  constructor <;> apply Point.ext <;> simp [firstRow, secondRow]

/-- The chord through the input, offset, and negative output supplies a third
linear relation.  Both curve equations are necessary for this relation. -/
theorem chord_annihilates (curveB a b x y : F)
    (hoffset : b ^ 2 = a ^ 3 + curveB)
    (hinput : y ^ 2 = x ^ 3 + curveB) :
    dot (⟨y - b, x - a, b * x - a * y⟩ : Point F)
        (formula (3 * curveB) ⟨a, b, 1⟩ ⟨x, y, 1⟩) = 0 := by
  simp only [dot, formula]
  linear_combination
    -3 * (a ^ 3 * x + a * b ^ 2 + 3 * a * curveB - b ^ 2 * x + curveB * x) * hinput +
      3 * x * (4 * curveB + x ^ 3) * hoffset

/-- The tangent at the negative offset supplies a low-degree denominator for
the translated x-coordinate.  Its common base point must not be ignored. -/
def tangentDenominator (curveB a b x y : F) : F :=
  a ^ 3 - 2 * curveB - 3 * a ^ 2 * x - 2 * b * y

def tangentNumerator (curveB a b x y : F) : F :=
  (a ^ 3 + 4 * curveB) * x + 6 * curveB * a - 2 * a * b * y

theorem tangent_ratio_identity (curveB a b x y : F)
    (hoffset : b ^ 2 = a ^ 3 + curveB)
    (hinput : y ^ 2 = x ^ 3 + curveB) :
    tangentDenominator curveB a b x y *
        (formula (3 * curveB) ⟨a, b, 1⟩ ⟨x, y, 1⟩).x =
      tangentNumerator curveB a b x y *
        (formula (3 * curveB) ⟨a, b, 1⟩ ⟨x, y, 1⟩).z := by
  simp only [tangentDenominator, tangentNumerator, formula]
  linear_combination
    b * (a ^ 4 + 2 * a ^ 3 * x + 2 * a * b ^ 2 + 10 * a * curveB -
      2 * b ^ 2 * x + 2 * curveB * x) * hinput +
    (3 * a ^ 2 * x ^ 2 * y + 2 * a * b * curveB + 2 * a * b * x ^ 3 +
      6 * a * curveB * y - 2 * b * curveB * x - 2 * b * x ^ 4 +
      6 * curveB * x * y) * hoffset

/-- At input twice the offset, the two linear forms can both vanish even
though complete RCB addition returns a finite point.  This exact rational
example rules out treating the low-degree ratio as a complete addition law. -/
theorem tangent_ratio_has_base_point :
    let input : Point ℚ := ⟨-23 / 16, -11 / 64, 1⟩
    input.y ^ 2 = input.x ^ 3 + 3 ∧
      tangentDenominator 3 1 2 input.x input.y = 0 ∧
      tangentNumerator 3 1 2 input.x input.y = 0 ∧
      (formula 9 ⟨1, 2, 1⟩ input).z ≠ 0 := by
  norm_num [tangentDenominator, tangentNumerator, formula]

section BasisTransport

variable {K : Type*} [Field K]

/-- Solve for the coordinates of any vector in the plane perpendicular to a
nonzero cross product, using the Z minor as a pivot. -/
theorem resolve_z (left right point : Point K)
    (hpivot : (cross left right).z ≠ 0)
    (hplane : dot point (cross left right) = 0) :
    combine
        ((point.x * right.y - point.y * right.x) / (cross left right).z)
        ((left.x * point.y - left.y * point.x) / (cross left right).z)
        left right = point := by
  have hminor : left.x * right.y - left.y * right.x ≠ 0 := hpivot
  have hminor' : right.y * left.x - right.x * left.y ≠ 0 := by
    simpa only [mul_comm] using hminor
  apply Point.ext
  · dsimp [combine, cross]
    field_simp [hminor, hminor']
    ring
  · dsimp [combine, cross]
    field_simp [hminor, hminor']
    ring
  · dsimp [combine, cross]
    dsimp [dot, cross] at hplane
    field_simp [hminor, hminor']
    linear_combination -hplane

/-- Equal nonzero oriented area vectors determine row bases differing by an
SL(2) matrix.  This is the pivot case of the prospective matrix privacy
transport; it proves equality of all six row entries after transport. -/
theorem equal_cross_transport_z (left right targetLeft targetRight : Point K)
    (hpivot : (cross left right).z ≠ 0)
    (hequal : cross targetLeft targetRight = cross left right) :
    ∃ s t u v : K, s * v - t * u = 1 ∧
      combine s t left right = targetLeft ∧
      combine u v left right = targetRight := by
  let s := (targetLeft.x * right.y - targetLeft.y * right.x) /
    (cross left right).z
  let t := (left.x * targetLeft.y - left.y * targetLeft.x) /
    (cross left right).z
  let u := (targetRight.x * right.y - targetRight.y * right.x) /
    (cross left right).z
  let v := (left.x * targetRight.y - left.y * targetRight.x) /
    (cross left right).z
  have hleft : combine s t left right = targetLeft := by
    apply resolve_z left right targetLeft hpivot
    rw [← hequal]
    exact dot_left_cross _ _
  have hright : combine u v left right = targetRight := by
    apply resolve_z left right targetRight hpivot
    rw [← hequal]
    exact dot_right_cross _ _
  refine ⟨s, t, u, v, ?_, hleft, hright⟩
  have hscaled := cross_combine s t u v left right
  rw [hleft, hright, hequal] at hscaled
  have hz := congrArg Point.z hscaled
  change (cross left right).z = (s * v - t * u) * (cross left right).z at hz
  apply mul_right_cancel₀ hpivot
  simpa using hz.symm

/-- Every two bases with the same nonzero cross product are related by a
determinant-one change of basis.  The cyclic pivot cases include projective
outputs at infinity, whose Z coordinate is zero. -/
theorem equal_cross_transport (left right targetLeft targetRight : Point K)
    (hnonzero : cross left right ≠ ⟨0, 0, 0⟩)
    (hequal : cross targetLeft targetRight = cross left right) :
    ∃ s t u v : K, s * v - t * u = 1 ∧
      combine s t left right = targetLeft ∧
      combine u v left right = targetRight := by
  by_cases hz : (cross left right).z ≠ 0
  · exact equal_cross_transport_z left right targetLeft targetRight hz hequal
  by_cases hx : (cross left right).x ≠ 0
  · obtain ⟨s, t, u, v, hdet, hleft, hright⟩ :=
      equal_cross_transport_z (rotate left) (rotate right)
        (rotate targetLeft) (rotate targetRight) hx
        (congrArg rotate hequal)
    exact ⟨s, t, u, v, hdet, rotate_injective hleft, rotate_injective hright⟩
  have hy : (cross left right).y ≠ 0 := by
    intro hzero
    apply hnonzero
    apply Point.ext
    · exact not_ne_iff.mp hx
    · exact hzero
    · exact not_ne_iff.mp hz
  obtain ⟨s, t, u, v, hdet, hleft, hright⟩ :=
    equal_cross_transport_z (rotate (rotate left)) (rotate (rotate right))
      (rotate (rotate targetLeft)) (rotate (rotate targetRight)) hy
      (congrArg (rotate ∘ rotate) hequal)
  exact ⟨s, t, u, v, hdet,
    rotate_injective (rotate_injective hleft),
    rotate_injective (rotate_injective hright)⟩

end BasisTransport

theorem five_table_size : 91 * 5 * 127 * 127 = 7338695 := by decide

theorem five_table_size_below_goal : 91 * 5 * 127 * 127 < 8200000 := by decide

theorem six_table_size_above_goal : 8200000 < 91 * 6 * 127 * 127 := by decide

end GarblingPrize.Submission.RCBMatrixEncoding
