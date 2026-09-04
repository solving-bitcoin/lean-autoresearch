import GarblingPrize.Submission.DREFamily

namespace GarblingPrize.Submission.HomogeneousRCB

open scoped BigOperators

variable {F : Type*} [CommRing F]

/-- An ordinary homogeneous coordinate triple. This file proves polynomial
identities only; membership in a concrete curve and nonzero output are
separate refinement obligations. -/
@[ext]
structure Point (F : Type*) where
  x : F
  y : F
  z : F

/-- Public sign of a binary Argo map. -/
inductive Sign where
  | positive
  | negative
  deriving DecidableEq

instance : Fintype Sign where
  elems := {.positive, .negative}
  complete sign := by cases sign <;> simp

/-- Interpret the public sign as `+1` or `-1` in the row field. -/
def Sign.value (sign : Sign) : F :=
  match sign with
  | .positive => 1
  | .negative => -1

/-- Interpret a Boolean selector as ring zero or one. -/
def selectorValue (selector : Bool) : F :=
  if selector then 1 else 0

/-- The ordinary homogeneous Renes--Costello--Batina polynomial tuple with
the curve parameter written as `c = 3b`.

No totality or curve-correctness claim is built into this definition. -/
def formula (c : F) (left right : Point F) : Point F where
  x :=
    (left.x * right.y + right.x * left.y) *
        (left.y * right.y - c * left.z * right.z) -
      c * (left.y * right.z + right.y * left.z) *
        (left.x * right.z + right.x * left.z)
  y :=
    (left.y * right.y + c * left.z * right.z) *
        (left.y * right.y - c * left.z * right.z) +
      3 * c * left.x * right.x *
        (left.x * right.z + right.x * left.z)
  z :=
    (left.y * right.z + right.y * left.z) *
        (left.y * right.y + c * left.z * right.z) +
      3 * left.x * right.x *
        (left.x * right.y + right.x * left.y)

/-- Inline a Boolean selector into the labelled operand. False selects the
canonical homogeneous identity `(0,1,0)`; true selects the signed input. -/
def selectedInput (selector : Bool) (sign : Sign)
    (point : Point F) : Point F :=
  let a := selectorValue (F := F) selector
  let ε := sign.value (F := F)
  {
    x := a * point.x
    y := 1 - a + a * ε * point.y
    z := a * point.z
  }

/-- Sparse selected X row from the returned Problems 02/03 proposal. -/
def selectedX (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) : F :=
  let a := selectorValue (F := F) selector
  let ε := sign.value (F := F)
  (1 - a) * hidden.x * hidden.y +
    a * ε * (hidden.y ^ 2 - c * hidden.z ^ 2) *
      (point.x * point.y) +
    a * hidden.x * hidden.y * point.y ^ 2 -
    2 * a * c * hidden.y * hidden.z * (point.x * point.z) -
    2 * a * ε * c * hidden.x * hidden.z * (point.y * point.z) -
    a * c * hidden.x * hidden.y * point.z ^ 2

/-- Sparse selected Y row from the returned Problems 02/03 proposal. -/
def selectedY (c : F) (hidden point : Point F)
    (selector : Bool) : F :=
  let a := selectorValue (F := F) selector
  (1 - a) * hidden.y ^ 2 +
    3 * a * c * hidden.x * hidden.z * point.x ^ 2 +
    3 * a * c * hidden.x ^ 2 * (point.x * point.z) +
    a * hidden.y ^ 2 * point.y ^ 2 -
    a * c ^ 2 * hidden.z ^ 2 * point.z ^ 2

/-- Sparse selected Z row from the returned Problems 02/03 proposal. -/
def selectedZ (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) : F :=
  let a := selectorValue (F := F) selector
  let ε := sign.value (F := F)
  (1 - a) * hidden.y * hidden.z +
    3 * a * hidden.x * hidden.y * point.x ^ 2 +
    3 * a * ε * hidden.x ^ 2 * (point.x * point.y) +
    a * hidden.y * hidden.z * point.y ^ 2 +
    a * ε * (hidden.y ^ 2 + c * hidden.z ^ 2) *
      (point.y * point.z) +
    a * c * hidden.y * hidden.z * point.z ^ 2

/-- Selector substitution into the RCB tuple gives exactly the three sparse
row polynomials, for both selector values and both public signs. -/
theorem formula_selectedInput
    (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) :
    formula c hidden (selectedInput selector sign point) =
      {
        x := selectedX c hidden point selector sign
        y := selectedY c hidden point selector
        z := selectedZ c hidden point selector sign
      } := by
  cases selector <;> cases sign <;>
    apply Point.ext <;>
    simp [formula, selectedInput, selectedX, selectedY, selectedZ,
      selectorValue, Sign.value] <;>
    ring_nf

/-- The three scalar coordinate rows. -/
inductive Row where
  | x
  | y
  | z
  deriving DecidableEq

instance : Fintype Row where
  elems := {.x, .y, .z}
  complete row := by cases row <;> simp

/-- Minimal sparse incidence width for each G1 row: `(6,5,6)`. -/
def rowWidth : Row → ℕ
  | .x => 6
  | .y => 5
  | .z => 6

/-- Minimal sparse incidence type for each G1 row. -/
abbrev Slot (row : Row) := Fin (rowWidth row)

/-- Public all-one reconstruction weights. -/
def rowWeights : (row : Row) → Slot row → F
  | .x => fun _ => 1
  | .y => fun _ => 1
  | .z => fun _ => 1

/-- Ordered sparse public monomial bases.

The row orders are
`(1,xy,y²,xz,yz,z²)`,
`(1,x²,xz,y²,z²)`, and
`(1,x²,xy,y²,yz,z²)`. -/
def rowBasis (point : Point F) : (row : Row) → Slot row → F
  | .x =>
      ![1, point.x * point.y, point.y ^ 2, point.x * point.z,
        point.y * point.z, point.z ^ 2]
  | .y =>
      ![1, point.x ^ 2, point.x * point.z, point.y ^ 2, point.z ^ 2]
  | .z =>
      ![1, point.x ^ 2, point.x * point.y, point.y ^ 2,
        point.y * point.z, point.z ^ 2]

/-- Ordered hidden coefficient vector for every sparse row. Slots never
disappear when a selector or hidden coefficient happens to be zero. -/
def rowCoefficients (c : F) (hidden : Point F)
    (selector : Bool) (sign : Sign) :
    (row : Row) → Slot row → F :=
  let a := selectorValue (F := F) selector
  let ε := sign.value (F := F)
  fun row =>
    match row with
    | .x =>
        ![
          (1 - a) * hidden.x * hidden.y,
          a * ε * (hidden.y ^ 2 - c * hidden.z ^ 2),
          a * hidden.x * hidden.y,
          -(2 * a * c * hidden.y * hidden.z),
          -(2 * a * ε * c * hidden.x * hidden.z),
          -(a * c * hidden.x * hidden.y)
        ]
    | .y =>
        ![
          (1 - a) * hidden.y ^ 2,
          3 * a * c * hidden.x * hidden.z,
          3 * a * c * hidden.x ^ 2,
          a * hidden.y ^ 2,
          -(a * c ^ 2 * hidden.z ^ 2)
        ]
    | .z =>
        ![
          (1 - a) * hidden.y * hidden.z,
          3 * a * hidden.x * hidden.y,
          3 * a * ε * hidden.x ^ 2,
          a * hidden.y * hidden.z,
          a * ε * (hidden.y ^ 2 + c * hidden.z ^ 2),
          a * c * hidden.y * hidden.z
        ]

/-- Coordinate projection of a homogeneous tuple. -/
def coordinate (point : Point F) : Row → F
  | .x => point.x
  | .y => point.y
  | .z => point.z

/-- The six X incidences reconstruct the selected X polynomial. -/
theorem xRow_evaluation
    (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) .x)
        (rowBasis point .x)
        (rowCoefficients c hidden selector sign .x) =
      selectedX c hidden point selector sign := by
  simp only [GarblingPrize.Submission.DRE.rowEvaluation, GarblingPrize.Submission.DRE.weightedSum,
    GarblingPrize.Submission.DRE.monomialUnmasked, rowWeights, one_mul]
  change
    (∑ index : Fin 6,
      rowCoefficients c hidden selector sign .x index *
        rowBasis point .x index) =
      selectedX c hidden point selector sign
  norm_num [rowCoefficients, rowBasis, selectedX, Fin.sum_univ_succ]
  ring

/-- The five Y incidences reconstruct the selected Y polynomial. -/
theorem yRow_evaluation
    (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) .y)
        (rowBasis point .y)
        (rowCoefficients c hidden selector sign .y) =
      selectedY c hidden point selector := by
  simp only [GarblingPrize.Submission.DRE.rowEvaluation, GarblingPrize.Submission.DRE.weightedSum,
    GarblingPrize.Submission.DRE.monomialUnmasked, rowWeights, one_mul]
  change
    (∑ index : Fin 5,
      rowCoefficients c hidden selector sign .y index *
        rowBasis point .y index) =
      selectedY c hidden point selector
  norm_num [rowCoefficients, rowBasis, selectedY, Fin.sum_univ_succ]
  ring

/-- The six Z incidences reconstruct the selected Z polynomial. -/
theorem zRow_evaluation
    (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) .z)
        (rowBasis point .z)
        (rowCoefficients c hidden selector sign .z) =
      selectedZ c hidden point selector sign := by
  simp only [GarblingPrize.Submission.DRE.rowEvaluation, GarblingPrize.Submission.DRE.weightedSum,
    GarblingPrize.Submission.DRE.monomialUnmasked, rowWeights, one_mul]
  change
    (∑ index : Fin 6,
      rowCoefficients c hidden selector sign .z index *
        rowBasis point .z index) =
      selectedZ c hidden point selector sign
  norm_num [rowCoefficients, rowBasis, selectedZ, Fin.sum_univ_succ]
  ring

/-- Each explicit sparse DRE row reconstructs its corresponding selected
RCB coordinate. -/
theorem rowEvaluation_eq_selected
    (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) (row : Row) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) row)
        (rowBasis point row)
        (rowCoefficients c hidden selector sign row) =
      coordinate
        {
          x := selectedX c hidden point selector sign
          y := selectedY c hidden point selector
          z := selectedZ c hidden point selector sign
        }
        row := by
  cases row with
  | x => exact xRow_evaluation c hidden point selector sign
  | y => exact yRow_evaluation c hidden point selector sign
  | z => exact zRow_evaluation c hidden point selector sign

/-- Consequently every explicit sparse row reconstructs the corresponding
coordinate of the selector-inlined RCB tuple. -/
theorem rowEvaluation_eq_formula
    (c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) (row : Row) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) row)
        (rowBasis point row)
        (rowCoefficients c hidden selector sign row) =
      coordinate (formula c hidden (selectedInput selector sign point)) row := by
  rw [formula_selectedInput]
  exact rowEvaluation_eq_selected c hidden point selector sign row

/-- Homogeneous multiplication of a returned G1 tuple by one base-ring
scalar. Nonzeroness of that scalar is a separate concrete projective-model
condition, not part of this polynomial identity. -/
def randomize (randomizer : F) (point : Point F) : Point F where
  x := randomizer * point.x
  y := randomizer * point.y
  z := randomizer * point.z

/-- Scale every coefficient while retaining the exact same row support. -/
def randomizedRowCoefficients (randomizer c : F) (hidden : Point F)
    (selector : Bool) (sign : Sign) :
    (row : Row) → Slot row → F :=
  fun row index =>
    randomizer * rowCoefficients c hidden selector sign row index

/-- Scalar multiplication distributes over every finite sparse row
reconstruction. -/
theorem randomizedRowEvaluation_eq_mul
    (randomizer c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) (row : Row) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) row)
        (rowBasis point row)
        (randomizedRowCoefficients randomizer c hidden selector sign row) =
      randomizer *
        GarblingPrize.Submission.DRE.rowEvaluation
          (rowWeights (F := F) row)
          (rowBasis point row)
          (rowCoefficients c hidden selector sign row) := by
  cases row <;>
    simp only [GarblingPrize.Submission.DRE.rowEvaluation, GarblingPrize.Submission.DRE.weightedSum,
      GarblingPrize.Submission.DRE.monomialUnmasked, rowWeights, one_mul,
      randomizedRowCoefficients, Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;>
    intro index _ <;>
    ring

/-- The unchanged sparse supports reconstruct the randomized selected tuple,
so G1 homogeneous randomization adds no DRE incidence. -/
theorem randomizedRowEvaluation_eq_selected
    (randomizer c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) (row : Row) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) row)
        (rowBasis point row)
        (randomizedRowCoefficients randomizer c hidden selector sign row) =
      coordinate
        (randomize randomizer
          {
            x := selectedX c hidden point selector sign
            y := selectedY c hidden point selector
            z := selectedZ c hidden point selector sign
          })
        row := by
  rw [randomizedRowEvaluation_eq_mul,
    rowEvaluation_eq_selected c hidden point selector sign row]
  cases row <;> rfl

/-- The same support-preserving statement against the selector-inlined
ordinary homogeneous RCB tuple. -/
theorem randomizedRowEvaluation_eq_formula
    (randomizer c : F) (hidden point : Point F)
    (selector : Bool) (sign : Sign) (row : Row) :
    GarblingPrize.Submission.DRE.rowEvaluation
        (rowWeights (F := F) row)
        (rowBasis point row)
        (randomizedRowCoefficients randomizer c hidden selector sign row) =
      coordinate
        (randomize randomizer
          (formula c hidden (selectedInput selector sign point)))
        row := by
  rw [formula_selectedInput]
  exact randomizedRowEvaluation_eq_selected
    randomizer c hidden point selector sign row

/-- The sparse G1 row language has exactly 17 coefficient-monomial
incidences. -/
theorem incidenceCount :
    ∑ row : Row, Fintype.card (Slot row) = 17 := by
  decide

end GarblingPrize.Submission.HomogeneousRCB
