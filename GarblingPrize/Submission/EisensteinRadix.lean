import GarblingPrize.Submission.EisensteinKernel

namespace GarblingPrize.Submission.EisensteinRadix

/-! Executable arithmetic for the norm-seven radix `3 + omega`. -/

@[ext] structure Value where
  re : Int
  im : Int
  deriving DecidableEq, Repr

def add (left right : Value) : Value :=
  ⟨left.re + right.re, left.im + right.im⟩

def neg (value : Value) : Value :=
  ⟨-value.re, -value.im⟩

def alphaMul (value : Value) : Value :=
  ⟨3 * value.re - value.im, value.re + 2 * value.im⟩

inductive Digit where
  | zero | one | negOne | omega | negOmega | omegaSq | negOmegaSq
  deriving DecidableEq, Repr

def Digit.value : Digit → Value
  | .zero => ⟨0, 0⟩
  | .one => ⟨1, 0⟩
  | .negOne => ⟨-1, 0⟩
  | .omega => ⟨0, 1⟩
  | .negOmega => ⟨0, -1⟩
  | .omegaSq => ⟨-1, -1⟩
  | .negOmegaSq => ⟨1, 1⟩

/-- The seven units give one representative of every residue modulo
`3 + omega`; in the quotient, `omega = -3`. -/
def select (value : Value) : Digit :=
  match (value.re - 3 * value.im) % 7 with
  | 0 => .zero
  | 1 => .one
  | 2 => .omegaSq
  | 3 => .negOmega
  | 4 => .omega
  | 5 => .negOmegaSq
  | _ => .negOne

def divide (value : Value) : Value :=
  let digit := (select value).value
  ⟨(2 * (value.re - digit.re) + (value.im - digit.im)) / 7,
    (-(value.re - digit.re) + 3 * (value.im - digit.im)) / 7⟩

theorem alphaMul_divide_add_digit (value : Value) :
    add (alphaMul (divide value)) (select value).value = value := by
  have hnonnegative : 0 ≤ (value.re - 3 * value.im) % 7 :=
    Int.emod_nonneg _ (by decide)
  have hless : (value.re - 3 * value.im) % 7 < 7 :=
    Int.emod_lt_of_pos _ (by decide)
  have hdecompose := Int.emod_add_mul_ediv (value.re - 3 * value.im) 7
  interval_cases hresidue : (value.re - 3 * value.im) % 7
  case «0» =>
    have hs : select value = .zero := by simp [select, hresidue]
    apply Value.ext <;>
      simp [divide, hs, Digit.value, alphaMul, add] <;> omega
  case «1» =>
    have hs : select value = .one := by simp [select, hresidue]
    apply Value.ext <;>
      simp [divide, hs, Digit.value, alphaMul, add] <;> omega
  case «2» =>
    have hs : select value = .omegaSq := by simp [select, hresidue]
    apply Value.ext <;>
      simp [divide, hs, Digit.value, alphaMul, add] <;> omega
  case «3» =>
    have hs : select value = .negOmega := by simp [select, hresidue]
    apply Value.ext <;>
      simp [divide, hs, Digit.value, alphaMul, add] <;> omega
  case «4» =>
    have hs : select value = .omega := by simp [select, hresidue]
    apply Value.ext <;>
      simp [divide, hs, Digit.value, alphaMul, add] <;> omega
  case «5» =>
    have hs : select value = .negOmegaSq := by simp [select, hresidue]
    apply Value.ext <;>
      simp [divide, hs, Digit.value, alphaMul, add] <;> omega
  case «6» =>
    have hs : select value = .negOne := by simp [select, hresidue]
    apply Value.ext <;>
      simp [divide, hs, Digit.value, alphaMul, add] <;> omega

def evaluate (value : Value) : EisensteinKernel.ScalarRing :=
  (value.re : EisensteinKernel.ScalarRing) +
    (value.im : EisensteinKernel.ScalarRing) * EisensteinKernel.lambda

theorem evaluate_add (left right : Value) :
    evaluate (add left right) = evaluate left + evaluate right := by
  simp [evaluate, add]
  ring

theorem evaluate_alphaMul (value : Value) :
    evaluate (alphaMul value) =
      (3 + EisensteinKernel.lambda) * evaluate value := by
  simp only [evaluate, alphaMul]
  push_cast
  linear_combination
    -(value.im : EisensteinKernel.ScalarRing) *
      EisensteinKernel.lambda_root

theorem evaluate_recompose_step (value : Value) :
    evaluate value = (3 + EisensteinKernel.lambda) * evaluate (divide value) +
      evaluate (select value).value := by
  rw [← evaluate_alphaMul, ← evaluate_add]
  exact congrArg evaluate (alphaMul_divide_add_digit value).symm

/-! ## Short representative modulo the scalar-order kernel -/

def roundDiv (numerator denominator : Nat) : Nat :=
  (2 * numerator + denominator) / (2 * denominator)

theorem roundDiv_error (numerator denominator : Nat) (hden : 0 < denominator) :
    -(denominator : Int) ≤
        2 * ((numerator : Int) -
          (roundDiv numerator denominator : Int) * denominator) ∧
      2 * ((numerator : Int) -
          (roundDiv numerator denominator : Int) * denominator) <
        denominator := by
  have htwo : 0 < 2 * denominator := by omega
  have hlo := Nat.mul_div_le (2 * numerator + denominator) (2 * denominator)
  have hhi := Nat.lt_mul_div_succ (2 * numerator + denominator) htwo
  have hloI : (2 * denominator : Int) *
      (roundDiv numerator denominator : Int) ≤ 2 * numerator + denominator := by
    exact_mod_cast hlo
  have hhiI : (2 * numerator + denominator : Int) <
      (2 * denominator : Int) * ((roundDiv numerator denominator : Int) + 1) := by
    exact_mod_cast hhi
  ring_nf at hloI hhiI ⊢
  omega

def latticeA : Int := EisensteinKernel.kernelA
def latticeB : Int := EisensteinKernel.kernelB

def babaiC (scalar : Nat) : Int :=
  roundDiv (scalar * (EisensteinKernel.kernelA -
    EisensteinKernel.kernelB)) GarblingPrize.Protected.scalarFieldModulus

def babaiD (scalar : Nat) : Int :=
  -roundDiv (scalar * EisensteinKernel.kernelB)
    GarblingPrize.Protected.scalarFieldModulus

def errorU (scalar : Nat) : Int :=
  scalar * (EisensteinKernel.kernelA - EisensteinKernel.kernelB) -
    babaiC scalar * GarblingPrize.Protected.scalarFieldModulus

def errorV (scalar : Nat) : Int :=
  scalar * EisensteinKernel.kernelB +
    babaiD scalar * GarblingPrize.Protected.scalarFieldModulus

def babai (scalar : Nat) : Value :=
  let c := babaiC scalar
  let d := babaiD scalar
  ⟨scalar - c * latticeA + d * latticeB,
    -c * latticeB - d * (latticeA - latticeB)⟩

def shiftFirst (value : Value) (direction : Int) : Value :=
  ⟨value.re + direction * latticeA,
    value.im + direction * latticeB⟩

def shiftSecond (value : Value) (direction : Int) : Value :=
  ⟨value.re - direction * latticeB,
    value.im + direction * (latticeA - latticeB)⟩

def norm (value : Value) : Int :=
  value.re ^ 2 - value.re * value.im + value.im ^ 2

def innerTwice (left right : Value) : Int :=
  2 * left.re * right.re - left.re * right.im -
    left.im * right.re + 2 * left.im * right.im

theorem norm_nonneg (value : Value) : 0 ≤ norm value := by
  simp only [norm]
  nlinarith [sq_nonneg (2 * value.re - value.im), sq_nonneg value.im]

theorem norm_add (left right : Value) :
    norm (add left right) =
      norm left + innerTwice left right + norm right := by
  simp only [norm, add, innerTwice]
  ring

theorem norm_alphaMul (value : Value) :
    norm (alphaMul value) = 7 * norm value := by
  simp only [norm, alphaMul]
  ring

theorem digit_norm_le_one (digit : Digit) : norm digit.value ≤ 1 := by
  cases digit <;> norm_num [Digit.value, norm]

theorem innerTwice_sq_le (left right : Value) :
    innerTwice left right ^ 2 ≤ 4 * norm left * norm right := by
  simp only [innerTwice, norm]
  nlinarith [sq_nonneg (left.re * right.im - left.im * right.re)]

theorem babai_error_bounds (scalar : Nat) :
    -(GarblingPrize.Protected.scalarFieldModulus : Int) ≤ 2 * errorU scalar ∧
      2 * errorU scalar < GarblingPrize.Protected.scalarFieldModulus ∧
    -(GarblingPrize.Protected.scalarFieldModulus : Int) ≤ 2 * errorV scalar ∧
      2 * errorV scalar < GarblingPrize.Protected.scalarFieldModulus := by
  have hmod : 0 < GarblingPrize.Protected.scalarFieldModulus := by
    norm_num [GarblingPrize.Protected.scalarFieldModulus]
  have hu := roundDiv_error
    (scalar * (EisensteinKernel.kernelA - EisensteinKernel.kernelB))
    GarblingPrize.Protected.scalarFieldModulus hmod
  have hv := roundDiv_error (scalar * EisensteinKernel.kernelB)
    GarblingPrize.Protected.scalarFieldModulus hmod
  simp only [errorU, errorV, babaiC, babaiD]
  constructor
  · exact hu.1
  constructor
  · exact hu.2
  constructor
  · simpa only [Int.natCast_mul, Int.reduceNeg, neg_mul, sub_eq_add_neg] using hv.1
  · simpa only [Int.natCast_mul, Int.reduceNeg, neg_mul, sub_eq_add_neg] using hv.2

private theorem lattice_norm :
    latticeA * latticeA - latticeA * latticeB + latticeB * latticeB =
      (GarblingPrize.Protected.scalarFieldModulus : Int) := by
  norm_num [latticeA, latticeB, EisensteinKernel.kernelA,
    EisensteinKernel.kernelB, GarblingPrize.Protected.scalarFieldModulus]

theorem babai_errorU_coordinates (scalar : Nat) :
    errorU scalar =
      (latticeA - latticeB) * (babai scalar).re +
        latticeB * (babai scalar).im := by
  simp only [errorU, babai, latticeA, latticeB]
  norm_num [EisensteinKernel.kernelA, EisensteinKernel.kernelB,
    GarblingPrize.Protected.scalarFieldModulus]
  ring

theorem babai_errorV_coordinates (scalar : Nat) :
    errorV scalar =
      latticeB * (babai scalar).re - latticeA * (babai scalar).im := by
  simp only [errorV, babai, latticeA, latticeB]
  norm_num [EisensteinKernel.kernelA, EisensteinKernel.kernelB,
    GarblingPrize.Protected.scalarFieldModulus]
  ring

theorem babai_norm_scaled (scalar : Nat) :
    (GarblingPrize.Protected.scalarFieldModulus : Int) * norm (babai scalar) =
      errorU scalar ^ 2 + errorU scalar * errorV scalar + errorV scalar ^ 2 := by
  rw [babai_errorU_coordinates, babai_errorV_coordinates]
  simp only [norm]
  rw [show (GarblingPrize.Protected.scalarFieldModulus : Int) =
    latticeA * latticeA - latticeA * latticeB + latticeB * latticeB by
      exact lattice_norm.symm]
  ring

def errorNorm (u v : Int) : Int := u ^ 2 + u * v + v ^ 2

private theorem error_cover (u v modulus : Int) (hmodulus : 0 ≤ modulus)
    (hu0 : -modulus ≤ 2 * u) (hu1 : 2 * u ≤ modulus)
    (hv0 : -modulus ≤ 2 * v) (hv1 : 2 * v ≤ modulus) :
    3 * errorNorm u v ≤ modulus ^ 2 ∨
      3 * errorNorm (u - modulus) v ≤ modulus ^ 2 ∨
      3 * errorNorm (u + modulus) v ≤ modulus ^ 2 ∨
      3 * errorNorm u (v - modulus) ≤ modulus ^ 2 ∨
      3 * errorNorm u (v + modulus) ≤ modulus ^ 2 := by
  by_cases hu : 0 ≤ u
  · by_cases hv : 0 ≤ v
    · by_cases hq : 3 * errorNorm u v ≤ modulus ^ 2
      · exact Or.inl hq
      · by_cases huv : v ≤ u
        · right; left
          simp only [errorNorm] at hq ⊢
          have ht : modulus < 2 * u + v := by
            by_contra hn
            have hp := mul_nonneg (by omega : 0 ≤ u - v)
              (by omega : 0 ≤ u + 2 * v)
            nlinarith
          have ht0 : 0 ≤ 2 * u + v - modulus := by omega
          have hb0 : 0 ≤ u - v := by omega
          have hp1 := mul_nonneg ht0
            (by omega : 0 ≤ 2 * modulus - 2 * u - v)
          have hp2 := mul_nonneg hb0 (by omega : 0 ≤ modulus - u + v)
          have hp3 := mul_nonneg ht0 hb0
          nlinarith
        · right; right; right; left
          simp only [errorNorm] at hq ⊢
          have ht : modulus < u + 2 * v := by
            by_contra hn
            have hp := mul_nonneg (by omega : 0 ≤ v - u)
              (by omega : 0 ≤ 2 * u + v)
            nlinarith
          have ht0 : 0 ≤ u + 2 * v - modulus := by omega
          have hb0 : 0 ≤ v - u := by omega
          have hp1 := mul_nonneg ht0
            (by omega : 0 ≤ 2 * modulus - u - 2 * v)
          have hp2 := mul_nonneg hb0 (by omega : 0 ≤ modulus - v + u)
          have hp3 := mul_nonneg ht0 hb0
          nlinarith
    · by_cases huv : -v ≤ u
      · left
        simp only [errorNorm]
        nlinarith [mul_nonneg (by omega : 0 ≤ -v)
          (by omega : 0 ≤ u + v), sq_nonneg u]
      · left
        simp only [errorNorm]
        nlinarith [mul_nonneg hu (by omega : 0 ≤ -v - u), sq_nonneg v]
  · by_cases hv : v ≤ 0
    · by_cases hq : 3 * errorNorm u v ≤ modulus ^ 2
      · exact Or.inl hq
      · by_cases huv : u ≤ v
        · right; right; left
          simp only [errorNorm] at hq ⊢
          have ht : -modulus > 2 * u + v := by
            by_contra hn
            have hp := mul_nonneg (by omega : 0 ≤ v - u)
              (by omega : 0 ≤ -u - 2 * v)
            nlinarith
          have ht0 : 0 ≤ -2 * u - v - modulus := by omega
          have hb0 : 0 ≤ v - u := by omega
          have hp1 := mul_nonneg ht0
            (by omega : 0 ≤ 2 * modulus + 2 * u + v)
          have hp2 := mul_nonneg hb0 (by omega : 0 ≤ modulus + u - v)
          have hp3 := mul_nonneg ht0 hb0
          nlinarith
        · right; right; right; right
          simp only [errorNorm] at hq ⊢
          have ht : -modulus > u + 2 * v := by
            by_contra hn
            have hp := mul_nonneg (by omega : 0 ≤ u - v)
              (by omega : 0 ≤ -2 * u - v)
            nlinarith
          have ht0 : 0 ≤ -u - 2 * v - modulus := by omega
          have hb0 : 0 ≤ u - v := by omega
          have hp1 := mul_nonneg ht0
            (by omega : 0 ≤ 2 * modulus + u + 2 * v)
          have hp2 := mul_nonneg hb0 (by omega : 0 ≤ modulus + v - u)
          have hp3 := mul_nonneg ht0 hb0
          nlinarith
    · by_cases huv : v ≤ -u
      · left
        simp only [errorNorm]
        nlinarith [mul_nonneg (by omega : 0 ≤ v)
          (by omega : 0 ≤ -u - v), sq_nonneg u]
      · left
        simp only [errorNorm]
        nlinarith [mul_nonneg (by omega : 0 ≤ -u)
          (by omega : 0 ≤ u + v), sq_nonneg v]

theorem shiftFirst_norm_scaled (scalar : Nat) (direction : Int) :
    (GarblingPrize.Protected.scalarFieldModulus : Int) *
        norm (shiftFirst (babai scalar) direction) =
      errorNorm
        (errorU scalar + direction * GarblingPrize.Protected.scalarFieldModulus)
        (errorV scalar) := by
  rw [babai_errorU_coordinates, babai_errorV_coordinates]
  simp only [shiftFirst, norm, errorNorm]
  rw [show (GarblingPrize.Protected.scalarFieldModulus : Int) =
    latticeA * latticeA - latticeA * latticeB + latticeB * latticeB by
      exact lattice_norm.symm]
  ring

theorem shiftSecond_norm_scaled (scalar : Nat) (direction : Int) :
    (GarblingPrize.Protected.scalarFieldModulus : Int) *
        norm (shiftSecond (babai scalar) direction) =
      errorNorm (errorU scalar)
        (errorV scalar - direction * GarblingPrize.Protected.scalarFieldModulus) := by
  rw [babai_errorU_coordinates, babai_errorV_coordinates]
  simp only [shiftSecond, norm, errorNorm]
  rw [show (GarblingPrize.Protected.scalarFieldModulus : Int) =
    latticeA * latticeA - latticeA * latticeB + latticeB * latticeB by
      exact lattice_norm.symm]
  ring

def better (left right : Value) : Value :=
  if norm left ≤ norm right then left else right

theorem better_norm_le_left (left right : Value) :
    norm (better left right) ≤ norm left := by
  unfold better
  split
  · exact le_rfl
  · omega

theorem better_norm_le_right (left right : Value) :
    norm (better left right) ≤ norm right := by
  unfold better
  split
  · assumption
  · exact le_rfl

/-- Check the Babai cell and its four relevant lattice neighbours. -/
def reduceScalar (scalar : Nat) : Value :=
  let base := babai scalar
  better (shiftSecond base (-1))
    (better (shiftSecond base 1)
      (better (shiftFirst base (-1))
        (better (shiftFirst base 1) base)))

theorem reduceScalar_norm_le_shiftSecond_neg (scalar : Nat) :
    norm (reduceScalar scalar) ≤ norm (shiftSecond (babai scalar) (-1)) := by
  simp only [reduceScalar]
  exact better_norm_le_left _ _

theorem reduceScalar_norm_le_shiftSecond_pos (scalar : Nat) :
    norm (reduceScalar scalar) ≤ norm (shiftSecond (babai scalar) 1) := by
  simp only [reduceScalar]
  exact (better_norm_le_right _ _).trans (better_norm_le_left _ _)

theorem reduceScalar_norm_le_shiftFirst_neg (scalar : Nat) :
    norm (reduceScalar scalar) ≤ norm (shiftFirst (babai scalar) (-1)) := by
  simp only [reduceScalar]
  exact (better_norm_le_right _ _).trans
    ((better_norm_le_right _ _).trans (better_norm_le_left _ _))

theorem reduceScalar_norm_le_shiftFirst_pos (scalar : Nat) :
    norm (reduceScalar scalar) ≤ norm (shiftFirst (babai scalar) 1) := by
  simp only [reduceScalar]
  exact (better_norm_le_right _ _).trans
    ((better_norm_le_right _ _).trans
      ((better_norm_le_right _ _).trans (better_norm_le_left _ _)))

theorem reduceScalar_norm_le_babai (scalar : Nat) :
    norm (reduceScalar scalar) ≤ norm (babai scalar) := by
  simp only [reduceScalar]
  exact (better_norm_le_right _ _).trans
    ((better_norm_le_right _ _).trans
      ((better_norm_le_right _ _).trans
        ((better_norm_le_right _ _).trans (le_refl _))))

private theorem norm_le_third_of_scaled {candidate : Value} {scaled : Int}
    (heq : (GarblingPrize.Protected.scalarFieldModulus : Int) *
      norm candidate = scaled)
    (hscaled : 3 * scaled ≤
      (GarblingPrize.Protected.scalarFieldModulus : Int) ^ 2) :
    3 * norm candidate ≤ GarblingPrize.Protected.scalarFieldModulus := by
  have hmod : (0 : Int) < GarblingPrize.Protected.scalarFieldModulus := by
    norm_num [GarblingPrize.Protected.scalarFieldModulus]
  rw [← heq] at hscaled
  have hproduct :
      (GarblingPrize.Protected.scalarFieldModulus : Int) * (3 * norm candidate) ≤
        (GarblingPrize.Protected.scalarFieldModulus : Int) *
          GarblingPrize.Protected.scalarFieldModulus := by
    nlinarith
  exact (Int.mul_le_mul_left hmod).mp hproduct

/-- Nearest-plane rounding followed by four neighbour checks reaches the
hexagonal covering radius `r / 3`. -/
theorem reduceScalar_norm_bound (scalar : Nat) :
    3 * norm (reduceScalar scalar) ≤
      GarblingPrize.Protected.scalarFieldModulus := by
  have herrors := babai_error_bounds scalar
  have hmodnonneg : (0 : Int) ≤ GarblingPrize.Protected.scalarFieldModulus := by
    norm_num [GarblingPrize.Protected.scalarFieldModulus]
  have hcover := error_cover (errorU scalar) (errorV scalar)
    GarblingPrize.Protected.scalarFieldModulus hmodnonneg
    herrors.1 (by omega) herrors.2.2.1 (by omega)
  rcases hcover with hbase | hfirstNeg | hfirstPos | hsecondPos | hsecondNeg
  · have hcandidate := norm_le_third_of_scaled
      (by simpa only [errorNorm] using babai_norm_scaled scalar) hbase
    nlinarith [reduceScalar_norm_le_babai scalar]
  · have hcandidate := norm_le_third_of_scaled
      (by simpa only [neg_mul, one_mul, sub_eq_add_neg] using
        shiftFirst_norm_scaled scalar (-1)) hfirstNeg
    nlinarith [reduceScalar_norm_le_shiftFirst_neg scalar]
  · have hcandidate := norm_le_third_of_scaled
      (by simpa using shiftFirst_norm_scaled scalar 1) hfirstPos
    nlinarith [reduceScalar_norm_le_shiftFirst_pos scalar]
  · have hcandidate := norm_le_third_of_scaled
      (by simpa using shiftSecond_norm_scaled scalar 1) hsecondPos
    nlinarith [reduceScalar_norm_le_shiftSecond_pos scalar]
  · have hcandidate := norm_le_third_of_scaled
      (by simpa only [neg_mul, one_mul, sub_neg_eq_add] using
        shiftSecond_norm_scaled scalar (-1)) hsecondNeg
    nlinarith [reduceScalar_norm_le_shiftSecond_neg scalar]

private theorem transition_arithmetic (current cross upper next : Int)
    (hcauchy : cross ^ 2 ≤ 28 * current)
    (hvalue : 7 * current + cross ≤ upper)
    (hpositive : upper + 2 ≤ 7 * (next + 1))
    (hboundary : 28 * (next + 1) < (7 * (next + 1) - upper) ^ 2) :
    current ≤ next := by
  by_contra hn
  have hcurrent : next + 1 ≤ current := by omega
  have ha0 : 0 ≤ 7 * current - upper := by omega
  have hcross : cross ≤ -(7 * current - upper) := by omega
  have hleft : 0 ≤ -cross - (7 * current - upper) := by omega
  have hright : 0 ≤ -cross + (7 * current - upper) := by omega
  have hsquare := mul_nonneg hleft hright
  have hfactorRight :
      0 ≤ 49 * (current + (next + 1)) - 14 * upper - 28 := by omega
  have hfactor := mul_nonneg (by omega : 0 ≤ current - (next + 1)) hfactorRight
  have hgrowth : 28 * current < (7 * current - upper) ^ 2 := by
    nlinarith
  nlinarith

/-- A checked numerical transition for one norm-seven digit.  The two side
conditions are integer versions of the sharp Cauchy bound
`(sqrt (7N) - 1)^2`. -/
theorem norm_divide_le (value : Value) (upper next : Int)
    (hupper : norm value ≤ upper)
    (hpositive : upper + 2 ≤ 7 * (next + 1))
    (hboundary : 28 * (next + 1) < (7 * (next + 1) - upper) ^ 2) :
    norm (divide value) ≤ next := by
  let quotient := divide value
  let digit := (select value).value
  let current := norm quotient
  let digitNorm := norm digit
  let cross := innerTwice (alphaMul quotient) digit
  have hcurrent : 0 ≤ current := norm_nonneg quotient
  have hdigit0 : 0 ≤ digitNorm := norm_nonneg digit
  have hdigit1 : digitNorm ≤ 1 := digit_norm_le_one (select value)
  have hproduct : current * digitNorm ≤ current := by
    nlinarith [mul_nonneg hcurrent (by omega : 0 ≤ 1 - digitNorm)]
  have hcauchy0 := innerTwice_sq_le (alphaMul quotient) digit
  rw [norm_alphaMul] at hcauchy0
  have hcauchy : cross ^ 2 ≤ 28 * current := by
    dsimp only [cross, current, digitNorm] at hcauchy0 hproduct ⊢
    nlinarith
  have hrecompose := congrArg norm (alphaMul_divide_add_digit value)
  rw [norm_add, norm_alphaMul] at hrecompose
  have hvalue : 7 * current + cross ≤ upper := by
    dsimp only [current, cross, quotient, digit, digitNorm] at hrecompose ⊢
    nlinarith
  exact transition_arithmetic current cross upper next hcauchy hvalue
    hpositive hboundary

theorem norm_le_one_of_le_two (value : Value) (hbound : norm value ≤ 2) :
    norm value ≤ 1 := by
  rcases value with ⟨re, im⟩
  have hxSq : re ^ 2 ≤ 2 := by
    simp only [norm] at hbound
    nlinarith [sq_nonneg (2 * im - re)]
  have hySq : im ^ 2 ≤ 2 := by
    simp only [norm] at hbound
    nlinarith [sq_nonneg (2 * re - im)]
  have hx0 : -1 ≤ re := by
    by_contra h
    have : re ≤ -2 := by omega
    nlinarith [sq_nonneg (re + 1)]
  have hx1 : re ≤ 1 := by
    by_contra h
    have : 2 ≤ re := by omega
    nlinarith [sq_nonneg (re - 1)]
  have hy0 : -1 ≤ im := by
    by_contra h
    have : im ≤ -2 := by omega
    nlinarith [sq_nonneg (im + 1)]
  have hy1 : im ≤ 1 := by
    by_contra h
    have : 2 ≤ im := by omega
    nlinarith [sq_nonneg (im - 1)]
  interval_cases re <;> interval_cases im
  all_goals norm_num [norm] at hbound
  all_goals norm_num [norm]

theorem divide_eq_zero_of_norm_le_one (value : Value) (hbound : norm value ≤ 1) :
    divide value = ⟨0, 0⟩ := by
  rcases value with ⟨re, im⟩
  have hxSq : re ^ 2 ≤ 1 := by
    simp only [norm] at hbound
    nlinarith [sq_nonneg (2 * im - re)]
  have hySq : im ^ 2 ≤ 1 := by
    simp only [norm] at hbound
    nlinarith [sq_nonneg (2 * re - im)]
  have hx0 : -1 ≤ re := by nlinarith [sq_nonneg (re + 1)]
  have hx1 : re ≤ 1 := by nlinarith [sq_nonneg (re - 1)]
  have hy0 : -1 ≤ im := by nlinarith [sq_nonneg (im + 1)]
  have hy1 : im ≤ 1 := by nlinarith [sq_nonneg (im - 1)]
  interval_cases re <;> interval_cases im
  all_goals norm_num [norm] at hbound
  all_goals norm_num [divide, select, Digit.value]

/-! The sharp integer Cauchy recurrence above is instantiated as a compact
certificate.  Entry 0 is floor(r / 3), and entry 90 is 2. -/
def normBound : Nat → Int
  | 0 => 7296080957279758407415468581752425029516121466805344781232734728858602831872
  | 1 => 1042297279611394058202209797393203575669565095232601592007431788641390376270
  | 2 => 148899611373056294028887113913314796533447764791514899451089485939617308537
  | 3 => 21271373053293756289841016273330685222550378640070829775039065167519407383
  | 4 => 3038767579041965184263002324761526461682079771193847195417715696093196636
  | 5 => 434109654148852169180428903537360923595498858925262027389958777666753461
  | 6 => 62015664878407452740061271933908703559034117770672138461523594873474353
  | 7 => 8859380696915350391437324561986957722441858483218203378421651258946899
  | 8 => 1265625813845050055919617794569565415812917854121844193666488678779496
  | 9 => 180803687692150007988516827795652212423455440626697847818232340624702
  | 10 => 25829098241735715426930975399378891330872542449420222693293793405765
  | 11 => 3689871177390816489561567914196985927905674028795557141106005294567
  | 12 => 527124453912973784223081130599569967101879075934951245358494903625
  | 13 => 75303493416139112031868732942795917024088352728435428815463428195
  | 14 => 10757641916591301718838390420399495121961183098941828124728633228
  | 15 => 1536805988084471674119770060057100365723830099116113331078561762
  | 16 => 219543712583495953445681437151025538565443666489186966840549729
  | 17 => 31363387511927993349383062450150738940076188985617835932758106
  | 18 => 4480483930275427621340437492880277077853242636888169149685573
  | 19 => 640069132896489660191491070412072929797190915680715688501143
  | 20 => 91438447556641380027355867201953288030139711884986896623447
  | 21 => 13062635365234482861050838171794009121185137879015284616052
  | 22 => 1866090766462068980150119738860370413511898625863256738272
  | 23 => 266584395208866997164302819849538136994684564268630466466
  | 24 => 38083485029838142452043259983170423109407029630773996268
  | 25 => 5440497861405448921720465713644683820749847580256622467
  | 26 => 777213980200778417388637959758522684008440330787425810
  | 27 => 111030568600111202484091137360245355589816035643557993
  | 28 => 15861509800015886069155876860952907274243816015515595
  | 29 => 2265929971430840867022268158976839919183237363797741
  | 30 => 323704281632977266717466893454344382942313020645620
  | 31 => 46243468804711038102495275633987404910919115828325
  | 32 => 6606209829244434014642184176356787669171175337140
  | 33 => 943744261320633430663169902409489084047326888013
  | 34 => 134820608760090490094738835048500660441028566281
  | 35 => 19260086965727212870677081343860011066271690672
  | 36 => 2751440995103887552953908415041543193954590013
  | 37 => 393062999300555364707716189057351415929702010
  | 38 => 56151857042936480672536548670045942916701092
  | 39 => 8021693863276640096078790796943639142249627
  | 40 => 1145956266182377156583493616562768540468429
  | 41 => 163708038026053879512233514785692058414802
  | 42 => 23386862575150554216148961683583368365979
  | 43 => 3340980367878650602350688137186927489735
  | 44 => 477282909696950086066612937953061481126
  | 45 => 68183272813850012301472364130541927144
  | 46 => 9740467544835716045426713824455027922
  | 47 => 1391495363547959435952665463916677639
  | 48 => 198785051935422776901699814042041057
  | 49 => 28397864562203253970486594311346999
  | 50 => 4056837794600464901074273358306913
  | 51 => 579548256371495004065842033582374
  | 52 => 82792608053070721744779865956694
  | 53 => 11827515436152962848981223234011
  | 54 => 1689645062307567103887461035767
  | 55 => 241377866043938529087773957791
  | 56 => 34482552291991358813171871855
  | 57 => 4926078898855961457533872893
  | 58 => 703725556979443118513597050
  | 59 => 100532222425642310595110566
  | 60 => 14361746060808909106675111
  | 61 => 2051678008688069783651075
  | 62 => 293096858384419217085158
  | 63 => 41870979769357426499562
  | 64 => 5981568538538096355958
  | 65 => 854509791241825365377
  | 66 => 122072827328612766322
  | 67 => 17438975335815725835
  | 68 => 2491282192023960811
  | 69 => 355897456454388576
  | 70 => 50842493949647344
  | 71 => 7263213485801849
  | 72 => 1037601950892975
  | 73 => 148228859330947
  | 74 => 21175554811543
  | 75 => 3025080573560
  | 76 => 432154864587
  | 77 => 61736597051
  | 78 => 8819584855
  | 79 => 1259967526
  | 80 => 180005502
  | 81 => 25718905
  | 82 => 3675578
  | 83 => 525630
  | 84 => 75297
  | 85 => 10835
  | 86 => 1577
  | 87 => 236
  | 88 => 38
  | 89 => 7
  | 90 => 2
  | _ => 1

set_option maxHeartbeats 2000000 in
private theorem normBound_step (index : Nat) (hindex : index < 90) :
    normBound index + 2 ≤ 7 * (normBound (index + 1) + 1) ∧
      28 * (normBound (index + 1) + 1) <
        (7 * (normBound (index + 1) + 1) - normBound index) ^ 2 := by
  interval_cases index <;> norm_num [normBound]

private theorem rotated_kernel_relation :
    (latticeB : EisensteinKernel.ScalarRing) -
      ((latticeA : EisensteinKernel.ScalarRing) -
        (latticeB : EisensteinKernel.ScalarRing)) *
        EisensteinKernel.lambda = 0 := by
  decide

private theorem int_kernel_relation :
    (latticeA : EisensteinKernel.ScalarRing) +
      (latticeB : EisensteinKernel.ScalarRing) * EisensteinKernel.lambda = 0 := by
  decide

theorem evaluate_shiftFirst (value : Value) (direction : Int) :
    evaluate (shiftFirst value direction) = evaluate value := by
  simp only [evaluate, shiftFirst]
  push_cast
  linear_combination
    (direction : EisensteinKernel.ScalarRing) *
      int_kernel_relation

theorem evaluate_shiftSecond (value : Value) (direction : Int) :
    evaluate (shiftSecond value direction) = evaluate value := by
  simp only [evaluate, shiftSecond]
  push_cast
  linear_combination
    -(direction : EisensteinKernel.ScalarRing) * rotated_kernel_relation

theorem evaluate_better (left right : Value)
    (hleft : evaluate left = target) (hright : evaluate right = target) :
    evaluate (better left right) = target := by
  unfold better
  split <;> assumption

theorem evaluate_babai (scalar : Nat) :
    evaluate (babai scalar) = (scalar : EisensteinKernel.ScalarRing) := by
  simp only [babai, evaluate]
  push_cast
  linear_combination
    -(babaiC scalar : EisensteinKernel.ScalarRing) * int_kernel_relation +
    (babaiD scalar : EisensteinKernel.ScalarRing) * rotated_kernel_relation

theorem evaluate_reduceScalar (scalar : Nat) :
    evaluate (reduceScalar scalar) =
      (scalar : EisensteinKernel.ScalarRing) := by
  unfold reduceScalar
  apply evaluate_better
  · rw [evaluate_shiftSecond]
    exact evaluate_babai scalar
  · apply evaluate_better
    · rw [evaluate_shiftSecond]
      exact evaluate_babai scalar
    · apply evaluate_better
      · rw [evaluate_shiftFirst]
        exact evaluate_babai scalar
      · apply evaluate_better
        · rw [evaluate_shiftFirst]
          exact evaluate_babai scalar
        · exact evaluate_babai scalar

/-! ## Fixed-width little-endian digit stream -/

def digits : Nat → Value → List Digit
  | 0, _ => []
  | count + 1, value => select value :: digits count (divide value)

def residual : Nat → Value → Value
  | 0, value => value
  | count + 1, value => residual count (divide value)

theorem residual_succ (count : Nat) (value : Value) :
    residual (count + 1) value = divide (residual count value) := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih =>
      simp only [residual]
      exact ih (divide value)

theorem residual_norm_le_bound (scalar count : Nat) (hcount : count ≤ 90) :
    norm (residual count (reduceScalar scalar)) ≤ normBound count := by
  induction count with
  | zero =>
      simp only [residual, normBound]
      have h := reduceScalar_norm_bound scalar
      norm_num [GarblingPrize.Protected.scalarFieldModulus] at h ⊢
      omega
  | succ count ih =>
      rw [residual_succ]
      have hindex : count < 90 := by omega
      have hstep := normBound_step count hindex
      exact norm_divide_le _ (normBound count) (normBound (count + 1))
        (ih (by omega)) hstep.1 hstep.2

theorem residual_ninety_one_zero (scalar : Nat) :
    residual 91 (reduceScalar scalar) = ⟨0, 0⟩ := by
  rw [show 91 = 90 + 1 by omega, residual_succ]
  apply divide_eq_zero_of_norm_le_one
  apply norm_le_one_of_le_two
  simpa [normBound] using residual_norm_le_bound scalar 90 (by omega)

def evaluateDigits : List Digit → EisensteinKernel.ScalarRing
  | [] => 0
  | digit :: tail =>
      evaluate digit.value +
        (3 + EisensteinKernel.lambda) * evaluateDigits tail

theorem evaluate_digits_add_residual (count : Nat) (value : Value) :
    evaluate value = evaluateDigits (digits count value) +
      (3 + EisensteinKernel.lambda) ^ count * evaluate (residual count value) := by
  induction count generalizing value with
  | zero => simp [digits, residual, evaluateDigits]
  | succ count ih =>
      rw [evaluate_recompose_step value, ih (divide value)]
      simp only [digits, residual, evaluateDigits, pow_succ]
      ring

theorem evaluateDigits_of_residual_zero (count : Nat) (value : Value)
    (hzero : residual count value = ⟨0, 0⟩) :
    evaluateDigits (digits count value) = evaluate value := by
  have h := evaluate_digits_add_residual count value
  rw [hzero] at h
  simpa [evaluate] using h.symm

/-! ## A 90-place expansion with one bounded wide top digit -/

/-- After the first 89 ordinary unit digits, retain the remaining
Eisenstein value as the most-significant digit.  This is the coefficient of
the 90th map in a mixed-width implementation. -/
def wideTopDigit (scalar : Nat) : Value :=
  residual 89 (reduceScalar scalar)

/-- The terminal wide digit lies in the closed norm-seven hexagon.  There
are only 31 Eisenstein integers in this set, versus another unrestricted
radix step. -/
theorem wideTopDigit_norm_le_seven (scalar : Nat) :
    norm (wideTopDigit scalar) ≤ 7 := by
  simpa [wideTopDigit, normBound] using
    residual_norm_le_bound scalar 89 (by omega)

/-- Exact mixed-width recomposition: 89 seven-way unit digits followed by
one norm-at-most-seven digit already represents the full scalar. -/
theorem evaluate_wide_ninety (scalar : Nat) :
    evaluateDigits (digits 89 (reduceScalar scalar)) +
        (3 + EisensteinKernel.lambda) ^ 89 *
          evaluate (wideTopDigit scalar) =
      (scalar : EisensteinKernel.ScalarRing) := by
  unfold wideTopDigit
  rw [← evaluate_digits_add_residual 89 (reduceScalar scalar)]
  exact evaluate_reduceScalar scalar

/-- Every scalar has an exact fixed-width 91-digit expansion in the seven
unit digits for radix `3 + omega`. -/
theorem evaluateDigits_reduceScalar (scalar : Nat) :
    evaluateDigits (digits 91 (reduceScalar scalar)) =
      (scalar : EisensteinKernel.ScalarRing) := by
  rw [evaluateDigits_of_residual_zero 91 (reduceScalar scalar)
    (residual_ninety_one_zero scalar)]
  exact evaluate_reduceScalar scalar

end GarblingPrize.Submission.EisensteinRadix
