import GarblingPrize.Submission.EisensteinRadix

namespace GarblingPrize.Submission.EisensteinWideTop

open GarblingPrize.Protected
open GarblingPrize.Submission.EisensteinRadix

/-!
# A hexagon-reduced 90-place Eisenstein expansion

The nearest-plane proof already places the scalar representative in a disk
covering the Eisenstein fundamental hexagon.  For the mixed-width 90-place
codec it is useful to choose the representative in the hexagon itself.  The
four corner corrections below are kernel vectors, so they preserve the scalar
while giving the three exact Voronoi inequalities used by the terminal-digit
bound.
-/

def modulus : Int := GarblingPrize.Protected.scalarFieldModulus

def coordU (value : Value) : Int :=
  (latticeA - latticeB) * value.re + latticeB * value.im

def coordV (value : Value) : Int :=
  latticeB * value.re - latticeA * value.im

def hexReduceScalar (scalar : Nat) : Value :=
  let base := babai scalar
  let u := errorU scalar
  let v := errorV scalar
  if modulus < 2 * u + v ∨ modulus < u + 2 * v then
    if v ≤ u then shiftFirst base (-1) else shiftSecond base 1
  else if 2 * u + v < -modulus ∨ u + 2 * v < -modulus then
    if u ≤ v then shiftFirst base 1 else shiftSecond base (-1)
  else
    base

theorem coordU_babai (scalar : Nat) :
    coordU (babai scalar) = errorU scalar := by
  exact (babai_errorU_coordinates scalar).symm

theorem coordV_babai (scalar : Nat) :
    coordV (babai scalar) = errorV scalar := by
  exact (babai_errorV_coordinates scalar).symm

theorem coordU_shiftFirst (value : Value) (direction : Int) :
    coordU (shiftFirst value direction) =
      coordU value + direction * modulus := by
  simp only [coordU, shiftFirst, modulus, latticeA, latticeB]
  norm_num [EisensteinKernel.kernelA, EisensteinKernel.kernelB,
    GarblingPrize.Protected.scalarFieldModulus]
  ring

theorem coordV_shiftFirst (value : Value) (direction : Int) :
    coordV (shiftFirst value direction) = coordV value := by
  simp only [coordV, shiftFirst, latticeA, latticeB]
  norm_num [EisensteinKernel.kernelA, EisensteinKernel.kernelB]
  ring

theorem coordU_shiftSecond (value : Value) (direction : Int) :
    coordU (shiftSecond value direction) = coordU value := by
  simp only [coordU, shiftSecond, latticeA, latticeB]
  norm_num [EisensteinKernel.kernelA, EisensteinKernel.kernelB]
  ring

theorem coordV_shiftSecond (value : Value) (direction : Int) :
    coordV (shiftSecond value direction) =
      coordV value - direction * modulus := by
  simp only [coordV, shiftSecond, modulus, latticeA, latticeB]
  norm_num [EisensteinKernel.kernelA, EisensteinKernel.kernelB,
    GarblingPrize.Protected.scalarFieldModulus]
  ring

theorem evaluate_hexReduceScalar (scalar : Nat) :
    evaluate (hexReduceScalar scalar) =
      (scalar : EisensteinKernel.ScalarRing) := by
  simp only [hexReduceScalar]
  split
  · split
    · rw [evaluate_shiftFirst, evaluate_babai]
    · rw [evaluate_shiftSecond, evaluate_babai]
  · split
    · split
      · rw [evaluate_shiftFirst, evaluate_babai]
      · rw [evaluate_shiftSecond, evaluate_babai]
    · exact evaluate_babai scalar

/-- The corrected representative is in the closed Voronoi hexagon, written
in the dual `(u,v)` coordinates of the certified scalar kernel. -/
theorem hexReduceScalar_bounds (scalar : Nat) :
    let u := coordU (hexReduceScalar scalar)
    let v := coordV (hexReduceScalar scalar)
    (-modulus ≤ 2 * u + v ∧ 2 * u + v ≤ modulus ∧
      -modulus ≤ u + 2 * v ∧ u + 2 * v ≤ modulus ∧
      -modulus ≤ u - v ∧ u - v ≤ modulus) := by
  have herrors := babai_error_bounds scalar
  unfold hexReduceScalar
  dsimp only
  split <;> rename_i hcorner
  · split <;> rename_i horder
    · rw [coordU_shiftFirst, coordV_shiftFirst,
        coordU_babai, coordV_babai]
      simp only [modulus, GarblingPrize.Protected.scalarFieldModulus] at *
      omega
    · rw [coordU_shiftSecond, coordV_shiftSecond,
        coordU_babai, coordV_babai]
      simp only [modulus, GarblingPrize.Protected.scalarFieldModulus] at *
      omega
  · split <;> rename_i hnegative
    · split <;> rename_i horder
      · rw [coordU_shiftFirst, coordV_shiftFirst,
          coordU_babai, coordV_babai]
        simp only [modulus, GarblingPrize.Protected.scalarFieldModulus] at *
        omega
      · rw [coordU_shiftSecond, coordV_shiftSecond,
          coordU_babai, coordV_babai]
        simp only [modulus, GarblingPrize.Protected.scalarFieldModulus] at *
        omega
    · rw [coordU_babai, coordV_babai]
      simp only [modulus, GarblingPrize.Protected.scalarFieldModulus] at *
      omega

theorem norm_scaled (value : Value) :
    modulus * norm value = errorNorm (coordU value) (coordV value) := by
  simp only [modulus, EisensteinRadix.norm, errorNorm, coordU, coordV,
    latticeA, latticeB]
  norm_num [EisensteinKernel.kernelA, EisensteinKernel.kernelB,
    GarblingPrize.Protected.scalarFieldModulus]
  ring

private theorem square_le_square {x radius : Int} (_hradius : 0 ≤ radius)
    (hlower : -radius ≤ x) (hupper : x ≤ radius) :
    x ^ 2 ≤ radius ^ 2 := by
  nlinarith [mul_nonneg (by omega : 0 ≤ radius - x)
    (by omega : 0 ≤ radius + x)]

private theorem hex_error_bound (u v radius : Int) (hradius : 0 ≤ radius)
    (ha0 : -radius ≤ 2 * u + v) (ha1 : 2 * u + v ≤ radius)
    (hb0 : -radius ≤ u + 2 * v) (hb1 : u + 2 * v ≤ radius)
    (hc0 : -radius ≤ u - v) (hc1 : u - v ≤ radius) :
    3 * errorNorm u v ≤ radius ^ 2 := by
  let a := 2 * u + v
  let b := u + 2 * v
  have haSq : a ^ 2 ≤ radius ^ 2 :=
    square_le_square hradius ha0 ha1
  have hbSq : b ^ 2 ≤ radius ^ 2 :=
    square_le_square hradius hb0 hb1
  have hcSq : (a - b) ^ 2 ≤ radius ^ 2 := by
    apply square_le_square hradius
    · dsimp only [a, b]
      omega
    · dsimp only [a, b]
      omega
  by_cases hab : a * b ≤ 0
  · simp only [errorNorm]
    dsimp only [a, b] at haSq hbSq hcSq hab ⊢
    nlinarith
  · have habpos : 0 < a * b := by omega
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := by
        by_contra hn
        have hp := mul_nonpos_of_nonneg_of_nonpos ha (by omega : b ≤ 0)
        omega
      by_cases hba : b ≤ a
      · have hp := mul_nonneg hb (by omega : 0 ≤ a - b)
        simp only [errorNorm]
        dsimp only [a, b] at haSq hbSq hcSq habpos ha hb hba hp ⊢
        nlinarith
      · have hp := mul_nonneg ha (by omega : 0 ≤ b - a)
        simp only [errorNorm]
        dsimp only [a, b] at haSq hbSq hcSq habpos ha hb hba hp ⊢
        nlinarith
    · have haNeg : a ≤ 0 := by omega
      have hbNeg : b ≤ 0 := by
        by_contra hn
        have hp := mul_nonpos_of_nonpos_of_nonneg haNeg (by omega : 0 ≤ b)
        omega
      by_cases habOrder : a ≤ b
      · have hp := mul_nonneg (by omega : 0 ≤ -b)
          (by omega : 0 ≤ b - a)
        simp only [errorNorm]
        dsimp only [a, b] at haSq hbSq hcSq habpos haNeg hbNeg habOrder hp ⊢
        nlinarith
      · have hp := mul_nonneg (by omega : 0 ≤ -a)
          (by omega : 0 ≤ a - b)
        simp only [errorNorm]
        dsimp only [a, b] at haSq hbSq hcSq habpos haNeg hbNeg habOrder hp ⊢
        nlinarith

theorem hexReduceScalar_norm_bound (scalar : Nat) :
    3 * norm (hexReduceScalar scalar) ≤ modulus := by
  have hhex := hexReduceScalar_bounds scalar
  have hmod : 0 < modulus := by
    norm_num [modulus, GarblingPrize.Protected.scalarFieldModulus]
  have hscaled := hex_error_bound
    (coordU (hexReduceScalar scalar)) (coordV (hexReduceScalar scalar))
    modulus (by omega) hhex.1 hhex.2.1 hhex.2.2.1 hhex.2.2.2.1
    hhex.2.2.2.2.1 hhex.2.2.2.2.2
  rw [← norm_scaled] at hscaled
  have hproduct : modulus * (3 * norm (hexReduceScalar scalar)) ≤
      modulus * modulus := by nlinarith
  exact (Int.mul_le_mul_left hmod).mp hproduct

set_option maxHeartbeats 2000000 in
private theorem normBound_step (index : Nat) (hindex : index < 90) :
    normBound index + 2 ≤ 7 * (normBound (index + 1) + 1) ∧
      28 * (normBound (index + 1) + 1) <
        (7 * (normBound (index + 1) + 1) - normBound index) ^ 2 := by
  interval_cases index <;> norm_num [normBound]

theorem residual_hex_norm_le_bound (scalar count : Nat) (hcount : count ≤ 90) :
    norm (EisensteinRadix.residual count (hexReduceScalar scalar)) ≤
      normBound count := by
  induction count with
  | zero =>
      simp only [EisensteinRadix.residual, normBound]
      have h := hexReduceScalar_norm_bound scalar
      norm_num [modulus, GarblingPrize.Protected.scalarFieldModulus] at h ⊢
      omega
  | succ count ih =>
      rw [residual_succ]
      have hindex : count < 90 := by omega
      have hstep := normBound_step count hindex
      exact norm_divide_le _ (normBound count) (normBound (count + 1))
        (ih (by omega)) hstep.1 hstep.2

def wideTopDigit (scalar : Nat) : Value :=
  EisensteinRadix.residual 89 (hexReduceScalar scalar)

theorem wideTopDigit_norm_le_seven (scalar : Nat) :
    norm (wideTopDigit scalar) ≤ 7 := by
  simpa [wideTopDigit, normBound] using
    residual_hex_norm_le_bound scalar 89 (by omega)

def directionFirst : Value := ⟨latticeA, latticeB⟩

def directionSecond : Value := ⟨-latticeB, latticeA - latticeB⟩

def directionThird : Value := ⟨latticeB - latticeA, -latticeA⟩

theorem inner_directionFirst (value : Value) :
    innerTwice value directionFirst = 2 * coordU value + coordV value := by
  simp only [innerTwice, directionFirst, coordU, coordV]
  ring

theorem inner_directionSecond (value : Value) :
    innerTwice value directionSecond = -(coordU value + 2 * coordV value) := by
  simp only [innerTwice, directionSecond, coordU, coordV]
  ring

theorem inner_directionThird (value : Value) :
    innerTwice value directionThird = -(coordU value - coordV value) := by
  simp only [innerTwice, directionThird, coordU, coordV]
  ring

theorem hex_inner_bounds (scalar : Nat) :
    (-modulus ≤ innerTwice (hexReduceScalar scalar) directionFirst ∧
        innerTwice (hexReduceScalar scalar) directionFirst ≤ modulus) ∧
      (-modulus ≤ innerTwice (hexReduceScalar scalar) directionSecond ∧
        innerTwice (hexReduceScalar scalar) directionSecond ≤ modulus) ∧
      (-modulus ≤ innerTwice (hexReduceScalar scalar) directionThird ∧
        innerTwice (hexReduceScalar scalar) directionThird ≤ modulus) := by
  have h := hexReduceScalar_bounds scalar
  rw [inner_directionFirst, inner_directionSecond, inner_directionThird]
  omega

def dualStep (direction : Value) : Value :=
  ⟨2 * direction.re + direction.im, -direction.re + 3 * direction.im⟩

theorem inner_alphaMul (value direction : Value) :
    innerTwice (alphaMul value) direction =
      innerTwice value (dualStep direction) := by
  simp only [innerTwice, alphaMul, dualStep]
  ring

theorem inner_add_left (left right direction : Value) :
    innerTwice (add left right) direction =
      innerTwice left direction + innerTwice right direction := by
  simp only [innerTwice, add]
  ring

def signedAbs (value : Int) : Int := max value (-value)

def unitBound (direction : Value) : Int :=
  max (signedAbs (2 * direction.re - direction.im))
    (max (signedAbs (-direction.re + 2 * direction.im))
      (signedAbs (direction.re + direction.im)))

theorem digit_inner_bound (digit : Digit) (direction : Value) :
    -unitBound direction ≤ innerTwice digit.value direction ∧
      innerTwice digit.value direction ≤ unitBound direction := by
  let x := 2 * direction.re - direction.im
  let y := -direction.re + 2 * direction.im
  let z := direction.re + direction.im
  have hx0 : x ≤ signedAbs x := le_max_left _ _
  have hx1 : -x ≤ signedAbs x := le_max_right _ _
  have hy0 : y ≤ signedAbs y := le_max_left _ _
  have hy1 : -y ≤ signedAbs y := le_max_right _ _
  have hz0 : z ≤ signedAbs z := le_max_left _ _
  have hz1 : -z ≤ signedAbs z := le_max_right _ _
  have hxb : signedAbs x ≤ unitBound direction := le_max_left _ _
  have hyb0 : signedAbs y ≤
      max (signedAbs y) (signedAbs z) := le_max_left _ _
  have hzb0 : signedAbs z ≤
      max (signedAbs y) (signedAbs z) := le_max_right _ _
  have hyb : signedAbs y ≤ unitBound direction := hyb0.trans (le_max_right _ _)
  have hzb : signedAbs z ≤ unitBound direction := hzb0.trans (le_max_right _ _)
  cases digit <;>
    simp only [Digit.value, innerTwice] <;>
    dsimp only [x, y, z] at * <;>
    omega

def dualPow : Nat → Value → Value
  | 0, direction => direction
  | count + 1, direction => dualPow count (dualStep direction)

def directionalBudget : Nat → Value → Int
  | 0, _ => 0
  | count + 1, direction =>
      unitBound direction + directionalBudget count (dualStep direction)

theorem residual_inner_error_bound (count : Nat) (value direction : Value) :
    let error := innerTwice value direction -
      innerTwice (EisensteinRadix.residual count value) (dualPow count direction)
    (-directionalBudget count direction ≤ error ∧
      error ≤ directionalBudget count direction) := by
  induction count generalizing value direction with
  | zero =>
      simp [EisensteinRadix.residual, dualPow, directionalBudget]
  | succ count ih =>
      have hdecompose := congrArg (fun result => innerTwice result direction)
        (alphaMul_divide_add_digit value)
      rw [inner_add_left, inner_alphaMul] at hdecompose
      have htail := ih (divide value) (dualStep direction)
      have hdigit := digit_inner_bound (select value) direction
      simp only [EisensteinRadix.residual, dualPow, directionalBudget]
      simp only at htail
      omega

theorem wide_inner_bound (scalar : Nat) (direction : Value)
    (hinner : -modulus ≤ innerTwice (hexReduceScalar scalar) direction ∧
      innerTwice (hexReduceScalar scalar) direction ≤ modulus) :
    -modulus - directionalBudget 89 direction ≤
        innerTwice (wideTopDigit scalar) (dualPow 89 direction) ∧
      innerTwice (wideTopDigit scalar) (dualPow 89 direction) ≤
        modulus + directionalBudget 89 direction := by
  have herror := residual_inner_error_bound 89
    (hexReduceScalar scalar) direction
  simp only [wideTopDigit] at herror ⊢
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem wideTopDigit_norm_ne_seven (scalar : Nat) :
    norm (wideTopDigit scalar) ≠ 7 := by
  intro hnorm
  have hhex := hex_inner_bounds scalar
  have hfirst := wide_inner_bound scalar directionFirst hhex.1
  have hsecond := wide_inner_bound scalar directionSecond hhex.2.1
  have hthird := wide_inner_bound scalar directionThird hhex.2.2
  rcases hvalue : wideTopDigit scalar with ⟨re, im⟩
  rw [hvalue] at hnorm hfirst hsecond hthird
  have hreSq : re ^ 2 ≤ 9 := by
    simp only [EisensteinRadix.norm] at hnorm
    nlinarith [sq_nonneg (2 * im - re)]
  have himSq : im ^ 2 ≤ 9 := by
    simp only [EisensteinRadix.norm] at hnorm
    nlinarith [sq_nonneg (2 * re - im)]
  have hre0 : -3 ≤ re := by nlinarith [sq_nonneg (re + 3)]
  have hre1 : re ≤ 3 := by nlinarith [sq_nonneg (re - 3)]
  have him0 : -3 ≤ im := by nlinarith [sq_nonneg (im + 3)]
  have him1 : im ≤ 3 := by nlinarith [sq_nonneg (im - 3)]
  norm_num [directionFirst, directionSecond, directionThird, dualPow, dualStep,
    directionalBudget, unitBound, signedAbs, innerTwice, latticeA, latticeB,
    EisensteinKernel.kernelA, EisensteinKernel.kernelB, modulus,
    GarblingPrize.Protected.scalarFieldModulus] at hfirst hsecond hthird
  interval_cases re <;> interval_cases im
  all_goals norm_num [EisensteinRadix.norm] at hnorm
  all_goals omega

theorem norm_le_four_of_le_seven (value : Value) (hbound : norm value ≤ 7)
    (hne : norm value ≠ 7) : norm value ≤ 4 := by
  rcases value with ⟨re, im⟩
  by_contra hfour
  have hnorm : EisensteinRadix.norm { re := re, im := im } = 5 ∨
      EisensteinRadix.norm { re := re, im := im } = 6 := by omega
  have hreSq : re ^ 2 ≤ 9 := by
    simp only [EisensteinRadix.norm] at hbound
    nlinarith [sq_nonneg (2 * im - re)]
  have himSq : im ^ 2 ≤ 9 := by
    simp only [EisensteinRadix.norm] at hbound
    nlinarith [sq_nonneg (2 * re - im)]
  have hre0 : -3 ≤ re := by nlinarith [sq_nonneg (re + 3)]
  have hre1 : re ≤ 3 := by nlinarith [sq_nonneg (re - 3)]
  have him0 : -3 ≤ im := by nlinarith [sq_nonneg (im + 3)]
  have him1 : im ≤ 3 := by nlinarith [sq_nonneg (im - 3)]
  interval_cases re <;> interval_cases im
  all_goals norm_num [EisensteinRadix.norm] at hnorm

/-- After 89 ordinary radix-seven digits, the exact terminal coefficient has
norm at most four.  Its alphabet therefore contains only 19 Eisenstein
integers (zero and three rings of six associates), rather than 31. -/
theorem wideTopDigit_norm_le_four (scalar : Nat) :
    norm (wideTopDigit scalar) ≤ 4 :=
  norm_le_four_of_le_seven _ (wideTopDigit_norm_le_seven scalar)
    (wideTopDigit_norm_ne_seven scalar)

def wideDigitCandidates : List Value :=
  [⟨0, 0⟩,
    ⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩,
    ⟨1, -1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨2, 1⟩, ⟨-2, -1⟩,
    ⟨2, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨-2, -2⟩]

theorem wideDigitCandidates_length : wideDigitCandidates.length = 19 := by
  decide

theorem mem_wideDigitCandidates_iff (value : Value) :
    value ∈ wideDigitCandidates ↔ norm value ≤ 4 := by
  rcases value with ⟨re, im⟩
  constructor
  · intro hmem
    simp only [wideDigitCandidates, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h <;> simp_all [EisensteinRadix.norm]
  · intro hbound
    have hreSq : re ^ 2 ≤ 5 := by
      simp only [EisensteinRadix.norm] at hbound
      nlinarith [sq_nonneg (2 * im - re)]
    have himSq : im ^ 2 ≤ 5 := by
      simp only [EisensteinRadix.norm] at hbound
      nlinarith [sq_nonneg (2 * re - im)]
    have hre0 : -2 ≤ re := by nlinarith [sq_nonneg (re + 2)]
    have hre1 : re ≤ 2 := by nlinarith [sq_nonneg (re - 2)]
    have him0 : -2 ≤ im := by nlinarith [sq_nonneg (im + 2)]
    have him1 : im ≤ 2 := by nlinarith [sq_nonneg (im - 2)]
    interval_cases re <;> interval_cases im
    all_goals norm_num [EisensteinRadix.norm] at hbound
    all_goals norm_num [wideDigitCandidates, EisensteinRadix.norm]

theorem evaluate_wide_ninety (scalar : Nat) :
    evaluateDigits (digits 89 (hexReduceScalar scalar)) +
        (3 + EisensteinKernel.lambda) ^ 89 * evaluate (wideTopDigit scalar) =
      (scalar : EisensteinKernel.ScalarRing) := by
  unfold wideTopDigit
  rw [← evaluate_digits_add_residual 89 (hexReduceScalar scalar)]
  exact evaluate_hexReduceScalar scalar

end GarblingPrize.Submission.EisensteinWideTop
