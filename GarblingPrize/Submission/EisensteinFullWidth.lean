import Mathlib.Algebra.Module.ZMod
import GarblingPrize.Submission.EisensteinRadix
import GarblingPrize.Submission.G1Eigenvalue

namespace GarblingPrize.Submission.EisensteinFullWidth

/-!
# Exact 91-map group semantics for the norm-seven GLV radix

The executable scalar codec produces little-endian digits in the units
`0, ±1, ±omega, ±omega²` of the Eisenstein integers.  This module interprets
those digits directly in BN254 G1, where `omega` is the checked coordinate
endomorphism and the Horner multiplier is `3 + omega`.
-/

open GarblingPrize.Protected
open GarblingPrize.Submission.EisensteinRadix

noncomputable section

set_option maxRecDepth 8192

abbrev Point := BN254.G1
abbrev ScalarRing := EisensteinKernel.ScalarRing

local instance concreteGroup : AddCommGroup Point :=
  BN254.bn254.addCommGroup

local instance scalarModule : Module ScalarRing Point :=
  AddCommGroup.zmodModule G1Eigenvalue.scalarFieldModulus_nsmul

/-- The group endomorphism represented by multiplication by the radix
`3 + omega`. -/
def alphaPoint (point : Point) : Point :=
  (3 + (EisensteinKernel.lambda : ScalarRing)) • point

theorem alphaPoint_eq_three_add_phi (point : Point) :
    alphaPoint point = 3 • point + G1Endomorphism.phi point := by
  rw [G1Eigenvalue.phi_eq_lambda_nsmul]
  unfold alphaPoint
  rw [scalarModule.add_smul]
  change
    ((3 : ScalarRing).val) • point +
        ((EisensteinKernel.lambda : ScalarRing).val) • point =
      3 • point + EisensteinKernel.lambda • point
  have hthree : (3 : ScalarRing).val = 3 := by
    decide
  have hlambda :
      (EisensteinKernel.lambda : ScalarRing).val =
        EisensteinKernel.lambda := by
    decide
  rw [hthree, hlambda]

@[simp] theorem alphaPoint_zero : alphaPoint (0 : Point) = 0 := by
  unfold alphaPoint
  exact scalarModule.smul_zero _

theorem scalarPoint_neg (scalar : ScalarRing) (point : Point) :
    scalar • (-point) = -(scalar • point) :=
  smul_neg scalar point

theorem point_nsmul_neg (count : Nat) (point : Point) :
    count • (-point) = -(count • point) :=
  neg_nsmul point count

/-- The exact group term represented by one seven-way unit digit. -/
def digitTerm (digit : Digit) (point : Point) : Point :=
  EisensteinRadix.evaluate digit.value • point

def unitPoint : Digit → Point → Point
  | .zero, _ => 0
  | .one, point => point
  | .negOne, point => -point
  | .omega, point => G1Endomorphism.phi point
  | .negOmega, point => -G1Endomorphism.phi point
  | .omegaSq, point => G1Endomorphism.phi (G1Endomorphism.phi point)
  | .negOmegaSq, point => -G1Endomorphism.phi (G1Endomorphism.phi point)

private theorem lambdaPoint (point : Point) :
    (EisensteinKernel.lambda : ScalarRing) • point =
      G1Endomorphism.phi point := by
  change ((EisensteinKernel.lambda : ScalarRing).val) • point = _
  have hlambda :
      (EisensteinKernel.lambda : ScalarRing).val =
        EisensteinKernel.lambda := by decide
  rw [hlambda]
  exact (G1Eigenvalue.phi_eq_lambda_nsmul point).symm

private theorem lambdaSqPoint (point : Point) :
    ((EisensteinKernel.lambda : ScalarRing) ^ 2) • point =
      G1Endomorphism.phi (G1Endomorphism.phi point) := by
  rw [pow_two, scalarModule.mul_smul, lambdaPoint, lambdaPoint]

theorem digitTerm_eq_unitPoint (digit : Digit) (point : Point) :
    digitTerm digit point = unitPoint digit point := by
  cases digit with
  | zero =>
      change (0 : ScalarRing) • point = 0
      exact scalarModule.zero_smul point
  | one =>
      change (1 : ScalarRing) • point = point
      exact scalarModule.one_smul point
  | negOne =>
      change (-1 : ScalarRing) • point = -point
      rw [neg_smul, scalarModule.one_smul]
      rfl
  | omega =>
      change (EisensteinKernel.lambda : ScalarRing) • point = _
      exact lambdaPoint point
  | negOmega =>
      change (-(EisensteinKernel.lambda : ScalarRing)) • point =
        -G1Endomorphism.phi point
      rw [neg_smul, lambdaPoint]
      rfl
  | omegaSq =>
      have hscalar :
          EisensteinRadix.evaluate Digit.omegaSq.value =
            (EisensteinKernel.lambda : ScalarRing) ^ 2 := by
        simp only [EisensteinRadix.evaluate, Digit.value]
        linear_combination -EisensteinKernel.lambda_root
      unfold digitTerm unitPoint
      rw [hscalar, lambdaSqPoint]
  | negOmegaSq =>
      have hscalar :
          EisensteinRadix.evaluate Digit.negOmegaSq.value =
            -((EisensteinKernel.lambda : ScalarRing) ^ 2) := by
        simp only [EisensteinRadix.evaluate, Digit.value]
        linear_combination EisensteinKernel.lambda_root
      unfold digitTerm unitPoint
      rw [hscalar, neg_smul, lambdaSqPoint]
      rfl

theorem digitTerm_neg (digit : Digit) (point : Point) :
    digitTerm digit (-point) = -digitTerm digit point := by
  unfold digitTerm
  exact scalarPoint_neg _ _

/-- Little-endian Horner recomposition in the norm-seven radix. -/
def recompose : List Point → Point
  | [] => 0
  | head :: tail => head + alphaPoint (recompose tail)

@[simp] theorem recompose_nil : recompose ([] : List Point) = 0 := rfl

@[simp] theorem recompose_cons (head : Point) (tail : List Point) :
    recompose (head :: tail) = head + alphaPoint (recompose tail) := rfl

theorem recompose_digitTerms (digits : List Digit) (point : Point) :
    recompose (digits.map fun digit => digitTerm digit point) =
      EisensteinRadix.evaluateDigits digits • point := by
  induction digits with
  | nil => rfl
  | cons digit tail ih =>
      simp only [List.map_cons, recompose_cons,
        EisensteinRadix.evaluateDigits, alphaPoint]
      rw [ih]
      have hmul :
          ((3 + (EisensteinKernel.lambda : ScalarRing)) *
              EisensteinRadix.evaluateDigits tail) • point =
            (3 + (EisensteinKernel.lambda : ScalarRing)) •
              (EisensteinRadix.evaluateDigits tail • point) :=
        scalarModule.mul_smul _ _ _
      calc
        digitTerm digit point +
              (3 + (EisensteinKernel.lambda : ScalarRing)) •
                (EisensteinRadix.evaluateDigits tail • point) =
            EisensteinRadix.evaluate digit.value • point +
              ((3 + (EisensteinKernel.lambda : ScalarRing)) *
                EisensteinRadix.evaluateDigits tail) • point := by
              unfold digitTerm
              rw [hmul]
        _ = (EisensteinRadix.evaluate digit.value +
              (3 + (EisensteinKernel.lambda : ScalarRing)) *
                EisensteinRadix.evaluateDigits tail) • point :=
            (scalarModule.add_smul _ _ _).symm

/-- Every protected scalar acts exactly as its 91 norm-seven digit terms. -/
theorem recompose_scalar (scalar : Fin scalarFieldModulus) (point : Point) :
    recompose
        ((EisensteinRadix.digits 91
          (EisensteinRadix.reduceScalar scalar.val)).map
            fun digit => digitTerm digit point) =
      scalar.val • point := by
  rw [recompose_digitTerms,
    EisensteinRadix.evaluateDigits_reduceScalar scalar.val]
  change ((scalar.val : ScalarRing).val) • point = scalar.val • point
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt scalar.isLt]

/-! ## Offset-plus-unit-digit maps -/

def offsetTotal (offsets : List Point) : Point := recompose offsets

def mapOutput (offset : Point) (digit : Digit) (point : Point) : Point :=
  offset - digitTerm digit point

def mapOutputs (offsets : List Point) (digits : List Digit)
    (point : Point) : List Point :=
  List.zipWith (fun offset digit => mapOutput offset digit point)
    offsets digits

def outputList (offsets : List Point) (digits : List Digit)
    (point : Point) : Point :=
  recompose (mapOutputs offsets digits point)

theorem alphaPoint_add (left right : Point) :
    alphaPoint (left + right) = alphaPoint left + alphaPoint right := by
  unfold alphaPoint
  exact scalarModule.smul_add _ _ _

theorem alphaPoint_sub (left right : Point) :
    alphaPoint (left - right) = alphaPoint left - alphaPoint right := by
  let alphaHom : Point →+ Point :=
    { toFun := fun point =>
        (3 + (EisensteinKernel.lambda : ScalarRing)) • point
      map_zero' := scalarModule.smul_zero _
      map_add' := scalarModule.smul_add _ }
  exact alphaHom.map_sub left right

theorem outputList_eq (offsets : List Point) (digits : List Digit)
    (point : Point) (hlength : offsets.length = digits.length) :
    outputList offsets digits point =
      offsetTotal offsets -
        recompose (digits.map fun digit => digitTerm digit point) := by
  induction offsets generalizing digits with
  | nil =>
      cases digits with
      | nil => rfl
      | cons digit digits => simp at hlength
  | cons offset offsets ih =>
      cases digits with
      | nil => simp at hlength
      | cons digit digits =>
          have htail : offsets.length = digits.length := by
            simpa using Nat.succ.inj hlength
          simp only [outputList, mapOutputs, List.zipWith_cons_cons,
            recompose_cons, List.map_cons]
          change
            mapOutput offset digit point +
                alphaPoint (outputList offsets digits point) =
              offsetTotal (offset :: offsets) -
                (digitTerm digit point +
                  alphaPoint
                    (recompose (digits.map fun digit => digitTerm digit point)))
          rw [ih digits htail, alphaPoint_sub]
          simp only [mapOutput, offsetTotal, recompose_cons]
          abel

theorem output_scalar (offsets : List Point)
    (scalar : Fin scalarFieldModulus) (point : Point)
    (hlength : offsets.length = 91) :
    outputList offsets
        (EisensteinRadix.digits 91
          (EisensteinRadix.reduceScalar scalar.val)) point =
      offsetTotal offsets - scalar.val • point := by
  rw [outputList_eq]
  · rw [recompose_scalar]
  · simpa using hlength.trans
      (by simp [EisensteinRadix.digits] :
        (EisensteinRadix.digits 91
          (EisensteinRadix.reduceScalar scalar.val)).length = 91).symm

/-! ## Exact offset translation -/

def translatedOffset (source target : Digit) (point offset : Point) : Point :=
  offset + digitTerm target point - digitTerm source point

theorem mapOutput_translatedOffset (source target : Digit)
    (point offset : Point) :
    mapOutput (translatedOffset source target point offset) target point =
      mapOutput offset source point := by
  unfold mapOutput translatedOffset
  abel

def translateOffsets :
    List Point → List Digit → List Digit → Point → List Point
  | offset :: offsets, source :: sources, target :: targets, point =>
      translatedOffset source target point offset ::
        translateOffsets offsets sources targets point
  | _, _, _, _ => []

theorem mapOutputs_translateOffsets (offsets : List Point)
    (source target : List Digit) (point : Point)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    mapOutputs (translateOffsets offsets source target point) target point =
      mapOutputs offsets source point := by
  induction offsets generalizing source target with
  | nil =>
      cases source with
      | cons source sources => simp at hsource
      | nil =>
          cases target with
          | cons target targets => simp at htarget
          | nil => rfl
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              have hs : offsets.length = sources.length := by
                simpa using Nat.succ.inj hsource
              have ht : offsets.length = targets.length := by
                simpa using Nat.succ.inj htarget
              simp only [translateOffsets, mapOutputs, List.zipWith_cons_cons,
                mapOutput_translatedOffset]
              exact congrArg (mapOutput offset source point :: ·)
                (ih sources targets hs ht)

theorem offsetTotal_translateOffsets (offsets : List Point)
    (source target : List Digit) (point : Point)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    offsetTotal (translateOffsets offsets source target point) =
      offsetTotal offsets +
        (recompose (target.map fun digit => digitTerm digit point) -
          recompose (source.map fun digit => digitTerm digit point)) := by
  induction offsets generalizing source target with
  | nil =>
      cases source with
      | cons source sources => simp at hsource
      | nil =>
          cases target with
          | cons target targets => simp at htarget
          | nil => rfl
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              have hs : offsets.length = sources.length := by
                simpa using Nat.succ.inj hsource
              have ht : offsets.length = targets.length := by
                simpa using Nat.succ.inj htarget
              simp only [translateOffsets, offsetTotal, recompose_cons,
                List.map_cons]
              change
                translatedOffset source target point offset +
                    alphaPoint
                      (offsetTotal
                        (translateOffsets offsets sources targets point)) =
                  offset + alphaPoint (offsetTotal offsets) +
                    (digitTerm target point +
                        alphaPoint
                          (recompose
                            (targets.map fun digit => digitTerm digit point)) -
                      (digitTerm source point +
                        alphaPoint
                          (recompose
                            (sources.map fun digit => digitTerm digit point))))
              rw [ih sources targets hs ht, alphaPoint_add,
                alphaPoint_sub]
              unfold translatedOffset
              abel

theorem translateOffsets_source_target_source (offsets : List Point)
    (source target : List Digit) (point : Point)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    translateOffsets
        (translateOffsets offsets source target point) target source point =
      offsets := by
  induction offsets generalizing source target with
  | nil =>
      cases source with
      | cons source sources => simp at hsource
      | nil =>
          cases target with
          | cons target targets => simp at htarget
          | nil => rfl
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              have hs : offsets.length = sources.length := by
                simpa using Nat.succ.inj hsource
              have ht : offsets.length = targets.length := by
                simpa using Nat.succ.inj htarget
              simp only [translateOffsets]
              rw [ih sources targets hs ht]
              congr 1
              unfold translatedOffset
              abel

end

end GarblingPrize.Submission.EisensteinFullWidth
