import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import GarblingPrize.Protected.Target

/-!
# Affine `Z = 1` specializations of Jacobian `addMap`

These lemmas are proved over an abstract field so the elaborator never
unfolds Mathlib's Jacobian addition polynomials at a concrete extension
field such as BN254 `Fq2`.  Concrete modules only apply the stored
generic proofs.
-/

open WeierstrassCurve
open WeierstrassCurve.Jacobian

namespace GarblingPrize.Submission.JacobianAffineAddMap

local notation3 "Xc" => (0 : Fin 3)
local notation3 "Yc" => (1 : Fin 3)
local notation3 "Zc" => (2 : Fin 3)

variable {F : Type*} [Field F]
variable (W : WeierstrassCurve F)

private theorem affine_Z_ne (x y : F) :
    (![x, y, (1 : F)] : Fin 3 → F) Zc ≠ 0 :=
  one_ne_zero

private theorem affine_div_X (x y : F) :
    (![x, y, (1 : F)] : Fin 3 → F) Xc /
        ((![x, y, (1 : F)] : Fin 3 → F) Zc) ^ 2 = x := by
  simp

private theorem affine_div_Y (x y : F) :
    (![x, y, (1 : F)] : Fin 3 → F) Yc /
        ((![x, y, (1 : F)] : Fin 3 → F) Zc) ^ 3 = y := by
  simp

/-- Distinct-abscissa affine representatives add to ordinary affine sum. -/
theorem addMap_of_X_ne
    [DecidableEq F]
    (lx ly rx ry : F)
    (hP : W.toJacobian.Equation ![lx, ly, 1])
    (hQ : W.toJacobian.Equation ![rx, ry, 1])
    (hx : lx ≠ rx) :
    W.toJacobian.addMap ⟦![lx, ly, (1 : F)]⟧ ⟦![rx, ry, (1 : F)]⟧ =
      ⟦![W.toAffine.addX lx rx (W.toAffine.slope lx rx ly ry),
        W.toAffine.addY lx rx ly (W.toAffine.slope lx rx ly ry),
        (1 : F)]⟧ := by
  have hsum :=
    W.toJacobian.addMap_of_Z_ne_zero hP hQ
      (affine_Z_ne lx ly) (affine_Z_ne rx ry)
      (by
        intro hxy
        exact hx (by
          have := hxy.left
          simpa using this))
  simpa [affine_div_X, affine_div_Y] using hsum

/-- Finite doubling when the tangent denominator is nonzero. -/
theorem addMap_of_Y_ne_negY
    [DecidableEq F]
    (x y : F)
    (hP : W.toJacobian.Equation ![x, y, 1])
    (hy : y ≠ W.toAffine.negY x y) :
    W.toJacobian.addMap ⟦![x, y, (1 : F)]⟧ ⟦![x, y, (1 : F)]⟧ =
      ⟦![W.toAffine.addX x x (W.toAffine.slope x x y y),
        W.toAffine.addY x x y (W.toAffine.slope x x y y),
        (1 : F)]⟧ := by
  have hsum :=
    W.toJacobian.addMap_of_Z_ne_zero hP hP
      (affine_Z_ne x y) (affine_Z_ne x y)
      (by
        intro hxy
        apply hy
        have hyJac :
            y * (1 : F) ^ 3 =
              W.toJacobian.negY ![x, y, (1 : F)] * (1 : F) ^ 3 :=
          hxy.right
        have hyJac' : y = W.toJacobian.negY ![x, y, (1 : F)] := by
          simpa using hyJac
        have hyAff :=
          W.toJacobian.negY_of_Z_ne_zero
            (P := ![x, y, (1 : F)]) (affine_Z_ne x y)
        have hyAff' :
            W.toJacobian.negY ![x, y, (1 : F)] = W.toAffine.negY x y := by
          simpa [one_pow, div_one] using hyAff
        exact hyJac'.trans hyAff')
  simpa [affine_div_X, affine_div_Y] using hsum

end GarblingPrize.Submission.JacobianAffineAddMap
