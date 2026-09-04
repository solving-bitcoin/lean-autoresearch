import GarblingPrize.Protected.PrimeCertificates.Base
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace GarblingPrize.Protected

open WeierstrassCurve

namespace BN254

abbrev Fq := ZMod baseFieldModulus

instance basePrime : Fact baseFieldModulus.Prime :=
  ⟨BN254Certificates.baseFieldModulus_prime⟩

/-- The short Weierstrass BN254 G1 curve `y² = x³ + 3`. -/
def curve : WeierstrassCurve Fq where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 3

abbrev G1 := curve.toAffine.Point

theorem discriminant_ne_zero : curve.Δ ≠ 0 := by
  rw [show curve.Δ = -(3888 : Fq) by
    simp [curve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring]
  intro hzero
  have hdiv : baseFieldModulus ∣ 3888 :=
    (ZMod.natCast_eq_zero_iff 3888 baseFieldModulus).mp (neg_eq_zero.mp hzero)
  norm_num [baseFieldModulus] at hdiv

/-- The protected finite-affine equation over canonical representatives. -/
def OnCurve (x y : CanonicalFq) : Prop :=
  ((y.val : Fq) ^ 2 = (x.val : Fq) ^ 3 + 3)

theorem onCurve_iff_nonsingular (x y : CanonicalFq) :
    OnCurve x y ↔ curve.toAffine.Nonsingular (x.val : Fq) (y.val : Fq) := by
  rw [← curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminant_ne_zero]
  simp [OnCurve, curve, WeierstrassCurve.Affine.equation_iff]

/-- Embed a canonical finite-affine witness in the canonical affine group. -/
def ofAffine (x y : CanonicalFq) (h : OnCurve x y) : G1 :=
  .some (x.val : Fq) (y.val : Fq) ((onCurve_iff_nonsingular x y).mp h)

@[simp] theorem ofAffine_ne_zero (x y : CanonicalFq) (h : OnCurve x y) :
    ofAffine x y h ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero
    ((onCurve_iff_nonsingular x y).mp h)

/-- Unique wire-level output: either infinity or one canonical finite affine
coordinate pair. Projective representatives never cross the protected
boundary. -/
inductive CanonicalOutput where
  | infinity
  | affine (x y : CanonicalFq) (onCurve : OnCurve x y)

namespace CanonicalOutput

def toPoint : CanonicalOutput → G1
  | .infinity => 0
  | .affine x y h => ofAffine x y h

def ofPoint : G1 → CanonicalOutput
  | .zero => .infinity
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y h =>
      let xCanonical : CanonicalFq := ⟨x.val, x.val_lt⟩
      let yCanonical : CanonicalFq := ⟨y.val, y.val_lt⟩
      .affine xCanonical yCanonical (by
        apply (onCurve_iff_nonsingular xCanonical yCanonical).mpr
        simpa [xCanonical, yCanonical, ZMod.natCast_zmod_val] using h)

@[simp] theorem toPoint_ofPoint (point : G1) :
    toPoint (ofPoint point) = point := by
  cases point with
  | zero => rfl
  | @some x y h =>
      simp only [ofPoint, toPoint, ofAffine]
      congr
      · exact ZMod.natCast_zmod_val x
      · exact ZMod.natCast_zmod_val y

@[simp] theorem ofPoint_toPoint (output : CanonicalOutput) :
    ofPoint (toPoint output) = output := by
  cases output with
  | infinity => rfl
  | affine x y h =>
      simp only [toPoint, ofAffine, ofPoint]
      congr
      · apply Fin.ext
        change ((x.val : Fq).val) = x.val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]
      · apply Fin.ext
        change ((y.val : Fq).val) = y.val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt y.isLt]

def pointEquiv : CanonicalOutput ≃ G1 where
  toFun := toPoint
  invFun := ofPoint
  left_inv := ofPoint_toPoint
  right_inv := toPoint_ofPoint

end CanonicalOutput

/-- The concrete protected profile, with a unique executable output carrier. -/
def bn254 : Profile where
  G1 := G1
  addCommGroup := inferInstance
  Output := CanonicalOutput
  outputEquiv := CanonicalOutput.pointEquiv
  AffineWitness := OnCurve
  affinePoint := ofAffine

end BN254

end GarblingPrize.Protected
