import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Bits
import Mathlib.Data.ZMod.Defs

namespace GarblingPrize.Protected

/-!
# Self-contained BN254 challenge profile boundary

The numerical profile and wire dimensions are fixed here. The concrete
kernel-checked elliptic-curve realization is represented by `BN254.Profile`:
it is protected infrastructure, never candidate-controlled. The active
challenge binds the ranked theorem to the reviewed concrete `BN254.bn254`
value below. Its typed canonical input/output representation is the protected codec
boundary. Native testing uses these typed values before later strict file
codecs.
-/

def baseFieldModulus : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

def scalarFieldModulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

def curveB : Nat := 3
def coordinateWidth : Nat := 256
def coordinateBitCount : Nat := 2 * coordinateWidth
abbrev labelByteCount : Nat := 32

abbrev CanonicalFq := Fin baseFieldModulus
abbrev CanonicalScalar := Fin scalarFieldModulus

namespace BN254

/-- Protected algebraic and canonical-output interpretation of BN254 G1.

Submissions are parameterized by this value; they cannot choose it. The ranked
claim is bound to the concrete `bn254 : Profile` in this protected module. -/
structure Profile where
  G1 : Type
  addCommGroup : AddCommGroup G1
  Output : Type
  outputEquiv : Output ≃ G1
  AffineWitness : CanonicalFq → CanonicalFq → Prop
  affinePoint : ∀ x y, AffineWitness x y → G1

end BN254

end GarblingPrize.Protected
