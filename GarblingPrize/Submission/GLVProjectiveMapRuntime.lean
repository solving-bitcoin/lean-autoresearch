import GarblingPrize.Submission.GLVProjectiveMap
import GarblingPrize.Submission.RuntimeG1

namespace GarblingPrize.Submission.GLVProjectiveMapRuntime

open GarblingPrize.Protected

abbrev Word := GLVProjectiveMap.Word
abbrev Point := RuntimeG1.Point

def normalizeCoordinates (coordinates : ProjectiveMap.Coordinates Word) :
    Except EvalError Point :=
  RuntimeG1.normalize
    { x := coordinates.x, y := coordinates.y, z := coordinates.z }

def finish : Option (ProjectiveMap.Coordinates Word) → Except EvalError Point
  | none => .error .invalidLabels
  | some coordinates => normalizeCoordinates coordinates

@[simp] theorem finish_some (coordinates : ProjectiveMap.Coordinates Word) :
    finish (some coordinates) = normalizeCoordinates coordinates := rfl

def evaluate (mapIndex : Nat) (artifact : GLVProjectiveMap.Artifact)
    (x y : Word) (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (xLabels yLabels : Fin IdealAffineTable.tableWidth → Label) :
    Except EvalError Point :=
  finish (GLVProjectiveMap.evaluate mapIndex artifact x y xBits yBits
    xLabels yLabels)

theorem evaluate_garble (mapIndex : Nat)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : GLVProjectiveMap.Hidden)
    (masks : (kind : GLVProjectiveMap.TableKind) →
      IdealAffineTable.MaskFiber (hidden.params kind).constant)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (hcurve : IdealAffineTable.decodeBits yBits ^ 2 =
      IdealAffineTable.decodeBits xBits ^ 3 + 3) :
    evaluate mapIndex
        (GLVProjectiveMap.garble mapIndex xPairs yPairs hidden masks)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      normalizeCoordinates
        (ProjectiveMap.polynomial hidden.coefficients
          (IdealAffineTable.decodeBits xBits)
          (IdealAffineTable.decodeBits yBits)) := by
  calc
    evaluate mapIndex
        (GLVProjectiveMap.garble mapIndex xPairs yPairs hidden masks)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      finish (some (ProjectiveMap.polynomial hidden.coefficients
        (IdealAffineTable.decodeBits xBits)
        (IdealAffineTable.decodeBits yBits))) :=
        congrArg finish
          (GLVProjectiveMap.evaluate_garble mapIndex xPairs yPairs hidden masks
            xBits yBits hcurve)
    _ = _ := finish_some _

end GarblingPrize.Submission.GLVProjectiveMapRuntime
