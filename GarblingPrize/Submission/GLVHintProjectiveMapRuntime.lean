import GarblingPrize.Submission.GLVHintProjectiveMap
import GarblingPrize.Submission.RuntimeG1

namespace GarblingPrize.Submission.GLVHintProjectiveMapRuntime

open GarblingPrize.Protected

abbrev Word := GLVHintProjectiveMap.Word
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

def evaluate (mapIndex : Nat) (artifact : GLVHintProjectiveMap.Artifact)
    (x y : Word) (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (xLabels yLabels : Fin IdealAffineTable.tableWidth → Label) :
    Except EvalError Point :=
  finish (GLVHintProjectiveMap.evaluate mapIndex artifact x y xBits yBits
    xLabels yLabels)

theorem evaluate_garble (mapIndex : Nat)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : GLVHintProjectiveMap.Hidden)
    (coins : GLVHintProjectiveMap.TableKind → HintAffineTable.RowIndex → HintAffineTable.Coin)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (hcurve : IdealAffineTable.decodeBits yBits ^ 2 =
      IdealAffineTable.decodeBits xBits ^ 3 + 3) :
    evaluate mapIndex
        (GLVHintProjectiveMap.garble mapIndex xPairs yPairs hidden coins)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      normalizeCoordinates
        (ProjectiveMap.polynomial hidden.coefficients
          (IdealAffineTable.decodeBits xBits)
          (IdealAffineTable.decodeBits yBits)) := by
  calc
    evaluate mapIndex
        (GLVHintProjectiveMap.garble mapIndex xPairs yPairs hidden coins)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      finish (some (ProjectiveMap.polynomial hidden.coefficients
        (IdealAffineTable.decodeBits xBits)
        (IdealAffineTable.decodeBits yBits))) :=
        congrArg finish
          (GLVHintProjectiveMap.evaluate_garble mapIndex xPairs yPairs hidden coins
            xBits yBits hcurve)
    _ = _ := finish_some _

end GarblingPrize.Submission.GLVHintProjectiveMapRuntime
