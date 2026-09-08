import Blake3Prize.Migration.Legacy.Reference

namespace Blake3Prize.Protected.Legacy

abbrev OutputIndex := Fin 256
abbrev Label := Vector UInt8 32
abbrev InputLabelPairs := InputIndex → Bool → Label
abbrev OutputLabelPairs := OutputIndex → Bool → Label
abbrev ActiveInputLabels := Vector Label 512
abbrev ActiveOutputLabels := Vector Label 256

def activeInput (pairs : InputLabelPairs) (input : Input) : ActiveInputLabels :=
  Vector.ofFn fun i => pairs i (inputBit input i)

def activeOutput (pairs : OutputLabelPairs) (output : Output) : ActiveOutputLabels :=
  Vector.ofFn fun i => pairs i (output[i].val = 1)

/-- No correlation or selector-bit convention is imposed on external pairs. -/
def DistinctPairs {n : Nat} (pairs : Fin n → Bool → Label) : Prop :=
  ∀ i, pairs i false ≠ pairs i true

end Blake3Prize.Protected.Legacy
