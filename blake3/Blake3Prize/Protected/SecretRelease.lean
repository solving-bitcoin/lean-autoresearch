import Blake3Prize.Protected.Core

namespace Blake3Prize.Protected.SecretRelease

/-- Construction-independent public observation. The message and therefore
its digest may be known. Giving the selected output labels for free makes
secrecy independent of the cost of honest evaluation. -/
structure View where
  inputValue : Input
  artifact : ByteArray
  inputs : ActiveInputLabels
  outputs : ActiveOutputLabels

/-- Indices 0..511 select opposite input labels; 512..767 select opposite
output labels. Guessing any one of the 768 labels is enough to win. -/
abbrev Guess := Fin 768 × Label

def oppositeLabel (inputs : InputLabelPairs) (outputs : OutputLabelPairs)
    (input : Input) (index : Fin 768) : Label :=
  if h : index.val < 512 then
    let i : InputIndex := ⟨index.val, h⟩
    inputs i (!(inputBit input i))
  else
    let i : OutputIndex := ⟨index.val - 512, by omega⟩
    outputs i (!((reference input)[i].val = 1))

/-- The same winning rule is used by every reviewed proof profile. It does
not mention circuits, cryptographic primitives, oracle models, or backends. -/
def Wins (inputs : InputLabelPairs) (outputs : OutputLabelPairs)
    (input : Input) (guess : Guess) : Prop :=
  guess.2 = oppositeLabel inputs outputs input guess.1

end Blake3Prize.Protected.SecretRelease
