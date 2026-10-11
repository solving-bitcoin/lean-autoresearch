import WotsLamport.Submission.Sharing

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Executable definitions only. Their complete extensional correspondence
is proved in MachineSharing, which the runtime probe must build first. -/
def reduceMachineField (x : UInt32) : UInt32 :=
  let low := x % 65536
  let high := x / 65536
  if low < high then low + 65537 - high else low - high

def machineHorner : List UInt32 → UInt32 → UInt32 → UInt32
  | [], _, initial => initial
  | a :: rest, x, initial => machineHorner rest x (reduceMachineField (a + x * initial))

def machineCoefficients (coefficients : List Nat) : List UInt32 :=
  coefficients.reverse.map fun a => UInt32.ofNat (a % prime)

def evaluateMachinePolynomial (coefficients : List UInt32) (x : Nat) : Nat :=
  (machineHorner coefficients (UInt32.ofNat x) 0).toNat

def readMachineField (bytes : ByteArray) (start length : Nat) : Nat :=
  evaluateMachinePolynomial
    (machineCoefficients ((List.range length).map fun j => bytes[start+j]!.toNat)) 256

def machinePolynomial (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : List Nat :=
  let id := 2*wire + if value then 1 else 0
  (List.range (threshold value)).map fun degree =>
    if degree = 0 then readLE ⟨label.toArray⟩ (2*limb) 2 else
      readMachineField coins (32 + ((id*16+limb)*1023+degree-1)*32) 32

def machineLabelTable (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) : ByteArray :=
  let polys := (List.range 16).map fun limb =>
    machineCoefficients (machinePolynomial coins label i.val limb value)
  concatenate ((slots i value).zipIdx.map fun ((j,k), index) =>
    let point := index+1
    let share := concatenate (polys.map fun p => writeLE 3 (evaluateMachinePolynomial p point))
    xorBytes share (mask h pk nonce i.val value point (chain h k (keys j))))

def machinePrepare (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : ByteArray :=
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  nonce ++ concatenate ((List.finRange 256).map fun i =>
    (ByteArray.mk (commitment h pk nonce i.val false ((labels i).get false)).toArray) ++
    (ByteArray.mk (commitment h pk nonce i.val true ((labels i).get true)).toArray)) ++
  concatenate ((List.finRange 256).map fun i =>
    machineLabelTable h coins pk nonce keys i false ((labels i).get false) ++
    machineLabelTable h coins pk nonce keys i true ((labels i).get true))

def machineConstruction : Construction := ⟨randomnessBytes, machinePrepare, expand⟩

end WotsLamport.Submission
