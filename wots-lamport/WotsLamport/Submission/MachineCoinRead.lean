import WotsLamport.Submission.MachineHorner

namespace WotsLamport.Submission
open SecretRelease

theorem evaluatePolynomial_mod_fold (coefficients : List Nat) (x : Nat) :
    evaluatePolynomial coefficients x =
      coefficients.foldr (fun a acc => a+x*acc) 0 % prime := by
  induction coefficients with
  | nil => simp [evaluatePolynomial]
  | cons a rest ih =>
    change fadd a (fmul x (evaluatePolynomial rest x)) = _
    rw [ih]
    simp [fadd, fmul, List.foldr_cons, Nat.add_mod, Nat.mul_mod]

/-- Decode only the field residue. Each intermediate value fits UInt32,
avoiding construction of a full 256-bit natural for every coefficient. -/
def readMachineField (bytes : ByteArray) (start length : Nat) : Nat :=
  evaluateMachinePolynomial
    (machineCoefficients ((List.range length).map fun j => bytes[start+j]!.toNat)) 256

theorem readMachineField_eq (bytes : ByteArray) (start length : Nat) :
    readMachineField bytes start length = readLE bytes start length % prime := by
  rw [readMachineField, evaluateMachinePolynomial_eq _ 256 (by decide),
    evaluatePolynomial_mod_fold]
  simp only [List.foldr_map, readLE]

def machinePolynomial (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : List Nat :=
  let id := 2*wire + if value then 1 else 0
  (List.range (threshold value)).map fun degree =>
    if degree = 0 then readLE ⟨label.toArray⟩ (2*limb) 2 else
      readMachineField coins (32 + ((id*16+limb)*1023+degree-1)*32) 32

theorem machinePolynomial_eq (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : machinePolynomial coins label wire limb value =
      polynomial coins label wire limb value := by
  simp only [machinePolynomial, polynomial, readMachineField_eq]

end WotsLamport.Submission
