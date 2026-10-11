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
theorem readMachineField_eq (bytes : ByteArray) (start length : Nat) :
    readMachineField bytes start length = readLE bytes start length % prime := by
  rw [readMachineField, evaluateMachinePolynomial_eq _ 256 (by decide),
    evaluatePolynomial_mod_fold]
  simp only [List.foldr_map, readLE]

theorem machinePolynomial_eq (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : machinePolynomial coins label wire limb value =
      polynomial coins label wire limb value := by
  simp only [machinePolynomial, polynomial, readMachineField_eq]

end WotsLamport.Submission
