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

/-- The direct reader is the same machine Horner fold for every byte array,
start, length and accumulator, including out-of-bounds default bytes. -/
theorem directFieldLoop_eq (bytes : ByteArray) (start length : Nat) (initial : UInt32) :
    directFieldLoop bytes start length initial =
      machineHorner
        (machineCoefficients ((List.range length).map fun j => bytes[start+j]!.toNat))
        256 initial := by
  induction length generalizing initial with
  | zero => rfl
  | succ length ih =>
    have byteBound : bytes[start+length]!.toNat < prime :=
      (UInt8.toNat_lt_size _).trans (by decide : 256 < prime)
    have byteMod := Nat.mod_eq_of_lt byteBound
    simp only [directFieldLoop, List.range_succ, List.map_append, List.map_singleton,
      machineCoefficients, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      machineHorner, byteMod]
    exact ih _

theorem readDirectField_eq_machine (bytes : ByteArray) (start length : Nat) :
    readDirectField bytes start length = readMachineField bytes start length := by
  unfold readDirectField readMachineField evaluateMachinePolynomial
  have base : (256 : UInt32) = UInt32.ofNat 256 := by decide +kernel
  rw [directFieldLoop_eq, base]

theorem readDirectField_eq (bytes : ByteArray) (start length : Nat) :
    readDirectField bytes start length = readLE bytes start length % prime := by
  rw [readDirectField_eq_machine, readMachineField_eq]

theorem machinePolynomial_eq (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : machinePolynomial coins label wire limb value =
      polynomial coins label wire limb value := by
  simp only [machinePolynomial, polynomial, readMachineField_eq]

end WotsLamport.Submission
