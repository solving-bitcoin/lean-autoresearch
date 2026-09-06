import SecretReleaseExamples
import Lean

open SecretRelease MeasureTheory ProbabilityTheory

-- The experiment must be a probability law, never a zero-measure shortcut.
theorem secretRelease_law_univ (c : Challenge) (s : Scheme c) :
    ROM.law s Set.univ = 1 := by
  let : MeasurableSpace c.inputs.Keys := ⊤
  let : MeasurableSpace c.outputs.Keys := ⊤
  unfold ROM.law
  exact measure_univ

-- A universally leaking scheme cannot pass even at zero oracle queries.
theorem secretRelease_rejects_leak (c : Challenge) (s : Scheme c)
    (p : c.Private) (x : c.Input) (a : View c → Program c.Claim)
    (queries : ROM.Bounded a 0) (leaks : ∀ ω, ω ∈ ROM.winEvent s p x a) :
    ¬ ROM.ReleaseSecure s := by
  intro secure
  have bound := (secure p x 0 (Nat.zero_le _) a queries).2
  have hevent : ROM.winEvent s p x a = Set.univ := Set.eq_univ_of_forall leaks
  rw [hevent, secretRelease_law_univ] at bound
  have small : (c.rom.error 0 : ENNReal) < 1 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_lt_one_iff]
    exact_mod_cast c.rom.nontrivial 0 (Nat.zero_le _)
  exact (not_le_of_gt small) bound

-- Equal permitted results must not allow a perfect private-input distinguisher.
theorem secretRelease_rejects_private_leak (c : Challenge) (s : Scheme c)
    (enabled : c.hidePrivate = true) (p₀ p₁ : c.Private) (x : c.Input)
    (same : c.reference p₀ x = c.reference p₁ x)
    (a : View c → Program Bool) (queries : ROM.Bounded a 0)
    (left : ROM.distinguishEvent s p₀ x a = Set.univ)
    (right : ROM.distinguishEvent s p₁ x a = ∅) : ¬ ROM.FunctionPrivate s := by
  intro secure
  have bound := (secure enabled p₀ p₁ x same 0 (Nat.zero_le _) a queries).2
  rw [left, right, secretRelease_law_univ, measure_empty, zero_add] at bound
  have small : (c.rom.error 0 : ENNReal) < 1 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_lt_one_iff]
    exact_mod_cast c.rom.nontrivial 0 (Nat.zero_le _)
  exact (not_le_of_gt small) bound

example : Examples.blake3.inputCodec.width = 512 := rfl
example : Examples.blake3.hidePrivate = false := rfl
example : Examples.blake3.correctness = .exact := rfl
example (keys : Label) : (Preimage id).reveal (fun _ => keys) keys false = ByteArray.empty := rfl
example (keys : Label) : (Preimage id).reveal (fun _ => keys) keys true = pack [keys] := rfl

open Lean Elab Command in
run_cmd liftTermElabM do
  for decl in [``secretRelease_law_univ, ``secretRelease_rejects_leak,
    ``secretRelease_rejects_private_leak,
    ``SecretRelease.Codec.bits, ``SecretRelease.Codec.unit, ``SecretRelease.Codec.checked,
    ``SecretRelease.Examples.rom128, ``SecretRelease.Examples.blake3,
    ``SecretRelease.Examples.privateMap, ``SecretRelease.Certified] do
    for ax in ← collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SecretRelease contract has forbidden axiom: {ax}"
  IO.println "PASS: SecretRelease sampling, nonvacuity, examples, and axiom closure"
