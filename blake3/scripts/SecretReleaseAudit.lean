import SecretReleaseExamples
import Lean

open SecretRelease MeasureTheory ProbabilityTheory

-- The experiment must be a probability law, never a zero-measure shortcut.
theorem secretRelease_law_probability (c : Challenge) (s : Scheme c) :
    IsProbabilityMeasure (ROM.law s) := by
  unfold ROM.law
  infer_instance

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

-- Equal declared leakage must not allow a perfect private-input distinguisher.
theorem secretRelease_rejects_private_leak (c : Challenge) (s : Scheme c)
    (leakage : c.Private → c.Input → ByteArray) (enabled : c.privateLeakage = some leakage)
    (p₀ p₁ : c.Private) (x : c.Input) (same : leakage p₀ x = leakage p₁ x)
    (a : View c → Program Bool) (queries : ROM.Bounded a 0)
    (left : ROM.distinguishEvent s p₀ x a = Set.univ)
    (right : ROM.distinguishEvent s p₁ x a = ∅) : ¬ ROM.FunctionPrivate s := by
  intro secure
  have bound := (secure leakage enabled p₀ p₁ x same 0 (Nat.zero_le _) a queries).2
  rw [left, right, secretRelease_law_univ, measure_empty, zero_add] at bound
  have small : (c.rom.error 0 : ENNReal) < 1 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_lt_one_iff]
    exact_mod_cast c.rom.nontrivial 0 (Nat.zero_le _)
  exact (not_le_of_gt small) bound

-- Withholding is independently checked before either disclosure is present.
theorem secretRelease_rejects_early_release (c : Challenge) (s : Scheme c)
    (wins : Hash → c.Private → c.Input → c.inputs.Keys → c.outputs.Keys → c.Claim → Prop)
    (enabled : c.withholding = some wins) (p : c.Private) (x : c.Input)
    (a : PreReleaseView c → Program c.Claim) (queries : ROM.Bounded a 0)
    (leaks : ∀ ω, ω ∈ ROM.preReleaseEvent s wins p x a) : ¬ ROM.WithholdingSecure s := by
  intro secure
  unfold ROM.WithholdingSecure at secure
  rw [enabled] at secure
  have bound := (secure p x 0 (Nat.zero_le _) a queries).2
  have hevent : ROM.preReleaseEvent s wins p x a = Set.univ := Set.eq_univ_of_forall leaks
  rw [hevent, secretRelease_law_univ] at bound
  have small : (c.rom.error 0 : ENNReal) < 1 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_lt_one_iff]
    exact_mod_cast c.rom.nontrivial 0 (Nat.zero_le _)
  exact (not_le_of_gt small) bound

-- A lossy output channel with constant permitted leakage must compare private
-- values even when their typed reference results differ.
private def redacted : Challenge where
  Private := Vector Bool 1
  Input := Vector Bool 1
  Output := Vector Bool 1
  privateCodec := Codec.bits 1
  inputCodec := Codec.bits 1
  inputs := Lamport (Codec.bits 1)
  outputs := Plain (fun _ => ByteArray.empty)
  reference := fun p _ => p
  Claim := Label
  wins := fun _ _ x ik _ guess => guess = (ik ⟨0, by decide⟩).get (!x[0])
  privateLeakage := some fun _ _ => ByteArray.empty
  rom := Examples.rom128

private def redactedLeak : Scheme redacted where
  Artifact := ByteArray
  randomnessBytes := 0
  garble := fun _ _ (p : Vector Bool 1) _ _ => ⟨#[if p[0] then 1 else 0]⟩
  encode := id
  decode := some
  evaluate := fun _ _ _ _ => some ByteArray.empty

theorem secretRelease_redacted_correct : Correct redactedLeak := by
  intro h coins p ik ok x
  rfl

theorem secretRelease_redacted_rejected : ¬ ROM.FunctionPrivate redactedLeak := by
  apply secretRelease_rejects_private_leak redacted redactedLeak
    (fun _ _ => ByteArray.empty) rfl #v[true] #v[false] #v[false] rfl
    (fun v => pure (v.artifact == (⟨#[1]⟩ : ByteArray)))
  · intro v; trivial
  · ext ω
    change ((⟨#[1]⟩ : ByteArray) == ⟨#[1]⟩) = true ↔ True
    decide
  · ext ω
    change ((⟨#[0]⟩ : ByteArray) == ⟨#[1]⟩) = true ↔ False
    decide

-- A constant-output construction that publishes the selected label is correct,
-- but cannot satisfy a separately requested pre-release withholding goal.
private def constantOutput : Challenge where
  Private := Unit
  Input := Vector Bool 1
  Output := Vector Bool 1
  privateCodec := Codec.unit
  inputCodec := Codec.bits 1
  inputs := Lamport (Codec.bits 1)
  outputs := Lamport (Codec.bits 1)
  reference := fun _ _ => #v[false]
  Claim := ByteArray
  wins := fun _ _ _ _ ok guess => guess = pack [(ok ⟨0, by decide⟩).get true]
  withholding := some fun _ _ _ _ ok guess => guess = pack [(ok ⟨0, by decide⟩).get false]
  rom := Examples.rom128

private def earlyRelease : Scheme constantOutput where
  Artifact := ByteArray
  randomnessBytes := 0
  garble := fun _ _ _ _ ok => pack [(ok ⟨0, by decide⟩).get false]
  encode := id
  decode := some
  evaluate := fun _ artifact _ _ => some artifact

theorem secretRelease_early_correct : Correct earlyRelease := by
  intro h coins p ik ok x
  simp [Scheme.evaluateBytes, Scheme.garbleBytes, earlyRelease, constantOutput,
    Lamport, Codec.bits, List.finRange]

theorem secretRelease_early_rejected : ¬ ROM.WithholdingSecure earlyRelease := by
  apply secretRelease_rejects_early_release constantOutput earlyRelease
    (fun _ _ _ _ ok guess => guess = pack [(ok ⟨0, by decide⟩).get false]) rfl () #v[false]
    (fun v => pure v.artifact)
  · intro v; trivial
  · intro ω; rfl

example : Examples.blake3.inputCodec.width = 512 := rfl
example : Examples.blake3.privateLeakage = none := rfl
example : Examples.blake3.withholding.isSome = true := rfl
example : Examples.blake3.correctness = .exact := rfl
example (keys : Label) : (Preimage id).reveal (fun _ => keys) keys false = ByteArray.empty := rfl
example (keys : Label) : (Preimage id).reveal (fun _ => keys) keys true = pack [keys] := rfl

open Lean Elab Command in
run_cmd liftTermElabM do
  for decl in [``secretRelease_law_probability, ``secretRelease_law_univ,
    ``secretRelease_rejects_leak, ``secretRelease_rejects_private_leak,
    ``secretRelease_rejects_early_release, ``secretRelease_redacted_correct,
    ``secretRelease_redacted_rejected, ``secretRelease_early_correct,
    ``secretRelease_early_rejected,
    ``SecretRelease.Codec.bits, ``SecretRelease.Codec.unit, ``SecretRelease.Codec.checked,
    ``SecretRelease.Examples.rom128, ``SecretRelease.Examples.blake3,
    ``SecretRelease.Examples.privateMap, ``SecretRelease.Certified, ``SecretRelease.SizeAccepted] do
    for ax in ← collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SecretRelease contract has forbidden axiom: {ax}"
  IO.println "PASS: SecretRelease sampling, nonvacuity, examples, and axiom closure"
