import Blake3Prize.Submission.RomFiniteProbability
import Blake3Prize.Submission.RomBytes

/-! Random-function facts for the protected countable-product ROM.
Injective coordinate selection followed by fixed XOR masks preserves the
ideal random-function law, without a finite-domain/lazy-oracle assumption. -/
namespace Blake3Prize.Submission.RomOracleLaw
open SecretRelease MeasureTheory ProbabilityTheory

noncomputable def law (D : Type*) : Measure (D → Label) :=
  Measure.infinitePi fun _ : D => uniformOn (Set.univ : Set Label)

instance (D : Type*) : IsProbabilityMeasure (law D) := by
  unfold law
  infer_instance

theorem reindex_preserving {D E : Type*} (f : D → E) (hf : Function.Injective f) :
    MeasurePreserving (fun oracle : E → Label => fun d => oracle (f d)) (law E) (law D) := by
  let e := Equiv.ofInjective f hf
  have hr : MeasurePreserving (Set.range f).domRestrict (law E) (law (Set.range f)) :=
    ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _, Measure.infinitePi_map_restrict' _⟩
  have he : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : D => Label) e.symm)
      (law (Set.range f)) (law D) :=
    ⟨by fun_prop, Measure.infinitePi_map_piCongrLeft (X := fun _ : D => Label)
      (fun _ : D => uniformOn (Set.univ : Set Label)) e.symm⟩
  convert he.comp hr using 1
  funext oracle d
  have hh := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : D => Label)
    ((Set.range f).domRestrict oracle) (e d)
  simpa [e, Function.comp_def] using hh.symm

def xorEquiv (mask : Label) : Label ≃ Label where
  toFun value := RomBytes.xor mask value
  invFun value := RomBytes.xor mask value
  left_inv := RomBytes.xor_cancel_left mask
  right_inv := RomBytes.xor_cancel_left mask

theorem xor_preserving {D : Type*} (mask : D → Label) :
    MeasurePreserving (fun oracle : D → Label => fun d => RomBytes.xor (mask d) (oracle d))
      (law D) (law D) := by
  refine ⟨measurable_pi_lambda _ fun d => (Measurable.of_discrete : Measurable (fun value : Label => RomBytes.xor (mask d) value)).comp (measurable_pi_apply d), ?_⟩
  rw [law, Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  congr 1
  funext d
  exact (RomFiniteProbability.uniform_equiv (xorEquiv (mask d))).map_eq

theorem masked_reindex_preserving {D E : Type*} (f : D → E)
    (hf : Function.Injective f) (mask : D → Label) :
    MeasurePreserving (fun oracle : E → Label => fun d => RomBytes.xor (mask d) (oracle (f d)))
      (law E) (law D) :=
  (xor_preserving mask).comp (reindex_preserving f hf)

noncomputable def programmedIndex {D C : Type*} (address : C → D) (query : D) : D ⊕ C := by
  letI : Decidable (∃ c, address c = query) := Classical.propDecidable _
  exact if h : ∃ c, address c = query then .inr (Classical.choose h) else .inl query

theorem programmedIndex_injective {D C : Type*} (address : C → D) :
    Function.Injective (programmedIndex address) := by
  classical
  intro a b h
  unfold programmedIndex at h
  split at h <;> split at h
  · rename_i ha hb
    have hc := Sum.inr.inj h
    exact (Classical.choose_spec ha).symm.trans
      ((congrArg address hc).trans (Classical.choose_spec hb))
  · contradiction
  · contradiction
  · exact Sum.inl.inj h

noncomputable def programmedMask {D C : Type*} (address : C → D) (payload : C → Label)
    (query : D) : Label := by
  letI : Decidable (∃ c, address c = query) := Classical.propDecidable _
  exact if h : ∃ c, address c = query then payload (Classical.choose h) else RomBytes.zero 32

noncomputable def program {D C : Type*} (address : C → D) (payload : C → Label)
    (oracle : D ⊕ C → Label) (query : D) : Label :=
  RomBytes.xor (programmedMask address payload query) (oracle (programmedIndex address query))

/-- Overwriting secret addresses using independent extra coordinates leaves
the real oracle marginal exactly uniform. The extra values can be exposed
as simulated ciphertexts; their correlation with the programmed oracle is
accounted for by the separate first-query argument. -/
theorem program_preserving {D C : Type*} (address : C → D) (payload : C → Label) :
    MeasurePreserving (program address payload) (law (D ⊕ C)) (law D) :=
  masked_reindex_preserving (programmedIndex address)
    (programmedIndex_injective address) (programmedMask address payload)

theorem program_at {D C : Type*} (address : C → D) (ha : Function.Injective address)
    (payload : C → Label) (oracle : D ⊕ C → Label) (c : C) :
    program address payload oracle (address c) = RomBytes.xor (payload c) (oracle (.inr c)) := by
  classical
  have hex : ∃ c', address c' = address c := ⟨c,rfl⟩
  have hc : Classical.choose hex = c := ha (Classical.choose_spec hex)
  simp [program, programmedMask, programmedIndex, hex, hc]

theorem program_outside {D C : Type*} (address : C → D) (payload : C → Label)
    (oracle : D ⊕ C → Label) (query : D) (h : ¬∃ c, address c = query) :
    program address payload oracle query = oracle (.inl query) := by
  simp [program, programmedMask, programmedIndex, h]

end Blake3Prize.Submission.RomOracleLaw
