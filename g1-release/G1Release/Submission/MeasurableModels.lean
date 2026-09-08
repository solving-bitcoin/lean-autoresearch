import G1Release.Submission.ROMTrace

namespace G1Release.Submission.MeasurableModels
open SecretRelease MeasureTheory

instance : Countable ByteArray := by
  apply Function.Injective.countable (f := fun b : ByteArray => b.data.toList.map UInt8.toFin)
  intro a b h
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact (List.map_inj_right (fun _ _ heq => UInt8.toFin_inj.mp heq)).mp h

instance : MeasurableSpace ByteArray := ⊤

instance (c : Challenge) [Countable c.Input] : Countable (View c) := by
  apply Function.Injective.countable (f := fun v : View c => (v.input,v.artifact,v.activeInputs,v.activeOutputs))
  intro a b h
  cases a
  cases b
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl

instance (c : Challenge) : MeasurableSpace (View c) := ⊤

theorem run_variable_measurable {I : Type} [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] [MeasurableSpace α]
    (program : I → Program α) :
    Measurable (fun p : I × ROM.Oracle => ROM.run (ROM.hash p.2) (program p.1)) :=
  measurable_from_prod_countable_right fun i => ROMTrace.run_measurable (program i)

theorem eval_variable_measurable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] [MeasurableSpace α]
    (family : Ω → I → α) (hf : ∀ i, Measurable (fun ω => family ω i))
    (index : Ω → I) (hi : Measurable index) : Measurable (fun ω => family ω (index ω)) := by
  have h : Measurable (fun p : Ω × I => family p.1 p.2) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hi)

theorem hash_variable_measurable {Ω : Type*} [MeasurableSpace Ω]
    (oracle : Ω → ROM.Oracle) (ho : Measurable oracle)
    (query : Ω → ByteArray) (hq : Measurable query) :
    Measurable (fun ω => ROM.hash (oracle ω) (query ω)) :=
  eval_variable_measurable _ (fun q => (ROMTrace.hash_measurable q).comp ho) query hq

end G1Release.Submission.MeasurableModels
