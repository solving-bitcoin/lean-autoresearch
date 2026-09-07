import Blake3Prize.Submission.RomTableModel

set_option synthInstance.maxHeartbeats 100000

namespace Blake3Prize.Submission.RomTableSecurity
open SecretRelease MeasureTheory ProbabilityTheory RomMixedKeys RomMixedGuessing RomTableModel

variable {Slot V : Type} [Fintype Slot] [MeasurableSpace V]
  [Countable V] [DiscreteMeasurableSpace V]

def realView (model : Model e k Slot) (render : Active e k → (Slot → Label) → V)
    (state : Keys e k × ROM.Oracle) : V :=
  render (selected model state.1) (ciphertexts model state.1 state.2)

def outcome (model : Model e k Slot) (render : Active e k → (Slot → Label) → V)
    (adversary : V → Program (Index e k × Label)) (state : Keys e k × ROM.Oracle) :
    Index e k × Label := ROM.run (ROM.hash state.2) (adversary (realView model render state))

def event (model : Model e k Slot) (render : Active e k → (Slot → Label) → V)
    (adversary : V → Program (Index e k × Label)) : Set (Keys e k × ROM.Oracle) :=
  {state | key state.1 (outcome model render adversary state).1
      (!(bit model.externalBits model.internalBits (outcome model render adversary state).1)) =
    (outcome model render adversary state).2}

theorem view_measurable (model : Model e k Slot) (render : Active e k → (Slot → Label) → V) :
    Measurable (realView model render) := by
  apply measurable_from_prod_countable_right
  intro keys
  apply (Measurable.of_discrete : Measurable (render (selected model keys))).comp
  exact measurable_pi_lambda _ fun slot =>
    (Measurable.of_discrete : Measurable (RomBytes.xor (model.payload keys slot))).comp
      (measurable_pi_apply (model.address keys slot))

theorem outcome_measurable (model : Model e k Slot) (render : Active e k → (Slot → Label) → V)
    (adversary : V → Program (Index e k × Label)) : Measurable (outcome model render adversary) :=
  (RomMeasurable.run_variable_measurable adversary).comp
    ((view_measurable model render).prodMk measurable_snd)

theorem event_measurable (model : Model e k Slot) (render : Active e k → (Slot → Label) → V)
    (adversary : V → Program (Index e k × Label)) : MeasurableSet (event model render adversary) := by
  exact (measurable_fst.prodMk (outcome_measurable model render adversary))
    (MeasurableSet.of_discrete : MeasurableSet {p : Keys e k × (Index e k × Label) |
      key p.1 p.2.1 (!(bit model.externalBits model.internalBits p.2.1)) = p.2.2})

noncomputable def programState (model : Model e k Slot) (state : Keys e k × Extended model) :
    Keys e k × ROM.Oracle := (state.1,programmed model state.1 state.2)

theorem programState_preserving (model : Model e k Slot) :
    MeasurePreserving (programState model)
      ((uniformOn (Set.univ : Set (Keys e k))).prod (RomOracleLaw.law (Address ⊕ Inactive model)))
      ((uniformOn (Set.univ : Set (Keys e k))).prod (RomOracleLaw.law Address)) := by
  classical
  unfold programState
  letI : IsProbabilityMeasure (RomOracleLaw.law (Address ⊕ Inactive model)) :=
    by unfold RomOracleLaw.law; infer_instance
  refine (MeasurePreserving.id (uniformOn (Set.univ : Set (Keys e k)))).skew_product
    (μc := RomOracleLaw.law (Address ⊕ Inactive model)) (μd := RomOracleLaw.law Address)
    (g := fun keys oracle => programmed model keys oracle) ?_ ?_
  · exact measurable_from_prod_countable_right fun keys =>
      (RomOracleLaw.program_preserving (fun s : Inactive model => model.address keys s.val)
        (fun s => model.payload keys s.val)).measurable
  · exact Filter.Eventually.of_forall fun keys =>
      (RomOracleLaw.program_preserving (fun s : Inactive model => model.address keys s.val)
        (fun s => model.payload keys s.val)).map_eq

theorem selected_inverse (model : Model e k Slot) (active : Active e k) (ranks : Ranks e k) :
    selected model ((split model.externalBits model.internalBits).symm (active,ranks)) = active := by
  rw [selected_eq,Equiv.apply_symm_apply]

theorem conditioned_subset (model : Model e k Slot) (render : Active e k → (Slot → Label) → V)
    (active : Active e k) (oracle : Extended model)
    (adversary : V → Program (Index e k × Label)) :
    {ranks : Ranks e k | programState model
      ((split model.externalBits model.internalBits).symm (active,ranks),oracle) ∈
        event model render adversary} ⊆
      guessesEvent active (guesses model (ROM.hash (base oracle))
        (adversary (render active (idealCiphertexts model active oracle)))) := by
  intro ranks hw
  simp only [event,Set.mem_setOf_eq,outcome,programState,realView,
    ciphertexts_programmed,selected_inverse] at hw
  exact win_implies_guesses model active ranks oracle _ hw

/-- The entire real experiment, including arbitrary adaptive local
computation, has at most q oracle guesses plus one final label guess. -/
theorem probability_le (model : Model e k Slot) (render : Active e k → (Slot → Label) → V)
    (adversary : V → Program (Index e k × Label)) (q : Nat) (ha : ROM.Bounded adversary q) :
    ((uniformOn (Set.univ : Set (Keys e k))).prod (RomOracleLaw.law Address))
      (event model render adversary) ≤ (q+1 : ENNReal) / (2^256-1 : Nat) := by
  have hm := programState_preserving model
  have he := event_measurable model render adversary
  rw [← hm.measure_preimage he.nullMeasurableSet]
  apply RomMixedConditional.bound model.externalBits model.internalBits
    (RomOracleLaw.law (Address ⊕ Inactive model)) _ (hm.measurable he)
  intro active oracle
  apply (measure_mono (conditioned_subset model render active oracle adversary)).trans
  apply (guesses_probability_le active _).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast guesses_length model (ROM.hash (base oracle))
    (adversary (render active (idealCiphertexts model active oracle))) q (ha _)

end Blake3Prize.Submission.RomTableSecurity
