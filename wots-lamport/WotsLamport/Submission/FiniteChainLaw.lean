import WotsLamport.Submission.OracleOverlay
import WotsLamport.Submission.CommonOracleDomain
import WotsLamport.Submission.UniformGoodFiber

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

variable (inputs : Finset OracleInput)
  (contains : ∀ node : Label, oracleInput (ByteArray.mk node.toArray) ∈ inputs)

def finiteChainAddress (tape : ChainTape) (edge : ChainEdge) : inputs :=
  ⟨oracleInput (ByteArray.mk (tape edge.val).toArray), contains _⟩

noncomputable def programFiniteChain (tape : ChainTape) (baseline : inputs → Label) : inputs → Label :=
  overlayOracle (finiteChainAddress inputs contains tape) (fun edge => tape (edgeNext edge)) baseline

theorem finiteChainAddress_injective (tape : ChainTape) (distinct : Function.Injective tape) :
    Function.Injective (finiteChainAddress inputs contains tape) := by
  intro a b he
  apply chain_address_injective tape distinct
  have hi := congrArg Subtype.val he
  -- oracleInput is an exact byte representation, with no digesting.
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact (List.map_inj_right (fun x y h => UInt8.toFin_inj.mp h)).mp hi

theorem programFiniteChain_consistent (tape : ChainTape) (distinct : Function.Injective tape)
    (baseline : inputs → Label) :
    TapeConsistent (ROM.hash (extendOracleTable inputs
      (programFiniteChain inputs contains tape baseline))) tape := by
  intro edge
  change extendOracleTable inputs (programFiniteChain inputs contains tape baseline)
    (oracleInput (ByteArray.mk (tape edge.val).toArray)) = _
  rw [extendOracleTable, dif_pos (contains _)]
  exact overlayOracle_at _ _ baseline (finiteChainAddress_injective inputs contains tape distinct) edge

abbrev FiniteChainIdeal := ChainTape × (inputs → Label)
abbrev FiniteChainReal := Keys × (inputs → Label)

noncomputable def finiteChainProgram (sample : FiniteChainIdeal inputs) : FiniteChainReal inputs :=
  (tapeKeys sample.1, programFiniteChain inputs contains sample.1 sample.2)

def finiteChainRealTape (sample : FiniteChainReal inputs) : ChainTape :=
  actualChainTape (ROM.hash (extendOracleTable inputs sample.2)) sample.1

theorem finiteChainProgram_tape (sample : FiniteChainIdeal inputs)
    (distinct : Function.Injective sample.1) :
    finiteChainRealTape inputs (finiteChainProgram inputs contains sample) = sample.1 := by
  exact (consistent_tape_unique _ _ sample.1 rfl
    (programFiniteChain_consistent inputs contains sample.1 distinct sample.2)).symm

abbrev FiniteChainFiber (target : FiniteChainReal inputs) :=
  {sample : FiniteChainIdeal inputs // Function.Injective sample.1 ∧
    finiteChainProgram inputs contains sample = target}

theorem finiteChainFiber_tape (target : FiniteChainReal inputs)
    (sample : FiniteChainFiber inputs contains target) :
    sample.val.1 = finiteChainRealTape inputs target := by
  rw [← sample.property.2]
  exact (finiteChainProgram_tape inputs contains sample.val sample.property.1).symm

noncomputable def finiteChainFiberEquiv (target : FiniteChainReal inputs)
    (distinct : Function.Injective (finiteChainRealTape inputs target)) :
    FiniteChainFiber inputs contains target ≃
      {baseline : inputs → Label //
        programFiniteChain inputs contains (finiteChainRealTape inputs target) baseline = target.2} where
  toFun sample := ⟨sample.val.2, by
    rw [← finiteChainFiber_tape inputs contains target sample]
    exact congrArg Prod.snd sample.property.2⟩
  invFun baseline := ⟨(finiteChainRealTape inputs target, baseline.val), distinct,
    Prod.ext rfl baseline.property⟩
  left_inv sample := by
    apply Subtype.ext
    exact Prod.ext (finiteChainFiber_tape inputs contains target sample).symm rfl
  right_inv baseline := by apply Subtype.ext; rfl

/-- Exact joint key/table fibers on a fixed finite oracle domain. The domain
contains all chain inputs; it is independent of the sampled secrets. -/
theorem finiteChainProgram_fiber_card (target : FiniteChainReal inputs)
    (distinct : Function.Injective (finiteChainRealTape inputs target)) :
    Nat.card (FiniteChainFiber inputs contains target) = (2^256)^989 := by
  classical
  letI := Fintype.ofFinite Label
  let tape := finiteChainRealTape inputs target
  let address := finiteChainAddress inputs contains tape
  have consistent := actualChainTape_consistent
    (ROM.hash (extendOracleTable inputs target.2)) target.1
  have answers : target.2 ∘ address = fun edge => tape (edgeNext edge) := by
    funext edge
    have he := consistent edge
    change extendOracleTable inputs target.2
      (oracleInput (ByteArray.mk (tape edge.val).toArray)) = _ at he
    rw [extendOracleTable, dif_pos (contains _)] at he
    exact he
  have labelCard : Fintype.card Label = 2^256 := by rw [bytes_card]; norm_num
  rw [Nat.card_congr (finiteChainFiberEquiv inputs contains target distinct)]
  have hc := overlay_fiber_card address
    (finiteChainAddress_injective inputs contains tape distinct) target.2
  simpa only [answers, programFiniteChain, address, tape, chainEdge_card, labelCard] using hc

local instance : MeasurableSpace Keys := ⊤

/-- The collision-free ideal tape and programmed oracle have precisely the
real joint key/oracle law restricted to collision-free actual chains. This
normalizes the finite fibers; it does not yet program mask or label queries. -/
theorem finiteChainProgram_good_law :
    ((uniformOn (Set.univ : Set (FiniteChainIdeal inputs))).restrict
      {sample | Function.Injective sample.1}).map (finiteChainProgram inputs contains) =
    (uniformOn (Set.univ : Set (FiniteChainReal inputs))).restrict
      {sample | Function.Injective (finiteChainRealTape inputs sample)} := by
  classical
  letI := Fintype.ofFinite Label
  have labelCard : Fintype.card Label = 2^256 := by rw [bytes_card]; norm_num
  apply uniform_good_fiber_law (finiteChainProgram inputs contains)
    {sample | Function.Injective sample.1}
    {sample | Function.Injective (finiteChainRealTape inputs sample)} ((2^256)^989)
    (pow_ne_zero _ (pow_ne_zero _ (by decide)))
  · intro sample distinct
    change Function.Injective (finiteChainRealTape inputs (finiteChainProgram inputs contains sample))
    rw [finiteChainProgram_tape inputs contains sample distinct]
    exact distinct
  · intro target distinct
    exact finiteChainProgram_fiber_card inputs contains target distinct
  · simp only [FiniteChainIdeal, FiniteChainReal, ChainTape, Keys,
      Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, chainPosition_card, labelCard]
    rw [show (1056 : Nat) = 989+67 from rfl, pow_add, mul_assoc]

/-- The actual finite joint key/oracle law and the independently sampled tape
programming law differ on any output event by at most the tape collision
bound. This comparison still excludes the later masks and commitments. -/
theorem finiteChainProgram_event_bounds (event : Set (FiniteChainReal inputs)) :
    uniformOn (Set.univ : Set (FiniteChainIdeal inputs))
        ((finiteChainProgram inputs contains) ⁻¹' event) ≤
      uniformOn (Set.univ : Set (FiniteChainReal inputs)) event +
        (1056 : ENNReal)^2 / 2^256 ∧
    uniformOn (Set.univ : Set (FiniteChainReal inputs)) event ≤
      uniformOn (Set.univ : Set (FiniteChainIdeal inputs))
        ((finiteChainProgram inputs contains) ⁻¹' event) +
        (1056 : ENNReal)^2 / 2^256 := by
  classical
  letI := Fintype.ofFinite Label
  have bad : uniformOn (Set.univ : Set (FiniteChainIdeal inputs))
      {sample | Function.Injective sample.1}ᶜ ≤ (1056 : ENNReal)^2 / 2^256 := by
    change uniformOn (Set.univ : Set (ChainTape × (inputs → Label)))
      ({tape | ¬Function.Injective tape} ×ˢ Set.univ) ≤ _
    rw [uniform_product, Measure.prod_prod, measure_univ, mul_one]
    exact uniform_chainTape_collision_bound
  have bounds := good_law_event_bounds
    (uniformOn (Set.univ : Set (FiniteChainIdeal inputs)))
    (uniformOn (Set.univ : Set (FiniteChainReal inputs)))
    (finiteChainProgram inputs contains) _ _ (finiteChainProgram_good_law inputs contains) event
  exact ⟨bounds.1.trans (add_le_add_left bad _), bounds.2.trans (add_le_add_left bad _)⟩

end WotsLamport.Submission
