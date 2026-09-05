import GarblingPrize.Submission.GLVHintScheme
import GarblingPrize.Submission.HintProductLaw
import GarblingPrize.Submission.HintAffineTablePrivacy

namespace GarblingPrize.Submission.GLVHintOracleLaw

/-! The balancing coins use modulus 4p, distinct from every core modulus.
The injection (wire, purpose) ↦ 512*purpose+wire proves independence for the
entire coin process, jointly with the existing constrained GLV randomness. -/

open GarblingPrize.Protected
open GLVCompactScheme GLVCompactOracleLaw GLVHintScheme
open MeasureTheory ProbabilityTheory

abbrev CoinIndex := BitIndex × Purpose
abbrev Coordinate := RawCoordinate ⊕ CoinIndex

def modulus : Coordinate → SamplingModulus
  | .inl coordinate => rawModulus coordinate
  | .inr _ => coinModulus

def purpose : Coordinate → Purpose
  | .inl coordinate => rawPurpose coordinate
  | .inr index => coinPurpose index.1 index.2

def address (coordinate : Coordinate) : InternalAddress :=
  ⟨modulus coordinate, purpose coordinate⟩

theorem coreModulus_ne_coin (coordinate : RawCoordinate) :
    rawModulus coordinate ≠ coinModulus := by
  intro heq
  have h := congrArg SamplingModulus.value heq
  cases coordinate <;>
    norm_num [rawModulus, coinModulus, BinaryFieldHint.modulus,
      baseFieldModulus, scalarFieldModulus] at h

theorem coinPurpose_injective :
    Function.Injective (fun index : CoinIndex => coinPurpose index.1 index.2) := by
  rintro ⟨wire, p⟩ ⟨wire', q⟩ heq
  have hw : wire.val < 512 := wire.isLt
  have hw' : wire'.val < 512 := wire'.isLt
  change 512 * p + wire.val = 512 * q + wire'.val at heq
  have hp : p = q := by
    have hdiv := congrArg (fun n : Nat => n / 512) heq
    simpa [Nat.mul_add_div, Nat.div_eq_of_lt hw, Nat.div_eq_of_lt hw'] using hdiv
  rw [hp] at heq
  have hi : wire = wire' := Fin.ext (Nat.add_left_cancel heq)
  simp [hp, hi]

theorem address_injective : Function.Injective address := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right => exact congrArg Sum.inl (rawAddress_injective heq)
    | inr right => exact False.elim (coreModulus_ne_coin left (congrArg Sigma.fst heq))
  | inr left =>
    cases right with
    | inl right => exact False.elim (coreModulus_ne_coin right (congrArg Sigma.fst heq).symm)
    | inr right =>
      exact congrArg Sum.inr (coinPurpose_injective (congrArg Sigma.snd heq))

abbrev Values := (coordinate : Coordinate) → Fin (modulus coordinate).value

def valuesFromOracle (oracle : InternalOracle) : Values :=
  fun coordinate => oracle (modulus coordinate) (purpose coordinate)

theorem valuesFromOracle_measurable : Measurable valuesFromOracle := by
  apply measurable_pi_lambda
  intro coordinate
  exact (internalOracleLaw_uniform_marginal (modulus coordinate) (purpose coordinate)).measurable

theorem valuesFromOracle_law :
    MeasurePreserving valuesFromOracle internalOracleLaw
      (Measure.infinitePi fun coordinate => internalValueLaw (modulus coordinate)) := by
  refine ⟨valuesFromOracle_measurable, ?_⟩
  have hind : iIndepFun (fun coordinate oracle => valuesFromOracle oracle coordinate)
      internalOracleLaw := internalCoordinates_independent.precomp address_injective
  have hlaw := hind.map_fun_eq_infinitePi_map (fun coordinate =>
    (internalOracleLaw_uniform_marginal (modulus coordinate) (purpose coordinate)).measurable)
  change Measure.map valuesFromOracle internalOracleLaw = _ at hlaw
  rw [hlaw]
  congr 1
  funext coordinate
  exact (internalOracleLaw_uniform_marginal (modulus coordinate) (purpose coordinate)).map_eq

noncomputable def coinLaw : Measure Coin := uniformOn Set.univ
noncomputable def coinsLaw : Measure Coins :=
  Measure.infinitePi fun _ : BitIndex => Measure.infinitePi fun _ : Purpose => coinLaw

instance : IsProbabilityMeasure coinLaw := by unfold coinLaw; infer_instance
instance : IsProbabilityMeasure coinsLaw := by unfold coinsLaw; infer_instance

noncomputable def valuesToState (hidden : Hidden) (values : Values) :
    Randomness hidden × Coins :=
  (rawRandomnessEquiv hidden (fun index => values (.inl index)),
    fun wire purpose => values (.inr (wire, purpose)))

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4096 in
theorem valuesToState_law (hidden : Hidden) :
    MeasurePreserving (valuesToState hidden)
      (Measure.infinitePi fun coordinate => internalValueLaw (modulus coordinate))
      ((randomnessLaw hidden).prod coinsLaw) := by
  have hsplit := HintProductLaw.infinitePi_sum
    (fun coordinate => internalValueLaw (modulus coordinate))
  have hraw : MeasurePreserving (rawRandomnessEquiv hidden)
      (Measure.infinitePi fun coordinate => internalValueLaw (rawModulus coordinate))
      (randomnessLaw hidden) := by
    rw [show (Measure.infinitePi fun coordinate => internalValueLaw (rawModulus coordinate)) =
      uniformOn (Set.univ : Set RawValues) from
        infinitePi_uniform_univ_dependent (fun coordinate => Fin (rawModulus coordinate).value)]
    exact measurePreserving_uniformOfFiniteEquiv (rawRandomnessEquiv hidden)
  have hcoins : MeasurePreserving (MeasurableEquiv.curry BitIndex Purpose Coin)
      (Measure.infinitePi fun _ : CoinIndex => coinLaw) coinsLaw :=
    ⟨by fun_prop, Measure.infinitePi_map_curry (fun _ _ => coinLaw)⟩
  have h := (hraw.prod hcoins).comp hsplit
  have hf : valuesToState hidden =
      Prod.map (rawRandomnessEquiv hidden) (MeasurableEquiv.curry BitIndex Purpose Coin) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun coordinate => Fin (modulus coordinate).value)) := by
    funext values
    apply Prod.ext
    · rfl
    · rfl
  rw [hf]
  exact h

def oracleState (hidden : Hidden) (oracle : InternalOracle) : Randomness hidden × Coins :=
  (randomnessFromOracle hidden oracle, coinsFromOracle oracle)

theorem oracleState_eq (hidden : Hidden) :
    oracleState hidden = valuesToState hidden ∘ valuesFromOracle := by
  funext oracle
  apply Prod.ext
  · exact (rawRandomnessEquiv_rawFromOracle hidden oracle).symm
  · rfl

theorem oracleState_law (hidden : Hidden) :
    MeasurePreserving (oracleState hidden) internalOracleLaw
      ((randomnessLaw hidden).prod coinsLaw) := by
  rw [oracleState_eq]
  exact (valuesToState_law hidden).comp valuesFromOracle_law

end GarblingPrize.Submission.GLVHintOracleLaw
