import GarblingPrize.Submission.CosetOracleLaw

namespace GarblingPrize.Submission.CosetRowLaw

open GarblingPrize.Protected
open GLVCompactScheme (Hidden Input Profile)
open CosetScheme CosetOracleLaw
open CosetRandomness (randomnessLaw)
open GLVHintRowLaw (Rows rowsLaw joinRows joinRows_law rowCoins rowPairs)
open MeasureTheory ProbabilityTheory

def derivedState (hidden : Hidden) (state : HiddenState) : Randomness hidden × Rows :=
  (randomnessFromOracle hidden state.internalOracle,
    joinRows (coinsFromOracle state.internalOracle, state.pairs))

theorem derivedState_law (hidden : Hidden) :
    MeasurePreserving (derivedState hidden) hiddenStateLaw
      ((randomnessLaw hidden).prod rowsLaw) := by
  have hstate : MeasurePreserving HiddenState.measurableEquiv hiddenStateLaw
      (internalOracleLaw.prod labelPairsLaw) := by
    unfold hiddenStateLaw
    exact (HiddenState.measurableEquiv.symm.measurable
      |>.measurePreserving (internalOracleLaw.prod labelPairsLaw)).symm
        HiddenState.measurableEquiv.symm
  have horacle := (oracleState_law hidden).prod (MeasurePreserving.id labelPairsLaw)
  have hassoc := measurePreserving_prodAssoc (randomnessLaw hidden) coinsLaw labelPairsLaw
  have hrows := (MeasurePreserving.id (randomnessLaw hidden)).prod joinRows_law
  exact hrows.comp (hassoc.comp (horacle.comp hstate))

end GarblingPrize.Submission.CosetRowLaw
