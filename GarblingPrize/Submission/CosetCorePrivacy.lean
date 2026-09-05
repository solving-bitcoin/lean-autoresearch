import GarblingPrize.Submission.CosetScheme

namespace GarblingPrize.Submission.CosetCorePrivacy

/-! Offset transport preserves each selected group output. The four-opening
quotient equivalence then transports each independent K state. Their skew
product is a finite bijection on the entire constrained core randomness. -/

open GarblingPrize.Protected
open GLVCompactScheme (Hidden Input Profile offsetAt digitAt)
open CosetScheme
open CosetCoordinates FourAffineQuotient
open CosetRandomness (randomnessProdEquiv randomnessLaw)
open MeasureTheory ProbabilityTheory

abbrev Word := BN254.Fq

noncomputable def stateChange (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91) : Equiv.Perm (State K) :=
  stateEquiv (CosetGLV.mapBase (offsetAt offsets index) (digitAt source index))
    (CosetGLV.mapBase (offsetAt (GLVCompactPrivacy.targetOffsets input source target hequal offsets)
      index) (digitAt target index)) (C (input.x.val : Word))
    (CosetGLV.mapBase_denominator_ne_zero _ _ input)
    (CosetGLV.mapBase_denominator_ne_zero _ _ input)

noncomputable def randomnessEquiv (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    Randomness source ≃ Randomness target :=
  (randomnessProdEquiv source).trans
    ((Equiv.prodCongrRight (fun offsets => Equiv.piCongrRight (fun index =>
        stateChange input source target hequal offsets index))).trans
      ((Equiv.prodCongr (GLVOffsetFamily.equiv input source target hequal) (Equiv.refl _)).trans
        (randomnessProdEquiv target).symm))

noncomputable def targetRandomness (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) : Randomness target :=
  randomnessEquiv input source target hequal randomness

theorem randomnessEquiv_measurePreserving (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    MeasurePreserving (targetRandomness input source target hequal)
      (randomnessLaw source) (randomnessLaw target) :=
  measurePreserving_uniformOfFiniteEquiv (randomnessEquiv input source target hequal)

theorem opened_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (index : Fin 91) :
    opened (mapBase target (targetRandomness input source target hequal randomness) index)
        ((targetRandomness input source target hequal randomness).states index)
        (C (input.x.val : Word)) (C (input.y.val : Word)) =
      opened (mapBase source randomness index) (randomness.states index)
        (C (input.x.val : Word)) (C (input.y.val : Word)) := by
  exact opened_stateEquiv _ _ _ _ _ _
    (CosetGLV.mapBase_value_preserved input source target hequal randomness.offsets index)
    (randomness.states index)

theorem params_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (index : Fin 91) (kind : CosetHintMap.TableKind) :
    (mapParams source randomness index kind).coefficient *
        IdealAffineTable.decodeBits (bitsFor kind input) +
      (mapParams source randomness index kind).constant =
      (mapParams target (targetRandomness input source target hequal randomness) index kind).coefficient *
        IdealAffineTable.decodeBits (bitsFor kind input) +
      (mapParams target (targetRandomness input source target hequal randomness) index kind).constant := by
  have hb : IdealAffineTable.decodeBits (bitsFor kind input) =
      CosetHintMap.inputFor kind (input.x.val : Word) (input.y.val : Word) := by
    fin_cases kind <;> simp [bitsFor, CosetHintMap.inputFor,
      GLVCompactScheme.decodeBits_xBits, GLVCompactScheme.decodeBits_yBits]
  rw [hb]
  unfold mapParams
  rw [CosetHintMap.params_opened, CosetHintMap.params_opened, opened_preserved]

end GarblingPrize.Submission.CosetCorePrivacy
