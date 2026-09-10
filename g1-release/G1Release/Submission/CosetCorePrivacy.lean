import G1Release.Submission.CosetSlots

namespace G1Release.Submission.CosetCorePrivacy

/-! Offset transport preserves each selected group output. The four-opening
quotient equivalence then transports each independent K state. Their skew
product is a finite bijection on the entire constrained core randomness. -/

open G1Release.Math
open G1Release.Protected
open GLVDigits (Hidden offsetAt digitAt)
open CosetSlots (bitsFor)
open CosetScheme
open CosetCoordinates FourAffineQuotient
open CosetRandomness (randomnessProdEquiv randomnessLaw)
open MeasureTheory ProbabilityTheory

abbrev Word := BN254.Fq

noncomputable def stateChange (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91) : Equiv.Perm (State K) :=
  stateEquiv (CosetGLV.mapBase (offsetAt offsets index) (digitAt source index))
    (CosetGLV.mapBase (offsetAt (GLVDigits.targetOffsets input source target hequal offsets)
      index) (digitAt target index)) (C (input.val.1.val : Word))
    (CosetGLV.mapBase_denominator_ne_zero _ _ input)
    (CosetGLV.mapBase_denominator_ne_zero _ _ input)

noncomputable def randomnessEquiv (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    Randomness source ≃ Randomness target :=
  (randomnessProdEquiv source).trans
    ((Equiv.prodCongrRight (fun offsets => Equiv.piCongrRight (fun index =>
        stateChange input source target hequal offsets index))).trans
      ((Equiv.prodCongr (GLVOffsetFamily.equiv input source target hequal) (Equiv.refl _)).trans
        (randomnessProdEquiv target).symm))

noncomputable def targetRandomness (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (randomness : Randomness source) : Randomness target :=
  randomnessEquiv input source target hequal randomness

theorem randomnessEquiv_measurePreserving (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    MeasurePreserving (targetRandomness input source target hequal)
      (randomnessLaw source) (randomnessLaw target) :=
  FiniteProbability.uniform_equiv (randomnessEquiv input source target hequal)

theorem opened_preserved (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (randomness : Randomness source) (index : Fin 91) :
    opened (mapBase target (targetRandomness input source target hequal randomness) index)
        ((targetRandomness input source target hequal randomness).states index)
        (C (input.val.1.val : Word)) (C (input.val.2.val : Word)) =
      opened (mapBase source randomness index) (randomness.states index)
        (C (input.val.1.val : Word)) (C (input.val.2.val : Word)) := by
  exact opened_stateEquiv _ _ _ _ _ _
    (CosetGLV.mapBase_value_preserved input source target hequal randomness.offsets index)
    (randomness.states index)

theorem params_preserved (input : Input) (source target : Hidden)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (randomness : Randomness source) (index : Fin 91) (kind : CosetHintMap.TableKind) :
    (mapParams source randomness index kind).coefficient *
        AffineTable.decodeBits (bitsFor kind input) +
      (mapParams source randomness index kind).constant =
      (mapParams target (targetRandomness input source target hequal randomness) index kind).coefficient *
        AffineTable.decodeBits (bitsFor kind input) +
      (mapParams target (targetRandomness input source target hequal randomness) index kind).constant := by
  have hb : AffineTable.decodeBits (bitsFor kind input) =
      CosetHintMap.inputFor kind (input.val.1.val : Word) (input.val.2.val : Word) := by
    fin_cases kind <;> simp [bitsFor, CosetHintMap.inputFor,
      Scheme.decodeBits_xBits, Scheme.decodeBits_yBits]
  rw [hb]
  unfold mapParams
  rw [CosetHintMap.params_opened, CosetHintMap.params_opened, opened_preserved]

end G1Release.Submission.CosetCorePrivacy
