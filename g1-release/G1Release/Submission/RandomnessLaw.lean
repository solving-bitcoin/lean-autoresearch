import G1Release.Submission.RandomnessCoupling
import G1Release.Submission.FiniteProbability

namespace G1Release.Submission.Randomized
open GarblingPrize.Protected G1Release.Protected MeasureTheory ProbabilityTheory

private def pointCode : BN254.G1 → Option (BN254.Fq × BN254.Fq)
  | .zero => none
  | .some x y _ => some (x, y)

private theorem pointCode_injective : Function.Injective pointCode := by
  intro left right hequal
  cases left <;> cases right <;> simpa [pointCode] using hequal

instance : Finite BN254.G1 :=
  Finite.of_injective pointCode pointCode_injective

private def chainMasksCode (masks : ProjectiveMap.ChainMasks Word) :
    Word × Word × Word × Word × Word × Word × Word × Word :=
  (masks.shared, masks.xCross, masks.xOuter, masks.yCubic,
    masks.yQuadratic, masks.zSquare, masks.zCross, masks.zLinear)

private theorem chainMasksCode_injective :
    Function.Injective chainMasksCode := by
  intro left right hequal
  apply ProjectiveMap.ChainMasks.ext <;>
    simp [chainMasksCode] at hequal <;> aesop

instance : Finite (ProjectiveMap.ChainMasks Word) :=
  Finite.of_injective chainMasksCode chainMasksCode_injective

private def offsetCode (hidden : Hidden)
    (offsets : OffsetFamily.Fiber hidden) : Fin 161 → BN254.G1 :=
  fun index => Scheme.offsetAt offsets index

private theorem offsetCode_injective (hidden : Hidden) :
    Function.Injective (offsetCode hidden) := by
  intro left right hequal
  apply OffsetFamily.Fiber.ext
  rw [← Scheme.map_finRange_offsetAt hidden left,
    ← Scheme.map_finRange_offsetAt hidden right]
  exact congrArg (fun values => (List.finRange 161).map values) hequal

instance (hidden : Hidden) : Finite (OffsetFamily.Fiber hidden) :=
  Finite.of_injective (offsetCode hidden) (offsetCode_injective hidden)


private def randomCode (hidden : Hidden) (random : Randomness hidden) :=
  (random.offsets, random.scales, random.chains, random.tableMasks)

private theorem randomCode_injective (hidden : Hidden) :
    Function.Injective (randomCode hidden) := by
  intro a b h
  have h' : a.offsets = b.offsets ∧ a.scales = b.scales ∧
      a.chains = b.chains ∧ a.tableMasks = b.tableMasks := by
    simpa [randomCode, Prod.mk.injEq] using h
  exact Randomness.ext a b h'.1 h'.2.1 h'.2.2.1 h'.2.2.2

instance (hidden : Hidden) : Finite (Randomness hidden) :=
  Finite.of_injective (randomCode hidden) (randomCode_injective hidden)

instance (hidden : Hidden) : MeasurableSpace (Randomness hidden) := ⊤
instance (hidden : Hidden) : DiscreteMeasurableSpace (Randomness hidden) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

noncomputable def idealLaw (hidden : Hidden) : Measure (Randomness hidden) :=
  uniformOn Set.univ

/-- The algebraic map is measure preserving for ideal uniformly sampled
arithmetic randomness. The finite-tape approximation is proved separately. -/
theorem randomnessEquiv_measurePreserving (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input) :
    MeasurePreserving (randomnessEquiv input source target hequal)
      (idealLaw source) (idealLaw target) :=
  FiniteProbability.uniform_equiv _

end G1Release.Submission.Randomized
