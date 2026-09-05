import GarblingPrize.Submission.CosetGLV

namespace GarblingPrize.Submission.CosetRandomness

/-! Exact oracle coordinates for 90 free offsets and 91 quotient states.
Each quotient state uses one projective direction, one nonzero radius, and
four base-field coordinates for its two additive extension-field masks. -/

open GarblingPrize.Protected
open GLVCompactScheme CosetCoordinates CosetFieldSampling
open MeasureTheory ProbabilityTheory

abbrev Word := BN254.Fq
abbrev MapState := FourAffineQuotient.State K

@[ext] structure Randomness (hidden : Hidden) where
  offsets : GLVOffsetFamily.Fiber hidden
  states : Fin 91 → MapState

def randomnessProdEquiv (hidden : Hidden) :
    Randomness hidden ≃ GLVOffsetFamily.Fiber hidden × (Fin 91 → MapState) where
  toFun r := (r.offsets, r.states)
  invFun p := ⟨p.1, p.2⟩

instance (hidden : Hidden) : Finite (Randomness hidden) := (randomnessProdEquiv hidden).finite_iff.mpr inferInstance
instance (hidden : Hidden) : Nonempty (Randomness hidden) :=
  ⟨⟨GLVOffsetFamily.canonical hidden, fun _ => (1, (0, 0))⟩⟩
instance (hidden : Hidden) : MeasurableSpace (Randomness hidden) := ⊤
instance (hidden : Hidden) : DiscreteMeasurableSpace (Randomness hidden) where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top

noncomputable def randomnessLaw (hidden : Hidden) : Measure (Randomness hidden) := uniformOn Set.univ
instance (hidden : Hidden) : IsProbabilityMeasure (randomnessLaw hidden) := by
  unfold randomnessLaw; infer_instance

abbrev MaskSamples := Fin 4 → Fin baseFieldModulus
abbrev Samples := (Fin 90 → Fin scalarFieldModulus) × (Fin 91 → UnitSamples × MaskSamples)

def masksFromSamples (samples : MaskSamples) : K × K :=
  (⟨(samples 0).val, (samples 1).val⟩, ⟨(samples 2).val, (samples 3).val⟩)

def maskSampleEquiv : MaskSamples ≃ K × K where
  toFun := masksFromSamples
  invFun masks := ![⟨masks.1.re.val, masks.1.re.val_lt⟩, ⟨masks.1.im.val, masks.1.im.val_lt⟩,
    ⟨masks.2.re.val, masks.2.re.val_lt⟩, ⟨masks.2.im.val, masks.2.im.val_lt⟩]
  left_inv := by
    intro samples
    funext i
    fin_cases i <;> apply Fin.ext <;> simp [masksFromSamples, ZMod.val_natCast_of_lt]
    all_goals exact Nat.mod_eq_of_lt (samples _).isLt
  right_inv := by
    intro masks
    apply Prod.ext <;> ext <;> simp [masksFromSamples]

noncomputable def mapSampleEquiv : UnitSamples × MaskSamples ≃ MapState :=
  Equiv.prodCongr unitSampleEquiv maskSampleEquiv

noncomputable def offsetSampleEquiv (hidden : Hidden) :
    (Fin 90 → Fin scalarFieldModulus) ≃ GLVOffsetFamily.Fiber hidden :=
  ((Equiv.piCongrRight fun _ => GLVCompactOracleLaw.generatorEquiv).trans
    GLVCompactOracleLaw.offsetTailEquiv).trans (GLVCompactOracleLaw.offsetsEquiv hidden)

noncomputable def sampleEquiv (hidden : Hidden) : Samples ≃ Randomness hidden :=
  (Equiv.prodCongr (offsetSampleEquiv hidden) (Equiv.piCongrRight fun _ => mapSampleEquiv)).trans
    (randomnessProdEquiv hidden).symm

def randomnessFromSamples (hidden : Hidden) (samples : Samples) : Randomness hidden where
  offsets := GLVCompactOracleLaw.offsetsFromTail hidden
    ⟨List.ofFn (fun i => (samples.1 i).val • standardGenerator), List.length_ofFn⟩
  states := fun i => (unitFromSamples (samples.2 i).1, masksFromSamples (samples.2 i).2)

@[simp] theorem randomnessFromSamples_eq (hidden : Hidden) (samples : Samples) :
    randomnessFromSamples hidden samples = sampleEquiv hidden samples := by rfl

private theorem fits {n : Nat} (h : n ≤ 2 ^ 256) : n ≤ 2 ^ 3072 :=
  h.trans (Nat.pow_le_pow_right (by decide) (by decide))

def scalarModulus : SamplingModulus :=
  ⟨scalarFieldModulus, by norm_num [scalarFieldModulus], fits (by norm_num [scalarFieldModulus])⟩
def directionModulus : SamplingModulus :=
  ⟨baseFieldModulus + 1, by omega, fits (by norm_num [baseFieldModulus])⟩
def radiusModulus : SamplingModulus :=
  ⟨baseFieldModulus - 1, by norm_num [baseFieldModulus], fits (by norm_num [baseFieldModulus])⟩
def fieldModulus : SamplingModulus :=
  ⟨baseFieldModulus, by norm_num [baseFieldModulus], fits (by norm_num [baseFieldModulus])⟩

abbrev RawCoordinate := Fin 90 ⊕ (Fin 91 × Fin 6)

def rawModulus : RawCoordinate → SamplingModulus
  | .inl _ => scalarModulus
  | .inr (_, kind) => match kind.val with
    | 0 => directionModulus
    | 1 => radiusModulus
    | _ => fieldModulus

def rawPurpose : RawCoordinate → Purpose
  | .inl index => index.val
  | .inr (index, kind) => 90 + 6 * index.val + kind.val

def rawAddress (coordinate : RawCoordinate) : InternalAddress :=
  ⟨rawModulus coordinate, rawPurpose coordinate⟩

theorem rawPurpose_injective : Function.Injective rawPurpose := by
  intro left right h
  cases left with
  | inl left =>
    cases right with
    | inl right => exact congrArg Sum.inl (Fin.ext h)
    | inr right =>
      have := left.isLt
      change left.val = 90 + 6 * right.1.val + right.2.val at h
      omega
  | inr left =>
    cases right with
    | inl right =>
      have := right.isLt
      change 90 + 6 * left.1.val + left.2.val = right.val at h
      omega
    | inr right =>
      have hl := left.2.isLt
      have hr := right.2.isLt
      change 90 + 6 * left.1.val + left.2.val = 90 + 6 * right.1.val + right.2.val at h
      have hi : left.1.val = right.1.val := by omega
      have hk : left.2.val = right.2.val := by omega
      exact congrArg Sum.inr (Prod.ext (Fin.ext hi) (Fin.ext hk))

theorem rawAddress_injective : Function.Injective rawAddress :=
  fun _ _ h => rawPurpose_injective (congrArg Sigma.snd h)

abbrev RawValues := (coordinate : RawCoordinate) → Fin (rawModulus coordinate).value

instance (coordinate : RawCoordinate) : Nonempty (Fin (rawModulus coordinate).value) :=
  ⟨⟨0, (rawModulus coordinate).positive⟩⟩

def samplesFromRaw (values : RawValues) : Samples :=
  (fun i => values (.inl i), fun i =>
    ((values (.inr (i, 0)), values (.inr (i, 1))),
      fun j => values (.inr (i, ⟨j.val + 2, by omega⟩))))

def rawFromSamples (samples : Samples) : RawValues
  | .inl i => samples.1 i
  | .inr (i, ⟨0, _⟩) => (samples.2 i).1.1
  | .inr (i, ⟨1, _⟩) => (samples.2 i).1.2
  | .inr (i, ⟨n + 2, h⟩) => (samples.2 i).2 ⟨n, by omega⟩

def rawSampleEquiv : RawValues ≃ Samples where
  toFun := samplesFromRaw
  invFun := rawFromSamples
  left_inv := by
    intro values
    funext c
    cases c with
    | inl i => rfl
    | inr pair => rcases pair with ⟨i, k⟩; fin_cases k <;> rfl
  right_inv := by
    intro samples
    apply Prod.ext
    · rfl
    · funext i
      apply Prod.ext
      · rfl
      · funext j; fin_cases j <;> rfl

def rawFromOracle (oracle : InternalOracle) : RawValues :=
  fun coordinate => oracle (rawModulus coordinate) (rawPurpose coordinate)

def randomnessFromOracle (hidden : Hidden) (oracle : InternalOracle) : Randomness hidden :=
  randomnessFromSamples hidden (samplesFromRaw (rawFromOracle oracle))

noncomputable def rawRandomnessEquiv (hidden : Hidden) : RawValues ≃ Randomness hidden :=
  rawSampleEquiv.trans (sampleEquiv hidden)

@[simp] theorem rawRandomnessEquiv_apply (hidden : Hidden) (values : RawValues) :
    rawRandomnessEquiv hidden values = randomnessFromSamples hidden (samplesFromRaw values) := rfl

theorem rawRandomnessEquiv_law (hidden : Hidden) :
    MeasurePreserving (rawRandomnessEquiv hidden)
      (Measure.infinitePi fun c => internalValueLaw (rawModulus c)) (randomnessLaw hidden) := by
  unfold internalValueLaw randomnessLaw
  rw [GLVCompactOracleLaw.infinitePi_uniform_univ_dependent]
  exact measurePreserving_uniformOfFiniteEquiv _

end GarblingPrize.Submission.CosetRandomness
