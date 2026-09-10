import G1Release.Submission.CosetGLV
import G1Release.Submission.CosetFieldSampling
import G1Release.Submission.GLVSampling

namespace G1Release.Submission.CosetRandomness

/-! Exact oracle coordinates for 90 free offsets and 91 quotient states.
Each quotient state uses one projective direction, one nonzero radius, and
four base-field coordinates for its two additive extension-field masks. -/

open G1Release.Math
open GLVDigits CosetCoordinates CosetFieldSampling
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
  ((Equiv.piCongrRight fun _ => Randomized.generatorEquiv).trans
    GLVSampling.offsetTailEquiv).trans (GLVSampling.offsetsEquiv hidden)

noncomputable def sampleEquiv (hidden : Hidden) : Samples ≃ Randomness hidden :=
  (Equiv.prodCongr (offsetSampleEquiv hidden) (Equiv.piCongrRight fun _ => mapSampleEquiv)).trans
    (randomnessProdEquiv hidden).symm

def randomnessFromSamples (hidden : Hidden) (samples : Samples) : Randomness hidden where
  offsets := GLVSampling.offsetsFromTail hidden
    ⟨List.ofFn (fun i => (samples.1 i).val • Randomized.standardGenerator), List.length_ofFn⟩
  states := fun i => (unitFromSamples (samples.2 i).1, masksFromSamples (samples.2 i).2)

@[simp] theorem randomnessFromSamples_eq (hidden : Hidden) (samples : Samples) :
    randomnessFromSamples hidden samples = sampleEquiv hidden samples := by rfl


end G1Release.Submission.CosetRandomness
