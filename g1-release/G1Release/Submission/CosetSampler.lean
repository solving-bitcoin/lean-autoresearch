import G1Release.Submission.CosetCorrect
import G1Release.Submission.ProductSampling
import G1Release.Submission.FlatBlock

namespace G1Release.Submission.CosetSampler
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open SecretRelease G1Release.Protected G1Release.Math
open CosetCoordinates

abbrev Hidden := Private
abbrev TableSlot := Fin 91 × Fin 8 × Fin 254
abbrev Coordinate := Fin 90 ⊕ (Fin 91 × Fin 6) ⊕ TableSlot
abbrev Randomness (hidden : Private) := CosetRandomness.Randomness hidden × CosetScheme.Coins
abbrev Samples := CosetRandomness.Samples × CosetScheme.Coins

def coordinateCount : Nat := 90 + 91*6 + 91*8*254
def coinBytes : Nat := coordinateCount * 64

def coordinateIndex : Coordinate → Nat
  | .inl i => i.val
  | .inr (.inl (i,k)) => 90 + 6*i.val + k.val
  | .inr (.inr (i,k,j)) => 636 + (8*i.val + k.val)*254 + j.val

def coordinateSlot (c : Coordinate) : Fin coordinateCount :=
  ⟨coordinateIndex c, by
    rcases c with i | ⟨i,k⟩ | ⟨i,k,j⟩ <;>
      simp only [coordinateIndex, coordinateCount] <;> omega⟩

theorem coordinateSlot_injective : Function.Injective coordinateSlot := by
  intro a b h
  have h := congrArg Fin.val h
  rcases a with i | ⟨i,k⟩ | ⟨i,k,j⟩ <;>
    rcases b with i' | ⟨i',k'⟩ | ⟨i',k',j'⟩
  all_goals simp only [coordinateSlot, coordinateIndex] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · omega
  · omega
  · omega
  · have hi : i = i' := Fin.ext (by omega)
    have hk : k = k' := Fin.ext (by omega)
    subst i'; subst k'; rfl
  · omega
  · omega
  · omega
  · have hi : i = i' := Fin.ext (by omega)
    have hk : k = k' := Fin.ext (by omega)
    have hj : j = j' := Fin.ext (by omega)
    subst i'; subst k'; subst j'; rfl

def rawModulus : Coordinate → Nat
  | .inl _ => scalarFieldModulus
  | .inr (.inl (_, k)) => match k.val with
    | 0 => baseFieldModulus + 1
    | 1 => baseFieldModulus - 1
    | _ => baseFieldModulus
  | .inr (.inr _) => 4 * BinaryFieldHint.modulus

theorem rawModulus_pos (c : Coordinate) : 0 < rawModulus c := by
  rcases c with i | ⟨i,k⟩ | slot
  · norm_num [rawModulus, BoundaryFacts.scalar_modulus]
  · fin_cases k <;> norm_num [rawModulus, baseFieldModulus]
  · norm_num [rawModulus, BinaryFieldHint.modulus, baseFieldModulus]

abbrev RawValues := (c : Coordinate) → Fin (rawModulus c)
instance (c : Coordinate) : Nonempty (Fin (rawModulus c)) := ⟨⟨0,rawModulus_pos c⟩⟩

def samplesFromRaw (raw : RawValues) : Samples :=
  ((fun i => raw (.inl i), fun i =>
    ((raw (.inr (.inl (i,0))), raw (.inr (.inl (i,1)))),
      fun j => raw (.inr (.inl (i,⟨j.val+2,by omega⟩))))),
    fun i k j => raw (.inr (.inr (i,k,j))))

def rawFromSamples (samples : Samples) : RawValues
  | .inl i => samples.1.1 i
  | .inr (.inl (i,⟨0,_⟩)) => (samples.1.2 i).1.1
  | .inr (.inl (i,⟨1,_⟩)) => (samples.1.2 i).1.2
  | .inr (.inl (i,⟨n+2,h⟩)) => (samples.1.2 i).2 ⟨n,by omega⟩
  | .inr (.inr (i,k,j)) => samples.2 i k j

def rawSamplesEquiv : RawValues ≃ Samples where
  toFun := samplesFromRaw
  invFun := rawFromSamples
  left_inv raw := by
    funext c
    rcases c with i | ⟨i,k⟩ | ⟨i,k,j⟩
    · rfl
    · fin_cases k <;> rfl
    · rfl
  right_inv samples := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        apply Prod.ext
        · rfl
        · funext j; fin_cases j <;> rfl
    · rfl

noncomputable def rawRandomnessEquiv (hidden : Private) : RawValues ≃ Randomness hidden :=
  rawSamplesEquiv.trans (Equiv.prodCongr (CosetRandomness.sampleEquiv hidden) (Equiv.refl _))

def sampleCoordinates (coins : SecretRelease.Bytes coinBytes) : RawValues := fun c =>
  ModuloSampling.sample (2^512) (rawModulus c) (rawModulus_pos c)
    (FiniteProbability.bytesFinEquiv 64
      (FiniteProbability.blockEquiv coordinateCount 64 coins (coordinateSlot c)))

def sample (coins : SecretRelease.Bytes coinBytes) (hidden : Private) : Randomness hidden :=
  let values := samplesFromRaw (sampleCoordinates coins)
  (CosetRandomness.randomnessFromSamples hidden values.1, values.2)

theorem sample_eq (coins : SecretRelease.Bytes coinBytes) (hidden : Private) :
    sample coins hidden = rawRandomnessEquiv hidden (sampleCoordinates coins) := by
  have h (values : RawValues) :
      (CosetRandomness.randomnessFromSamples hidden (samplesFromRaw values).1,
        (samplesFromRaw values).2) = rawRandomnessEquiv hidden values := by rfl
  exact h (sampleCoordinates coins)

def scheme : SecretRelease.Scheme challenge := CosetScheme.scheme coinBytes sample

theorem correct : Correct scheme := CosetScheme.correct coinBytes sample

theorem artifactBound : ArtifactBound scheme 5940480 := CosetScheme.artifactBound coinBytes sample

end G1Release.Submission.CosetSampler
