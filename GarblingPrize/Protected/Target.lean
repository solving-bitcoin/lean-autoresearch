import GarblingPrize.Protected.G1
import GarblingPrize.Protected.CodecLemmas
import GarblingPrize.Protected.PrimeCertificates.Base
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn

namespace GarblingPrize.Protected

/-!
# Protected target for `Q + [r]A`

This module fixes the semantic and transcript boundary of the optimization
challenge. It intentionally says nothing about scalar decompositions,
projective-map counts, addition formulae, polynomial factorizations, affine
tables, sharing between digits, or artifact layouts.

The ranked object is the exact `ByteArray` returned by `garbleBytes`. Labels
and the canonical output carrier are protected, so neither can be used as an
unmeasured channel for the hidden map.
-/

/-- A valid finite-affine evaluator input for the protected profile. Infinity
is excluded from the input format. -/
structure AffineInput (profile : BN254.Profile) where
  x : CanonicalFq
  y : CanonicalFq
  onCurve : profile.AffineWitness x y

namespace AffineInput

def point {profile : BN254.Profile} (input : AffineInput profile) : profile.G1 :=
  profile.affinePoint input.x input.y input.onCurve

end AffineInput

/-- Hidden garbler inputs. `Q` already uses the protected unique output
carrier, and `r` is the canonical BN254 scalar representative. -/
structure HiddenInput (profile : BN254.Profile) where
  Q : profile.Output
  r : CanonicalScalar

/-- Exact public meaning of the challenge. -/
def reference (profile : BN254.Profile) (hidden : HiddenInput profile)
    (input : AffineInput profile) : profile.G1 :=
  letI := profile.addCommGroup
  profile.outputEquiv hidden.Q + hidden.r.val • input.point

abbrev BitIndex := Fin coordinateBitCount
/-- One fixed-width pad block returned by an ideal label at a purpose. -/
abbrev SeedLabel := Bytes labelByteCount

/-- Domain-separated table purpose. The protected contract does not bound or
interpret purposes, so candidates remain free to change their architecture. -/
abbrev Purpose := Nat

/-- A positive modulus accepted by the protected internal-randomness oracle.
The 3072-bit ceiling bounds the native sampler while remaining independent of
the BN254-specific construction used by the official submission. -/
structure SamplingModulus where
  value : Nat
  positive : 0 < value
  fits : value ≤ 2 ^ 3072
  deriving DecidableEq

namespace SamplingModulus

private theorem value_injective : Function.Injective SamplingModulus.value := by
  intro left right hequal
  cases left
  cases right
  simp only [SamplingModulus.value] at hequal
  cases hequal
  rfl

instance : Countable SamplingModulus :=
  value_injective.countable

end SamplingModulus

/-- The only non-label randomness interface visible to an accepted scheme.
Each `(modulus, purpose)` coordinate is an ideal uniform residue. -/
abbrev InternalOracle :=
  (modulus : SamplingModulus) → Purpose → Fin modulus.value

namespace InternalOracle

/-- Convenience projection for callers that already have the positivity and
3072-bit-bound proofs for a modulus. -/
def sample (oracle : InternalOracle) (modulus : Nat)
    (positive : 0 < modulus) (fits : modulus ≤ 2 ^ 3072)
    (purpose : Purpose) : Fin modulus :=
  oracle ⟨modulus, positive, fits⟩ purpose

end InternalOracle

/-- Ideal one-transcript label oracle. Each purpose exposes one independent
32-byte pad. This oracle is the primitive of the privacy theorem; no finite-seed
expander or computational security claim is part of the ranked theorem. -/
abbrev Label := Purpose → SeedLabel
/-- One curried ideal pad oracle for every `(wire, bit, purpose)` address. -/
abbrev IdealPads := BitIndex → Bool → Purpose → SeedLabel
abbrev LabelPairs := IdealPads
abbrev ActiveLabels := BitIndex → Label
/-- A flattened address for stating facts about all ideal-pad coordinates. -/
abbrev LabelAddress := (BitIndex × Bool) × Purpose
/-- A flattened address for the protected typed internal oracle. -/
abbrev InternalAddress := Sigma fun _modulus : SamplingModulus => Purpose

open MeasureTheory ProbabilityTheory

private theorem seedLabel_finite : Finite SeedLabel := by
  apply Finite.of_injective
    (fun bytes : SeedLabel => fun index : Fin labelByteCount =>
      (bytes.get index).toFin)
  intro left right hequal
  apply Vector.ext
  intro index hindex
  apply UInt8.ext
  exact Fin.ext_iff.mp (congrFun hequal ⟨index, hindex⟩)

instance : Finite SeedLabel := seedLabel_finite

/-- Pads carry the discrete measurable structure. Function spaces built from
them retain the product σ-algebra rather than becoming discrete. -/
instance : MeasurableSpace SeedLabel := ⊤

/-- The ideal uniform law of one 32-byte label pad. -/
noncomputable def seedLabelLaw : Measure SeedLabel :=
  uniformOn Set.univ

instance : IsProbabilityMeasure seedLabelLaw := by
  unfold seedLabelLaw
  infer_instance

/-- The independent countable product law on every `(wire, bit, purpose)` pad
coordinate. `Purpose := Nat` remains unbounded. -/
noncomputable def labelPairsLaw : Measure LabelPairs :=
  Measure.infinitePi fun _ : BitIndex =>
    Measure.infinitePi fun _ : Bool =>
      Measure.infinitePi fun _ : Purpose => seedLabelLaw

instance : IsProbabilityMeasure labelPairsLaw := by
  unfold labelPairsLaw
  infer_instance

/-- The discrete uniform law at one protected internal-oracle coordinate. -/
noncomputable def internalValueLaw (modulus : SamplingModulus) :
    Measure (Fin modulus.value) :=
  uniformOn Set.univ

instance (modulus : SamplingModulus) :
    IsProbabilityMeasure (internalValueLaw modulus) := by
  letI : Nonempty (Fin modulus.value) :=
    ⟨⟨0, modulus.positive⟩⟩
  unfold internalValueLaw
  infer_instance

/-- The independent ideal law on every typed internal-randomness coordinate. -/
noncomputable def internalOracleLaw : Measure InternalOracle :=
  Measure.infinitePi fun modulus : SamplingModulus =>
    Measure.infinitePi fun _purpose : Purpose => internalValueLaw modulus

instance : IsProbabilityMeasure internalOracleLaw := by
  unfold internalOracleLaw
  infer_instance

/-- Evaluation at one ideal-pad address has the uniform 32-byte marginal. -/
theorem labelPairsLaw_uniform_marginal (wire : BitIndex) (bit : Bool)
    (purpose : Purpose) :
    MeasurePreserving
      (fun pairs : LabelPairs => pairs wire bit purpose)
      labelPairsLaw seedLabelLaw := by
  unfold labelPairsLaw
  let h := (measurePreserving_eval_infinitePi
      (fun _ : Purpose => seedLabelLaw) purpose).comp
      ((measurePreserving_eval_infinitePi
        (fun _ : Bool => Measure.infinitePi
          (fun _ : Purpose => seedLabelLaw)) bit).comp
        (measurePreserving_eval_infinitePi
          (fun _ : BitIndex => Measure.infinitePi
            (fun _ : Bool => Measure.infinitePi
              (fun _ : Purpose => seedLabelLaw))) wire))
  apply h.congr (by fun_prop)
  filter_upwards [] with pairs
  rfl

/-- At a fixed wire and bit, all purpose-indexed pad coordinates are mutually
independent under the ideal product law. -/
theorem labelPurposeCoordinates_independent (wire : BitIndex) (bit : Bool) :
    iIndepFun (fun purpose (pairs : LabelPairs) => pairs wire bit purpose)
      labelPairsLaw := by
  have hslice : MeasurePreserving
      (fun pairs : LabelPairs => pairs wire bit)
      labelPairsLaw (Measure.infinitePi fun _ : Purpose => seedLabelLaw) := by
    unfold labelPairsLaw
    let h := (measurePreserving_eval_infinitePi
      (fun _ : Bool => Measure.infinitePi
        (fun _ : Purpose => seedLabelLaw)) bit).comp
      (measurePreserving_eval_infinitePi
        (fun _ : BitIndex => Measure.infinitePi
          (fun _ : Bool => Measure.infinitePi
            (fun _ : Purpose => seedLabelLaw))) wire)
    apply h.congr (by fun_prop)
    filter_upwards [] with pairs
    rfl
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), hslice.map_eq]
  congr 1
  funext purpose
  exact (labelPairsLaw_uniform_marginal wire bit purpose).map_eq.symm

/-- All `(wire, bit, purpose)` pad coordinates are mutually independent under
the ideal product law. -/
theorem labelCoordinates_independent :
    iIndepFun
      (fun address : LabelAddress => fun pairs : LabelPairs =>
        pairs address.1.1 address.1.2 address.2)
      labelPairsLaw := by
  have hgroups : iIndepFun
      (fun address : BitIndex × Bool => fun pairs : LabelPairs =>
        pairs address.1 address.2)
      labelPairsLaw := by
    unfold labelPairsLaw
    exact iIndepFun_uncurry_infinitePi'
      (μ := fun _ : BitIndex => fun _ : Bool =>
        Measure.infinitePi fun _ : Purpose => seedLabelLaw)
      (X := fun _ _ pads => pads) (by fun_prop)
  exact iIndepFun_uncurry' (by fun_prop) hgroups fun address =>
    labelPurposeCoordinates_independent address.1 address.2

/-- Evaluation at one internal-oracle address has the requested exact uniform
marginal under the ideal law. -/
theorem internalOracleLaw_uniform_marginal (modulus : SamplingModulus)
    (purpose : Purpose) :
    MeasurePreserving
      (fun oracle : InternalOracle => oracle modulus purpose)
      internalOracleLaw (internalValueLaw modulus) := by
  unfold internalOracleLaw
  let h := (measurePreserving_eval_infinitePi
      (fun _ : Purpose => internalValueLaw modulus) purpose).comp
    (measurePreserving_eval_infinitePi
      (fun modulus : SamplingModulus =>
        Measure.infinitePi fun _ : Purpose => internalValueLaw modulus)
      modulus)
  apply h.congr (by fun_prop)
  filter_upwards [] with oracle
  rfl

/-- All `(modulus, purpose)` coordinates of the ideal internal oracle are
mutually independent. -/
theorem internalCoordinates_independent :
    iIndepFun
      (fun address : InternalAddress => fun oracle : InternalOracle =>
        oracle address.1 address.2)
      internalOracleLaw := by
  unfold internalOracleLaw
  exact iIndepFun_uncurry_infinitePi
    (μ := fun modulus : SamplingModulus => fun _ : Purpose =>
      internalValueLaw modulus)
    (X := fun _ _ value => value) (by fun_prop)

/-- Coordinatewise uniform-preserving permutations preserve the complete
typed ideal internal-oracle law. This utility makes no statement about the
concrete seeded PRF. -/
theorem internalOracleLaw_map_coordinatewise
    (change : (modulus : SamplingModulus) → Purpose →
      Fin modulus.value → Fin modulus.value)
    (hmeasurable : ∀ modulus purpose,
      Measurable (change modulus purpose))
    (hpreserves : ∀ modulus purpose,
      Measure.map (change modulus purpose) (internalValueLaw modulus) =
        internalValueLaw modulus) :
    Measure.map
        (fun oracle modulus purpose =>
          change modulus purpose (oracle modulus purpose))
        internalOracleLaw = internalOracleLaw := by
  unfold internalOracleLaw
  change Measure.map
      (fun oracle => fun modulus =>
        (fun values => fun purpose =>
          change modulus purpose (values purpose)) (oracle modulus))
      (Measure.infinitePi fun modulus : SamplingModulus =>
        Measure.infinitePi fun _ : Purpose => internalValueLaw modulus) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun modulus : SamplingModulus =>
      Measure.infinitePi fun _ : Purpose => internalValueLaw modulus)
    (f := fun modulus values => fun purpose =>
      change modulus purpose (values purpose))
    (fun _ => by fun_prop)]
  congr 1
  funext modulus
  change Measure.map
      (fun values => fun purpose => change modulus purpose (values purpose))
      (Measure.infinitePi fun _ : Purpose => internalValueLaw modulus) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : Purpose => internalValueLaw modulus)
    (f := fun purpose value => change modulus purpose value)
    (fun _ => by fun_prop)]
  congr 1
  funext purpose
  exact hpreserves modulus purpose

/-- The fixed 512-bit little-endian `(x,y)` presentation. -/
def inputBit {profile : BN254.Profile} (input : AffineInput profile)
    (index : BitIndex) : Bool :=
  if index.val < coordinateWidth then
    input.x.val.testBit index.val
  else
    input.y.val.testBit (index.val - coordinateWidth)

/-- Protected genuine-label selection. A candidate never receives a custom
label key or a candidate-defined selected-label carrier. -/
def activeLabels {profile : BN254.Profile} (pairs : LabelPairs)
    (input : AffineInput profile) : ActiveLabels :=
  fun index => pairs index (inputBit input index)

theorem activeLabels_measurable {profile : BN254.Profile}
    (input : AffineInput profile) :
    Measurable (fun pairs : LabelPairs => activeLabels pairs input) := by
  apply measurable_pi_lambda
  intro wire
  apply measurable_pi_lambda
  intro purpose
  unfold activeLabels
  fun_prop

inductive EvalError where
  | malformedArtifact
  | invalidLabels
  | internalFailure
  deriving DecidableEq, Repr

inductive DecodeError where
  | malformedArtifact
  | trailingBytes
  deriving DecidableEq, Repr

/-- Candidate-controlled ideal scheme. The artifact carrier is internal;
only `encodeArtifact` crosses the evaluator boundary. -/
structure Scheme (profile : BN254.Profile) where
  Artifact : Type
  garble : HiddenInput profile → InternalOracle → LabelPairs → Artifact
  evaluate : Artifact → AffineInput profile → ActiveLabels →
    Except EvalError profile.Output
  encodeArtifact : Artifact → ByteArray
  decodeArtifact : ByteArray → Except DecodeError Artifact

namespace Scheme

/-- Assemble a scheme from named component functions. Keeping this constructor
visible lets concrete implementations reuse generic correctness/codec lifting
without normalizing dependent record projections. -/
def ofFunctions {profile : BN254.Profile}
    (Artifact : Type)
    (garble : HiddenInput profile → InternalOracle → LabelPairs → Artifact)
    (evaluate : Artifact → AffineInput profile → ActiveLabels →
      Except EvalError profile.Output)
    (encodeArtifact : Artifact → ByteArray)
    (decodeArtifact : ByteArray → Except DecodeError Artifact) :
  Scheme profile where
  Artifact := Artifact
  garble := garble
  evaluate := evaluate
  encodeArtifact := encodeArtifact
  decodeArtifact := decodeArtifact

/-- The exact bytes emitted by the generic garbler. -/
def garbleBytes {profile : BN254.Profile} (scheme : Scheme profile)
    (hidden : HiddenInput profile) (oracle : InternalOracle)
    (pairs : LabelPairs) : ByteArray :=
  scheme.encodeArtifact (scheme.garble hidden oracle pairs)

/-- The generic evaluator has no hidden key, advice, closure, or other
per-instance channel. It receives only artifact bytes, `A`, and fixed active
labels. -/
def evaluateBytes {profile : BN254.Profile} (scheme : Scheme profile)
    (bytes : ByteArray) (input : AffineInput profile)
    (labels : ActiveLabels) : Except EvalError profile.Output :=
  match scheme.decodeArtifact bytes with
  | .error _ => .error .malformedArtifact
  | .ok artifact => scheme.evaluate artifact input labels

end Scheme

/-- Every evaluator-visible ideal field. Privacy is about actual artifact
bytes, not only the decoded group result. -/
structure PublicView (profile : BN254.Profile) where
  artifactBytes : ByteArray
  activeLabels : ActiveLabels
  result : Except EvalError profile.Output

@[ext] theorem PublicView.ext {profile : BN254.Profile}
    (left right : PublicView profile)
    (hartifactBytes : left.artifactBytes = right.artifactBytes)
    (hactiveLabels : left.activeLabels = right.activeLabels)
    (hresult : left.result = right.result) : left = right := by
  cases left
  cases right
  cases hartifactBytes
  cases hactiveLabels
  cases hresult
  rfl

namespace PublicView

def presentation (profile : BN254.Profile) :
    PublicView profile → (ByteArray × ActiveLabels) ×
      Except EvalError profile.Output :=
  fun view => ((view.artifactBytes, view.activeLabels), view.result)

def presentationEquiv (profile : BN254.Profile) :
    PublicView profile ≃ (ByteArray × ActiveLabels) ×
      Except EvalError profile.Output where
  toFun := presentation profile
  invFun value := ⟨value.1.1, value.1.2, value.2⟩
  left_inv view := by cases view; rfl
  right_inv value := by cases value with | mk left result => cases left; rfl

end PublicView

noncomputable instance : MeasurableSpace ByteArray := ⊤
noncomputable instance : DiscreteMeasurableSpace ByteArray where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top

noncomputable instance (profile : BN254.Profile) :
    MeasurableSpace (Except EvalError profile.Output) := ⊤
noncomputable instance (profile : BN254.Profile) :
    DiscreteMeasurableSpace (Except EvalError profile.Output) where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top

/-- Artifact bytes and evaluator results are discrete. Active labels retain
their product σ-algebra, making every finite-purpose observation measurable. -/
noncomputable instance (profile : BN254.Profile) :
    MeasurableSpace (PublicView profile) :=
  MeasurableSpace.comap (PublicView.presentation profile) inferInstance

noncomputable def PublicView.measurableEquiv (profile : BN254.Profile) :
    PublicView profile ≃ᵐ (ByteArray × ActiveLabels) ×
      Except EvalError profile.Output where
  toEquiv := PublicView.presentationEquiv profile
  measurable_toFun := measurable_iff_comap_le.2 le_rfl
  measurable_invFun := by
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap (PublicView.presentationEquiv profile).symm
      (MeasurableSpace.comap (PublicView.presentationEquiv profile)
        (inferInstance : MeasurableSpace
          ((ByteArray × ActiveLabels) ×
            Except EvalError profile.Output))) ≤
      (inferInstance : MeasurableSpace
        ((ByteArray × ActiveLabels) × Except EvalError profile.Output))
    rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap
      (id : ((ByteArray × ActiveLabels) ×
        Except EvalError profile.Output) →
          ((ByteArray × ActiveLabels) × Except EvalError profile.Output))
      (inferInstance : MeasurableSpace
        ((ByteArray × ActiveLabels) × Except EvalError profile.Output)) ≤
      (inferInstance : MeasurableSpace
        ((ByteArray × ActiveLabels) × Except EvalError profile.Output))
    rw [MeasurableSpace.comap_id]

def publicView {profile : BN254.Profile} (scheme : Scheme profile)
    (hidden : HiddenInput profile) (oracle : InternalOracle)
    (pairs : LabelPairs) (input : AffineInput profile) : PublicView profile :=
  let bytes := scheme.garbleBytes hidden oracle pairs
  let labels := activeLabels pairs input
  { artifactBytes := bytes
    activeLabels := labels
    result := scheme.evaluateBytes bytes input labels }

/-- The complete hidden one-shot garbling state.  The harness owns the label
pairs, but they are hidden randomness and therefore belong inside the
source/target reparameterization.  Keeping the selected labels in
`PublicView` forces the equivalence to preserve exactly the labels delivered
to the evaluator while permitting the unused labels to change. -/
structure HiddenState where
  internalOracle : InternalOracle
  pairs : LabelPairs

namespace HiddenState

def prodEquiv : HiddenState ≃ InternalOracle × LabelPairs where
  toFun state := (state.internalOracle, state.pairs)
  invFun state := ⟨state.1, state.2⟩
  left_inv state := by cases state; rfl
  right_inv state := by cases state; rfl

noncomputable instance : MeasurableSpace HiddenState :=
  MeasurableSpace.comap prodEquiv inferInstance

noncomputable def measurableEquiv :
    HiddenState ≃ᵐ InternalOracle × LabelPairs where
  toEquiv := prodEquiv
  measurable_toFun := measurable_iff_comap_le.2 le_rfl
  measurable_invFun := by
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap prodEquiv.symm
      (MeasurableSpace.comap prodEquiv
        (inferInstance : MeasurableSpace
          (InternalOracle × LabelPairs))) ≤
      (inferInstance : MeasurableSpace
        (InternalOracle × LabelPairs))
    rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap
      (id : InternalOracle × LabelPairs → InternalOracle × LabelPairs)
      (inferInstance : MeasurableSpace
        (InternalOracle × LabelPairs)) ≤
      (inferInstance : MeasurableSpace
        (InternalOracle × LabelPairs))
    rw [MeasurableSpace.comap_id]

end HiddenState

@[ext] theorem HiddenState.ext (left right : HiddenState)
    (horacle : left.internalOracle = right.internalOracle)
    (hpairs : left.pairs = right.pairs) : left = right := by
  cases left
  cases right
  cases horacle
  cases hpairs
  rfl

def stateView {profile : BN254.Profile} (scheme : Scheme profile)
    (hidden : HiddenInput profile) (state : HiddenState)
    (input : AffineInput profile) : PublicView profile :=
  publicView scheme hidden state.internalOracle state.pairs input

/-- The independent product of the ideal internal oracle and ideal label pads,
transported to the protected hidden-state carrier. -/
noncomputable def hiddenStateLaw : Measure HiddenState :=
  Measure.map HiddenState.measurableEquiv.symm
    (internalOracleLaw.prod labelPairsLaw)

/-- Every equivalence between finite discrete uniform spaces preserves the
uniform probability law. -/
theorem measurePreserving_uniformOfFiniteEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [Finite α] [Finite β] [Nonempty α] [Nonempty β]
    (equiv : α ≃ β) :
    MeasurePreserving equiv (uniformOn Set.univ) (uniformOn Set.univ) := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  refine ⟨Measurable.of_discrete, ?_⟩
  ext event hevent
  rw [Measure.map_apply Measurable.of_discrete hevent,
    uniformOn_univ, uniformOn_univ,
    Measure.count_apply (hevent.preimage Measurable.of_discrete),
    Measure.count_apply hevent,
    Set.encard_preimage_of_bijective equiv.bijective,
    Fintype.card_congr equiv]

/-- A maximally biased coin witnesses why a set-theoretic state-space
bijection is insufficient: the identity bijection does not turn an always
false coin into an always true coin. -/
theorem stateSpaceBijection_not_distributional :
    ¬ MeasurePreserving (Equiv.refl Bool)
      (Measure.dirac false) (Measure.dirac true) := by
  intro hpreserves
  have hequal := congrArg (fun law : Measure Bool => law {false})
    hpreserves.map_eq
  simpa [MeasurableEquiv.map_apply] using hequal

/-- Coordinatewise measure-preserving pad permutations preserve the complete
unbounded ideal-pad product law. -/
theorem labelPairsLaw_map_coordinatewise
    (change : BitIndex → Bool → Purpose → SeedLabel → SeedLabel)
    (hmeasurable : ∀ wire bit purpose, Measurable (change wire bit purpose))
    (hpreserves : ∀ wire bit purpose,
      Measure.map (change wire bit purpose) seedLabelLaw = seedLabelLaw) :
    Measure.map
        (fun pairs wire bit purpose =>
          change wire bit purpose (pairs wire bit purpose))
        labelPairsLaw = labelPairsLaw := by
  unfold labelPairsLaw
  change Measure.map
      (fun pairs => fun wire =>
        (fun values => fun bit =>
          (fun pads => fun purpose =>
            change wire bit purpose (pads purpose)) (values bit)) (pairs wire))
      (Measure.infinitePi fun _ : BitIndex =>
        Measure.infinitePi fun _ : Bool =>
          Measure.infinitePi fun _ : Purpose => seedLabelLaw) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : BitIndex =>
      Measure.infinitePi fun _ : Bool =>
        Measure.infinitePi fun _ : Purpose => seedLabelLaw)
    (f := fun wire values => fun bit => fun purpose =>
      change wire bit purpose (values bit purpose))
    (fun _ => by fun_prop)]
  congr 1
  funext wire
  change Measure.map
      (fun values => fun bit =>
        (fun pads => fun purpose =>
          change wire bit purpose (pads purpose)) (values bit))
      (Measure.infinitePi fun _ : Bool =>
        Measure.infinitePi fun _ : Purpose => seedLabelLaw) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : Bool =>
      Measure.infinitePi fun _ : Purpose => seedLabelLaw)
    (f := fun bit pads => fun purpose =>
      change wire bit purpose (pads purpose))
    (fun _ => by fun_prop)]
  congr 1
  funext bit
  change Measure.map
      (fun pads => fun purpose => change wire bit purpose (pads purpose))
      (Measure.infinitePi fun _ : Purpose => seedLabelLaw) = _
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : Purpose => seedLabelLaw)
    (f := fun purpose pad => change wire bit purpose pad)
    (fun _ => by fun_prop)]
  congr 1
  funext purpose
  exact hpreserves wire bit purpose

/-- Universal genuine-label correctness, including zero scalars, infinity
outputs, doubling, inverse, and identity cases. -/
def Correct {profile : BN254.Profile} (scheme : Scheme profile) : Prop :=
  ∀ (hidden : HiddenInput profile) (oracle : InternalOracle)
    (pairs : LabelPairs) (input : AffineInput profile),
    ∃ output : profile.Output,
      scheme.evaluateBytes (scheme.garbleBytes hidden oracle pairs) input
          (activeLabels pairs input) = .ok output ∧
        profile.outputEquiv output = reference profile hidden input

/-- Exact codec laws. The second direction forbids ignored truncation,
trailing bytes, or alternative encodings. -/
structure CodecLaws {profile : BN254.Profile} (scheme : Scheme profile) : Prop where
  decode_encode : ∀ artifact,
    scheme.decodeArtifact (scheme.encodeArtifact artifact) = .ok artifact
  encode_decode : ∀ bytes artifact,
    scheme.decodeArtifact bytes = .ok artifact →
      scheme.encodeArtifact artifact = bytes

/-- Lift internal artifact correctness through an exact artifact codec. This
keeps concrete fixed-width encoders out of the normalization path for the
ranked correctness theorem. -/
theorem correct_of_artifact {profile : BN254.Profile} (scheme : Scheme profile)
    (codec : CodecLaws scheme)
    (artifactCorrect :
      ∀ (hidden : HiddenInput profile) (oracle : InternalOracle)
        (pairs : LabelPairs) (input : AffineInput profile),
        ∃ output : profile.Output,
          scheme.evaluate (scheme.garble hidden oracle pairs) input
              (activeLabels pairs input) = .ok output ∧
            profile.outputEquiv output = reference profile hidden input) :
    Correct scheme := by
  intro hidden oracle pairs input
  obtain ⟨output, hevaluate, houtput⟩ :=
    artifactCorrect hidden oracle pairs input
  refine ⟨output, ?_, houtput⟩
  unfold Scheme.garbleBytes Scheme.evaluateBytes
  rw [codec.decode_encode]
  exact hevaluate

/-- Component-level codec laws for `Scheme.ofFunctions`. -/
theorem Scheme.codecLaws_ofFunctions {profile : BN254.Profile}
    (Artifact : Type)
    (garble : HiddenInput profile → InternalOracle → LabelPairs → Artifact)
    (evaluate : Artifact → AffineInput profile → ActiveLabels →
      Except EvalError profile.Output)
    (encodeArtifact : Artifact → ByteArray)
    (decodeArtifact : ByteArray → Except DecodeError Artifact)
    (decode_encode : ∀ artifact,
      decodeArtifact (encodeArtifact artifact) = .ok artifact)
    (encode_decode : ∀ bytes artifact,
      decodeArtifact bytes = .ok artifact → encodeArtifact artifact = bytes) :
    CodecLaws (Scheme.ofFunctions Artifact garble evaluate
      encodeArtifact decodeArtifact) where
  decode_encode := decode_encode
  encode_decode := encode_decode

/-- Component-level internal correctness lifts through an exact codec. -/
theorem Scheme.correct_ofFunctions {profile : BN254.Profile}
    (Artifact : Type)
    (garble : HiddenInput profile → InternalOracle → LabelPairs → Artifact)
    (evaluate : Artifact → AffineInput profile → ActiveLabels →
      Except EvalError profile.Output)
    (encodeArtifact : Artifact → ByteArray)
    (decodeArtifact : ByteArray → Except DecodeError Artifact)
    (codec : CodecLaws (Scheme.ofFunctions Artifact garble evaluate
      encodeArtifact decodeArtifact))
    (artifactCorrect :
      ∀ (hidden : HiddenInput profile) (oracle : InternalOracle)
        (pairs : LabelPairs) (input : AffineInput profile),
        ∃ output : profile.Output,
          evaluate (garble hidden oracle pairs) input
              (activeLabels pairs input) = .ok output ∧
            profile.outputEquiv output = reference profile hidden input) :
    Correct (Scheme.ofFunctions Artifact garble evaluate
      encodeArtifact decodeArtifact) :=
  correct_of_artifact _ codec artifactCorrect

theorem CodecLaws.encode_injective {profile : BN254.Profile}
    {scheme : Scheme profile} (laws : CodecLaws scheme) :
    Function.Injective scheme.encodeArtifact := by
  intro left right equality
  have decoded := congrArg scheme.decodeArtifact equality
  simpa [laws.decode_encode] using decoded

/-- Information-theoretic one-shot function privacy under the explicit ideal
law. The accepted proof establishes equality of the complete public-view
distributions whenever two hidden maps agree at the selected `A`. -/
structure FunctionPrivate {profile : BN254.Profile}
    (scheme : Scheme profile) : Prop where
  stateView_measurable : ∀ (hidden : HiddenInput profile)
    (input : AffineInput profile),
    Measurable (fun state : HiddenState =>
      stateView scheme hidden state input)
  publicView_identDistrib : ∀ (input : AffineInput profile)
    (source target : HiddenInput profile),
    reference profile source input = reference profile target input →
    IdentDistrib
      (fun state => stateView scheme source state input)
      (fun state => stateView scheme target state input)
      hiddenStateLaw hiddenStateLaw

namespace FunctionPrivate

/-- The protected distributional privacy theorem for the complete public
view. -/
theorem identDistrib {profile : BN254.Profile} {scheme : Scheme profile}
    (privacy : FunctionPrivate scheme) (input : AffineInput profile)
    (source target : HiddenInput profile)
    (hequal : reference profile source input = reference profile target input) :
    IdentDistrib
      (fun state => stateView scheme source state input)
      (fun state => stateView scheme target state input)
      hiddenStateLaw hiddenStateLaw :=
  privacy.publicView_identDistrib input source target hequal

/-- Equality of the probability of every measurable public-view event. -/
theorem eventProbability_eq {profile : BN254.Profile} {scheme : Scheme profile}
    (privacy : FunctionPrivate scheme) (input : AffineInput profile)
    (source target : HiddenInput profile)
    (hequal : reference profile source input = reference profile target input)
    {event : Set (PublicView profile)} (hevent : MeasurableSet event) :
    hiddenStateLaw
        ((fun state => stateView scheme source state input) ⁻¹' event) =
      hiddenStateLaw
        ((fun state => stateView scheme target state input) ⁻¹' event) :=
  (privacy.identDistrib input source target hequal).measure_mem_eq hevent

end FunctionPrivate

/-- The protected acceptance predicate. Its only optimization parameter is
the universal worst-case size of the exact serialized artifact. -/
structure ValidCandidate {profile : BN254.Profile}
    (scheme : Scheme profile) (maxBytes : Nat) : Prop where
  correct : Correct scheme
  function_private : FunctionPrivate scheme
  codec : CodecLaws scheme
  artifact_bound : ∀ (hidden : HiddenInput profile)
      (oracle : InternalOracle) (pairs : LabelPairs),
    (scheme.garbleBytes hidden oracle pairs).size ≤ maxBytes

/-- Generated benchmark modules instantiate this declaration with the exact
canonical decimal parsed from `Submission/score.txt`.  The concrete profile is
fixed here; a submission cannot replace the curve or output interpretation. -/
def RankedClaim
    (scheme : Scheme BN254.bn254) (claimedBytes : Nat) : Prop :=
  ValidCandidate scheme claimedBytes

end GarblingPrize.Protected
