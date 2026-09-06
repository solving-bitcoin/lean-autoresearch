import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn

/-! A one-shot, known-input conditional-release contract. This file contains
interfaces and acceptance predicates, not construction/security reductions.
The challenge author fixes every field of `Challenge` before submissions.
SHA-256, circuits, signatures' public verification keys, and gate costs are
not implicit assumptions. Any public instance data belongs in the artifact
unless it is explicitly part of the fixed input/output disclosure channels. -/
namespace SecretRelease
open MeasureTheory ProbabilityTheory OracleSpec OracleComp

abbrev Bytes (n : Nat) := Vector UInt8 n
abbrev Label := Bytes 32
abbrev Hash := ByteArray → Label
abbrev Program (α : Type) := OracleComp (ByteArray →ₒ Label) α

instance (n : Nat) : Finite (Bytes n) := by
  apply Finite.of_injective (fun v : Bytes n => fun i : Fin n => (v.get i).toFin)
  intro a b h
  apply Vector.ext
  intro i hi
  exact UInt8.ext (Fin.ext_iff.mp (congrFun h ⟨i, hi⟩))
instance (n : Nat) : MeasurableSpace (Bytes n) := ⊤

/-- Accepted encodings are exactly the canonical encodings of typed values.
Invalid encodings are outside honest correctness, never a restriction on an
attacker's computations or intermediate values. -/
structure Codec (A : Type) where
  width : Nat
  encode : A → Vector Bool width
  decode : Vector Bool width → Option A
  decode_encode : ∀ a, decode (encode a) = some a
  encode_decode : ∀ b a, decode b = some a → encode a = b

def Codec.bits (n : Nat) : Codec (Vector Bool n) :=
  ⟨n, id, some, fun _ => rfl, fun _ _ h => (Option.some.inj h).symm⟩
def Codec.unit : Codec Unit :=
  ⟨0, fun _ => #v[], fun _ => some (), fun a => by cases a; rfl,
    fun b a _ => by apply Vector.ext; intro i hi; omega⟩

/-- A checksum/shape predicate becomes part of the value type itself. -/
def Codec.checked (n : Nat) (valid : Vector Bool n → Bool) :
    Codec {bits : Vector Bool n // valid bits = true} where
  width := n
  encode := Subtype.val
  decode := fun bits => if h : valid bits = true then some ⟨bits, h⟩ else none
  decode_encode := fun a => by simp [a.property]
  encode_decode := by
    intro bits a h
    split at h
    · exact (congrArg Subtype.val (Option.some.inj h)).symm
    · contradiction

/-- Keys are sampled uniformly from this finite nonempty space, independently
of the oracle, the other disclosure's keys, and construction coins. A custom
space can express distinct pairs or correlated derived credentials; the
submission never chooses this space or the reveal function. -/
structure Disclosure (A : Type) where
  Keys : Type
  finite : Finite Keys
  nonempty : Nonempty Keys
  reveal : Hash → Keys → A → ByteArray
attribute [instance] Disclosure.finite Disclosure.nonempty
instance (d : Disclosure A) : MeasurableSpace d.Keys := ⊤

def pack (labels : List Label) : ByteArray :=
  ⟨labels.foldl (fun acc label => acc ++ label.toArray) #[]⟩

abbrev Pair := {p : Label × Label // p.1 ≠ p.2}
instance : Nonempty Pair :=
  ⟨⟨(Vector.replicate 32 0, Vector.replicate 32 1), by decide⟩⟩
def Pair.get (p : Pair) (b : Bool) : Label := if b then p.val.2 else p.val.1

def Lamport (codec : Codec A) : Disclosure A where
  Keys := Fin codec.width → Pair
  finite := inferInstance
  nonempty := inferInstance
  reveal := fun _ keys a => pack ((List.finRange codec.width).map fun i =>
    (keys i).get (codec.encode a)[i.val])

/-- The selector is part of the challenge. This is HORS-style disclosure,
not an assumed HORS unforgeability theorem or an implicit public-key channel. -/
def HORS (n : Nat) (select : Hash → A → Fin n → Bool) : Disclosure A where
  Keys := Fin n → Label
  finite := inferInstance
  nonempty := inferInstance
  reveal := fun h keys a => pack (((List.finRange n).filter (select h a)).map keys)

def OnesOnly (codec : Codec A) : Disclosure A :=
  HORS codec.width (fun _ a i => (codec.encode a)[i.val])

def Preimage (condition : A → Bool) : Disclosure A where
  Keys := Label
  finite := inferInstance
  nonempty := inferInstance
  reveal := fun _ key a => if condition a then pack [key] else ByteArray.empty

def Plain (encode : A → ByteArray) : Disclosure A where
  Keys := Unit
  finite := inferInstance
  nonempty := inferInstance
  reveal := fun _ _ a => encode a

/-- Classical, static-input, one-release ROM. Bounds are reviewed challenge
parameters, not submission choices. Local computation is unrestricted. -/
structure ClassicalBoundedQueryROM where
  maxQueries : Nat
  error : Nat → ℚ≥0
  nontrivial : ∀ q, q ≤ maxQueries → error q < 1

/-- Exact correctness is the default. A reviewed challenge may instead allow
a declared probability of failure over keys, coins, and the ideal oracle. -/
inductive Correctness where
  | exact
  | statistical (error : ℚ≥0) (nontrivial : error < 1)

structure Challenge where
  Private : Type
  Input : Type
  Output : Type
  privateCodec : Codec Private
  inputCodec : Codec Input
  inputs : Disclosure Input
  outputs : Disclosure Output
  reference : Private → Input → Output
  Claim : Type
  /-- A successful forbidden disclosure. For credential forgery, check a
  DIFFERENT VALID encoding here; invalid intermediate credentials are allowed.
  Raw-label recovery is a different goal and can be required separately. -/
  wins : Hash → Private → Input → inputs.Keys → outputs.Keys → Claim → Prop
  hidePrivate : Bool := false
  correctness : Correctness := .exact
  rom : ClassicalBoundedQueryROM

structure Scheme (c : Challenge) where
  Artifact : Type
  randomnessBytes : Nat
  garble : Hash → Bytes randomnessBytes → c.Private → c.inputs.Keys → c.outputs.Keys → Artifact
  encode : Artifact → ByteArray
  decode : ByteArray → Option Artifact
  evaluate : Hash → Artifact → c.Input → ByteArray → Option ByteArray

def Scheme.garbleBytes (s : Scheme c) (h : Hash) (coins : Bytes s.randomnessBytes)
    (p : c.Private) (ik : c.inputs.Keys) (ok : c.outputs.Keys) : ByteArray :=
  s.encode (s.garble h coins p ik ok)
def Scheme.evaluateBytes (s : Scheme c) (h : Hash) (artifact : ByteArray)
    (x : c.Input) (active : ByteArray) : Option ByteArray :=
  (s.decode artifact).bind fun a => s.evaluate h a x active

def Correct (s : Scheme c) : Prop :=
  ∀ h coins p ik ok x,
    s.evaluateBytes h (s.garbleBytes h coins p ik ok) x (c.inputs.reveal h ik x) =
      some (c.outputs.reveal h ok (c.reference p x))
def ArtifactBound (s : Scheme c) (bytes : Nat) : Prop :=
  ∀ h coins p ik ok, (s.garbleBytes h coins p ik ok).size ≤ bytes

structure View (c : Challenge) where
  input : c.Input
  artifact : ByteArray
  activeInputs : ByteArray
  /-- Give the authorized result for free, so security cannot depend on
  making honest evaluation computationally difficult. -/
  activeOutputs : ByteArray

namespace ROM
abbrev Oracle := List (Fin 256) → Label
abbrev Sample (s : Scheme c) := c.inputs.Keys × c.outputs.Keys × Bytes s.randomnessBytes × Oracle
def hash (oracle : Oracle) : Hash := fun b => oracle (b.data.toList.map UInt8.toFin)
def run (h : Hash) (p : Program α) : α := Id.run (simulateQ (QueryImpl.ofFn h) p)
noncomputable def law (s : Scheme c) : Measure (Sample s) :=
  letI : MeasurableSpace c.inputs.Keys := ⊤
  letI : MeasurableSpace c.outputs.Keys := ⊤
  (uniformOn (Set.univ : Set c.inputs.Keys)).prod
    ((uniformOn (Set.univ : Set c.outputs.Keys)).prod
      ((uniformOn (Set.univ : Set (Bytes s.randomnessBytes))).prod
        (Measure.infinitePi fun _ : List (Fin 256) => uniformOn (Set.univ : Set Label))))

def view (s : Scheme c) (p : c.Private) (x : c.Input) (ω : Sample s) : View c :=
  let h := hash ω.2.2.2
  ⟨x, s.garbleBytes h ω.2.2.1 p ω.1 ω.2.1,
    c.inputs.reveal h ω.1 x, c.outputs.reveal h ω.2.1 (c.reference p x)⟩
def Bounded (a : View c → Program α) (q : Nat) : Prop :=
  ∀ v, IsTotalQueryBound (a v) q
def winEvent (s : Scheme c) (p : c.Private) (x : c.Input)
    (a : View c → Program c.Claim) : Set (Sample s) :=
  {ω | c.wins (hash ω.2.2.2) p x ω.1 ω.2.1
    (run (hash ω.2.2.2) (a (view s p x ω)))}
def distinguishEvent (s : Scheme c) (p : c.Private) (x : c.Input)
    (a : View c → Program Bool) : Set (Sample s) :=
  {ω | run (hash ω.2.2.2) (a (view s p x ω)) = true}

def CorrectWithError (s : Scheme c) (error : ENNReal) : Prop :=
  letI : MeasurableSpace c.inputs.Keys := ⊤
  letI : MeasurableSpace c.outputs.Keys := ⊤
  ∀ p x,
    let failed : Set (Sample s) := {ω |
      s.evaluateBytes (hash ω.2.2.2) (view s p x ω).artifact x
        (view s p x ω).activeInputs ≠ some (view s p x ω).activeOutputs}
    MeasurableSet failed ∧ law s failed ≤ error

def ReleaseSecure (s : Scheme c) : Prop :=
  letI : MeasurableSpace c.inputs.Keys := ⊤
  letI : MeasurableSpace c.outputs.Keys := ⊤
  ∀ p x q, q ≤ c.rom.maxQueries → ∀ a, Bounded a q →
    MeasurableSet (winEvent s p x a) ∧ law s (winEvent s p x a) ≤ (c.rom.error q : ENNReal)

/-- Preserve hidden-parameter privacy whenever the two permitted results
agree. Quantifying both ordered pairs gives both distinguishing inequalities.
The input, public oracle access, and authorized output are all in the view. -/
def FunctionPrivate (s : Scheme c) : Prop :=
  letI : MeasurableSpace c.inputs.Keys := ⊤
  letI : MeasurableSpace c.outputs.Keys := ⊤
  c.hidePrivate = true → ∀ p₀ p₁ x, c.reference p₀ x = c.reference p₁ x →
    ∀ q, q ≤ c.rom.maxQueries → ∀ a, Bounded a q →
      MeasurableSet (distinguishEvent s p₀ x a) ∧
      law s (distinguishEvent s p₀ x a) ≤
        law s (distinguishEvent s p₁ x a) + (c.rom.error q : ENNReal)
end ROM

/-- Only the exact serialized scheme can be certified. Mathematical
well-formedness and compilation/resource/source-policy checks are separate:
proofs can be noncomputable; the executed methods must compile. -/
structure Certified (c : Challenge) where
  scheme : Scheme c
  maxBytes : Nat
  correct : match c.correctness with
    | .exact => Correct scheme
    | .statistical error _ => ROM.CorrectWithError scheme error
  decode_encode : ∀ a, scheme.decode (scheme.encode a) = some a
  encode_decode : ∀ b a, scheme.decode b = some a → scheme.encode a = b
  artifactBound : ArtifactBound scheme maxBytes
  releaseSecure : ROM.ReleaseSecure scheme
  functionPrivate : ROM.FunctionPrivate scheme

end SecretRelease
