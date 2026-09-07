import G1Release.Submission.SchemeCert

/-! Randomized arithmetic construction. Every randomness value is correct;
the distribution of the eventual byte-tape sampler is a separate obligation.
In particular, the offset fiber fixes only the Horner sum, not its entries. -/
namespace G1Release.Submission.Randomized
open GarblingPrize.Protected G1Release.Protected SecretRelease
open G1Release.Submission.BalancedTernary

abbrev Hidden := Private
abbrev Word := BN254.Fq

def coefficients (offset : BN254.G1) (digit : Digit) (scale : Wordˣ) :
    ProjectiveMap.Coefficients Word :=
  (ProjectiveMap.coefficients Scheme.curveC
    (RuntimeG1.encode (Scheme.runtimeOfGroup offset))
    (Scheme.digitSelector digit) (Scheme.digitSign digit)).scale (scale : Word)

theorem coefficients_xX (offset : BN254.G1) (digit : Digit) (scale : Wordˣ) :
    (coefficients offset digit scale).xX =
      -(2 * ProjectiveMap.curveC * (coefficients offset digit scale).zYY) := by
  apply ProjectiveMap.scale_xX
  exact ProjectiveMap.coefficients_xX _ _ _ _

theorem coefficients_zXX (offset : BN254.G1) (digit : Digit) (scale : Wordˣ) :
    (coefficients offset digit scale).zXX =
      3 * (coefficients offset digit scale).xYY := by
  apply ProjectiveMap.scale_zXX
  exact ProjectiveMap.coefficients_zXX _ _ _ _

theorem polynomial_coefficients (offset : BN254.G1) (digit : Digit)
    (scale : Wordˣ) (input : Input) :
    ProjectiveMap.polynomial (coefficients offset digit scale)
        (input.val.1.val : Word) (input.val.2.val : Word) =
      ProjectiveMap.Coordinates.ofHomogeneous
        (HomogeneousRCB.randomize (scale : Word) (Scheme.rawMap offset digit input)) := by
  rw [coefficients, ProjectiveMap.polynomial_scale,
    ProjectiveMap.polynomial_coefficients]
  rfl

def mapHidden (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (scales : Fin 161 → Wordˣ) (chains : Fin 161 → ProjectiveMap.ChainMasks Word)
    (index : Fin 161) : ProjectiveMap.Hidden :=
  ⟨coefficients (Scheme.offsetAt offsets index) (Scheme.digitAt hidden index)
      (scales index), chains index⟩

structure Randomness (hidden : Hidden) where
  offsets : OffsetFamily.Fiber hidden
  scales : Fin 161 → Wordˣ
  chains : Fin 161 → ProjectiveMap.ChainMasks Word
  tableMasks : Fin 161 → ProjectiveMap.TableKind → Fin 254 → Word
  tableMasks_sum : ∀ index kind, ∑ i, tableMasks index kind i =
    ((mapHidden hidden offsets scales chains index).params kind).constant

theorem Randomness.ext {hidden : Hidden} (left right : Randomness hidden)
    (hoffsets : left.offsets = right.offsets) (hscales : left.scales = right.scales)
    (hchains : left.chains = right.chains) (hmasks : left.tableMasks = right.tableMasks) :
    left = right := by
  cases left
  cases right
  cases hoffsets
  cases hscales
  cases hchains
  cases hmasks
  rfl

def Randomness.masks {hidden : Hidden} (random : Randomness hidden)
    (index : Fin 161) (kind : ProjectiveMap.TableKind) :
    AffineTable.MaskFiber
      ((mapHidden hidden random.offsets random.scales random.chains index).params kind).constant :=
  ⟨random.tableMasks index kind, random.tableMasks_sum index kind⟩

def canonical (hidden : Hidden) : Randomness hidden where
  offsets := OffsetFamily.canonical hidden
  scales := fun _ => 1
  chains := fun _ => Scheme.zeroChainMasks
  tableMasks := fun _ _ => (AffineTable.canonicalMasks _).1
  tableMasks_sum := fun _ _ => (AffineTable.canonicalMasks _).2

instance (hidden : Hidden) : Nonempty (Randomness hidden) := ⟨canonical hidden⟩

def maps (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (index : Fin 161) : ProjectiveMap.Artifact :=
  ProjectiveMap.garble hash index.val (Scheme.xPairs keys) (Scheme.yPairs keys)
    (mapHidden hidden random.offsets random.scales random.chains index) (random.masks index)

def garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) : Scheme.Artifact :=
  ⟨Scheme.encodeFrom (maps hash hidden random keys) 161 (Nat.le_refl 161),
    by simpa [Scheme.claimedBytes] using
      Scheme.encodeFrom_size (maps hash hidden random keys) 161 (Nat.le_refl 161)⟩

theorem mapAt_garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (i : Fin 161) :
    Scheme.mapAt (garble hash hidden random keys) i =
      some (maps hash hidden random keys i) := by
  change ProjectiveMap.decode
    ((Scheme.encodeFrom (maps hash hidden random keys) 161 (Nat.le_refl 161)).extract
      (i.val * Scheme.mapBytes) ((i.val + 1) * Scheme.mapBytes)) = _
  rw [Scheme.encodeFrom_extract]
  exact ProjectiveMap.decode_encode _

/-- A sampler is an executable function, not a security assumption. The final
certificate must prove its distribution and both ROM games for this scheme. -/
def scheme (n : Nat) (sample : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) :
    SecretRelease.Scheme challenge where
  Artifact := Scheme.Artifact
  randomnessBytes := n
  garble := fun hash coins hidden keys _ => garble hash hidden (sample coins hidden) keys
  encode := Scheme.encode
  decode := Scheme.decode
  evaluate := Scheme.evaluate

@[simp] theorem scheme_encode (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) :
    (scheme n sample).encode = Scheme.encode := rfl

@[simp] theorem scheme_decode (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) :
    (scheme n sample).decode = Scheme.decode := rfl

@[simp] theorem scheme_garble (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden)
    (hash : Hash) (coins : SecretRelease.Bytes n) (hidden : Hidden)
    (keys : challenge.inputs.Keys) (outputs : challenge.outputs.Keys) :
    (scheme n sample).garble hash coins hidden keys outputs =
      garble hash hidden (sample coins hidden) keys := rfl

@[simp] theorem scheme_evaluate (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden)
    (hash : Hash) (artifact : Scheme.Artifact) (input : Input) (active : ByteArray) :
    (scheme n sample).evaluate hash artifact input active =
      Scheme.evaluate hash artifact input active := rfl

theorem artifactBound (n : Nat) (sample : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) :
    ArtifactBound (scheme n sample) Scheme.claimedBytes := by
  intro hash coins hidden keys outputs
  exact le_of_eq (Scheme.encode_size _)

end G1Release.Submission.Randomized
