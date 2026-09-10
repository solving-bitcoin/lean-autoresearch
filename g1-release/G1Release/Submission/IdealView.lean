import G1Release.Submission.RandomnessCoupling

/-! Proof-only view with independent ciphertexts in every inactive half-row.
No unrevealed input labels are used in this view. The ROM reduction must
justify replacing the real ciphertexts with these independent values. -/
namespace G1Release.Submission.IdealView
open G1Release.Math SecretRelease
open G1Release.Protected G1Release.Submission.Randomized

abbrev Slot := Fin 161 × ProjectiveMap.TableKind × Fin 254
abbrev InactiveCiphertexts := Slot → Label

def tableWire (kind : ProjectiveMap.TableKind) (row : Fin 254) : Fin 512 :=
  match kind with
  | .shared | .xXY | .yCubic | .yQuadratic | .yLinear |
      .zSquare | .zCross | .zLinear => ⟨row.val, by omega⟩
  | .xYY | .xCorrection | .zCorrection => ⟨256+row.val, by omega⟩

def table (hash : Hash) (purpose : Nat) (params : AffineTable.Params)
    (masks : Fin 254 → AffineTable.Word) (bits : Fin 254 → Bool)
    (active : Fin 254 → Label) (inactive : Fin 254 → Label) : AffineTable.Table :=
  Bytes.ofFn fun k =>
    let row : Fin 254 := ⟨k.val / 64, by omega⟩
    let bit := decide (32 ≤ k.val % 64)
    let byte : Fin 32 := ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
    (if bit = bits row then
      AffineTable.encrypt (AffineTable.share params (masks row) row bit)
        (AffineTable.pad hash (active row) purpose row.val)
    else inactive row).get byte

theorem table_eq_of_shares (hash : Hash) (purpose : Nat)
    (p₀ p₁ : AffineTable.Params) (m₀ m₁ : Fin 254 → AffineTable.Word)
    (bits : Fin 254 → Bool) (active inactive : Fin 254 → Label)
    (h : ∀ i, AffineTable.share p₀ (m₀ i) i (bits i) =
      AffineTable.share p₁ (m₁ i) i (bits i)) :
    table hash purpose p₀ m₀ bits active inactive =
      table hash purpose p₁ m₁ bits active inactive := by
  apply Vector.ext
  intro k hk
  simp only [table, Bytes.ofFn, Vector.getElem_ofFn]
  split
  · rename_i heq
    rw [heq, h]
  · rfl

def maps (hash : Hash) (input : Input) (hidden : Hidden) (random : Randomness hidden)
    (active : Fin 512 → Label) (inactive : InactiveCiphertexts)
    (mapIndex : Fin 161) : ProjectiveMap.Artifact where
  tables := fun kind => table hash (ProjectiveMap.purpose mapIndex.val kind)
    ((mapHidden hidden random.offsets random.scales random.chains mapIndex).params kind)
    (random.tableMasks mapIndex kind) (bitsFor kind input)
    (fun row => active (tableWire kind row)) (fun row => inactive (mapIndex,kind,row))

def garble (hash : Hash) (input : Input) (hidden : Hidden) (random : Randomness hidden)
    (active : Fin 512 → Label) (inactive : InactiveCiphertexts) : ByteArray :=
  Scheme.encodeFrom (maps hash input hidden random active inactive) 161 (Nat.le_refl 161)

theorem selectedShare_preserved (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (random : Randomness source) (index : Fin 161) (kind : ProjectiveMap.TableKind)
    (row : Fin 254) :
    let changed := targetRandomness input source target hequal random
    AffineTable.share
      ((mapHidden source random.offsets random.scales random.chains index).params kind)
      (random.tableMasks index kind row) row (bitsFor kind input row) =
    AffineTable.share
      ((mapHidden target changed.offsets changed.scales changed.chains index).params kind)
      (changed.tableMasks index kind row) row (bitsFor kind input row) := by
  exact (AffineTablePrivacy.share_maskEquiv
    ((mapHidden source random.offsets random.scales random.chains index).params kind)
    ((mapHidden target
      (targetOffsets input source target hequal random.offsets)
      (fun i => targetRandomizer input source target hequal random.offsets i (random.scales i))
      (targetChainMasks input source target hequal random.offsets random.scales random.chains)
      index).params kind)
    (bitsFor kind input)
    (tableOutput_preserved input source target hequal random.offsets random.scales random.chains index kind)
    (random.masks index kind) row).symm

theorem maps_preserved (hash : Hash) (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (random : Randomness source) (active : Fin 512 → Label) (inactive : InactiveCiphertexts) :
    maps hash input source random active inactive =
      maps hash input target (targetRandomness input source target hequal random) active inactive := by
  funext index
  apply ProjectiveMap.Artifact.ext
  funext kind
  dsimp only [maps]
  apply table_eq_of_shares
  exact selectedShare_preserved input source target hequal random index kind

theorem garble_preserved (hash : Hash) (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (random : Randomness source) (active : Fin 512 → Label) (inactive : InactiveCiphertexts) :
    garble hash input source random active inactive =
      garble hash input target (targetRandomness input source target hequal random) active inactive := by
  unfold garble
  rw [maps_preserved hash input source target hequal random active inactive]

end G1Release.Submission.IdealView
