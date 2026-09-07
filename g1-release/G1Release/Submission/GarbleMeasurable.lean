import G1Release.Submission.RealIdeal
import G1Release.Submission.MeasurableModels

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace G1Release.Submission.GarbleMeasurable
open GarblingPrize.Protected SecretRelease G1Release.Protected
open Randomized IdealView MeasureTheory MeasurableModels

abbrev Halves := Slot × Bool → Label

def mapsFromHalves (halves : Halves) (index : Fin 161) : ProjectiveMap.Artifact where
  tables := fun kind => Bytes.ofFn fun k =>
    let row : Fin 254 := ⟨k.val / 64, by omega⟩
    let bit := decide (32 ≤ k.val % 64)
    let byte : Fin 32 := ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
    (halves ((index,kind,row),bit)).get byte

def fromHalves (halves : Halves) : ByteArray :=
  Scheme.encodeFrom (mapsFromHalves halves) 161 (Nat.le_refl 161)

def ciphertexts (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (index : Slot × Bool) : Label :=
  AffineTable.ciphertextAt hash (ProjectiveMap.purpose index.1.1.val index.1.2.1)
    (ProjectiveMap.pairsFor (Scheme.xPairs keys) (Scheme.yPairs keys) index.1.2.1)
    ((mapHidden hidden random.offsets random.scales random.chains index.1.1).params index.1.2.1)
    (random.masks index.1.1 index.1.2.1) index.1.2.2 index.2

theorem garble_fromHalves (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) :
    Scheme.encode (Randomized.garble hash hidden random keys) =
      fromHalves (ciphertexts hash hidden random keys) := rfl

theorem ciphertexts_measurable {Ω : Type*} [MeasurableSpace Ω]
    (hashes : Ω → Hash) (hh : ∀ q, Measurable (fun ω => hashes ω q))
    (hidden : Hidden) (random : Randomness hidden) (keys : Fin 512 → Pair) :
    Measurable (fun ω => ciphertexts (hashes ω) hidden random keys) := by
  apply measurable_pi_lambda
  intro i
  let value := AffineTable.share
    ((mapHidden hidden random.offsets random.scales random.chains i.1.1).params i.1.2.1)
    (random.tableMasks i.1.1 i.1.2.1 i.1.2.2) i.1.2.2 i.2
  exact (Measurable.of_discrete : Measurable (AffineTable.encrypt value)).comp (hh _)

theorem garble_measurable {Ω : Type*} [MeasurableSpace Ω]
    (hashes : Ω → Hash) (hh : ∀ q, Measurable (fun ω => hashes ω q))
    (hidden : Hidden) (random : Randomness hidden) (keys : Fin 512 → Pair) :
    Measurable (fun ω => Scheme.encode (Randomized.garble (hashes ω) hidden random keys)) := by
  simp only [garble_fromHalves]
  exact (Measurable.of_discrete : Measurable fromHalves).comp
    (ciphertexts_measurable hashes hh hidden random keys)

def idealCiphertexts (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (input : Input) (active : Fin 512 → Label) (inactive : InactiveCiphertexts)
    (index : Slot × Bool) : Label :=
  if index.2 = bitsFor index.1.2.1 input index.1.2.2 then
    AffineTable.encrypt (AffineTable.share
      ((mapHidden hidden random.offsets random.scales random.chains index.1.1).params index.1.2.1)
      (random.tableMasks index.1.1 index.1.2.1 index.1.2.2) index.1.2.2 index.2)
      (AffineTable.pad hash (active (tableWire index.1.2.1 index.1.2.2))
        (ProjectiveMap.purpose index.1.1.val index.1.2.1) index.1.2.2.val)
  else inactive index.1

theorem ideal_fromHalves (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (input : Input) (active : Fin 512 → Label) (inactive : InactiveCiphertexts) :
    IdealView.garble hash input hidden random active inactive =
      fromHalves (idealCiphertexts hash hidden random input active inactive) := rfl

theorem ideal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (hashes : Ω → Hash) (hh : ∀ q, Measurable (fun ω => hashes ω q))
    (hidden : Hidden) (random : Randomness hidden) (input : Input) (active : Fin 512 → Label)
    (inactive : Ω → InactiveCiphertexts) (hc : Measurable inactive) :
    Measurable (fun ω => IdealView.garble (hashes ω) input hidden random active (inactive ω)) := by
  simp only [ideal_fromHalves]
  apply (Measurable.of_discrete : Measurable fromHalves).comp
  apply measurable_pi_lambda
  intro i
  by_cases h : i.2 = bitsFor i.1.2.1 input i.1.2.2
  · simp only [idealCiphertexts, if_pos h]
    exact (Measurable.of_discrete : Measurable (AffineTable.encrypt _)).comp (hh _)
  · simp only [idealCiphertexts, if_neg h]
    exact (measurable_pi_apply i.1).comp hc

end G1Release.Submission.GarbleMeasurable
