import Blake3Prize.Migration.Legacy.ROM
import Blake3Prize.Protected.Wire

/-! Migration evidence, outside the accepted import graph. The historical
768-fold independent pair law is exactly the shared product of uniform input
and output key spaces. The oracle and coins are unchanged. -/
namespace Blake3Prize.Migration
open Blake3Prize.Protected MeasureTheory ProbabilityTheory

abbrev IK := Fin 512 → SecretRelease.Pair
abbrev OK := Fin 256 → SecretRelease.Pair
local instance : MeasurableSpace IK := ⊤
local instance : MeasurableSpace OK := ⊤

/-- Split at the original input/output boundary, preserving the bit order. -/
def splitKeys : Legacy.ROM.LabelMaterial ≃ IK × OK where
  toFun m := (fun i => m ⟨i.val,by omega⟩, fun i => m ⟨512+i.val,by omega⟩)
  invFun p := fun i => if h : i.val < 512 then p.1 ⟨i.val,h⟩ else p.2 ⟨i.val-512,by omega⟩
  left_inv := by
    intro m; funext i
    dsimp
    split
    · rfl
    · exact congrArg m (Fin.ext (by dsimp; omega))
  right_inv := by
    intro p
    apply Prod.ext <;> funext i <;> simp [i.isLt]

private theorem uniform_equiv {A B : Type} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] (e : A ≃ B) :
    (uniformOn (Set.univ : Set A)).map e = uniformOn (Set.univ : Set B) := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq_symm_apply]
  simp [he, uniformOn_univ, Fintype.card_congr e]

private theorem uniform_prod {A B : Type} [Finite A] [Finite B] [Nonempty A] [Nonempty B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    uniformOn (Set.univ : Set (A × B)) =
      (uniformOn (Set.univ : Set A)).prod (uniformOn (Set.univ : Set B)) := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [uniformOn_univ, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv]

/-- An exact equality of distributions, not a heuristic independence claim. -/
theorem splitKeys_law : Legacy.ROM.materialLaw.map splitKeys =
    (uniformOn (Set.univ : Set IK)).prod (uniformOn (Set.univ : Set OK)) := by
  have hm : Legacy.ROM.materialLaw = uniformOn (Set.univ : Set Legacy.ROM.LabelMaterial) := by
    unfold Legacy.ROM.materialLaw Legacy.ROM.pairLaw
    rw [Measure.infinitePi_eq_pi, ← uniformOn_pi]
    simp
  rw [hm, uniform_equiv splitKeys, uniform_prod]

/-- The independent input and output key laws, coins and shared oracle are
transported together; reassociation changes no probabilities. -/
def splitSample (n : Nat) : Legacy.ROM.Sample n → IK × OK × SecretRelease.Bytes n × SecretRelease.ROM.Oracle :=
  fun s => ((splitKeys s.1).1, (splitKeys s.1).2, s.2)

theorem splitSample_law (n : Nat) :
    (Legacy.ROM.experimentLaw n).map (splitSample n) =
      (uniformOn (Set.univ : Set IK)).prod ((uniformOn (Set.univ : Set OK)).prod
        ((Legacy.ROM.coinsLaw n).prod Legacy.ROM.oracleLaw)) := by
  let tail := (Legacy.ROM.coinsLaw n).prod Legacy.ROM.oracleLaw
  have hm := Measure.map_prod_map Legacy.ROM.materialLaw tail
    (measurable_of_countable splitKeys) measurable_id
  rw [Measure.map_id, splitKeys_law] at hm
  have ha := Measure.prodAssoc_prod (μ := uniformOn (Set.univ : Set IK))
    (ν := uniformOn (Set.univ : Set OK)) (τ := tail)
  rw [hm, Measure.map_map (MeasurableEquiv.measurable _) ((measurable_of_countable splitKeys).prodMap measurable_id)] at ha
  exact ha

/-- This is literally the shared contract's probability law, including its
explicit discrete key sigma-algebras, rather than a parallel model of it. -/
theorem shared_law (s : SecretRelease.Scheme challenge) :
    (Legacy.ROM.experimentLaw s.randomnessBytes).map (splitSample s.randomnessBytes) =
      SecretRelease.ROM.law s := by
  rw [splitSample_law]
  rfl

/-- Old pair functions become distinct shared keys without correlations. -/
def pairs {n : Nat} (keys : Fin n → SecretRelease.Pair) : Fin n → Bool → Label :=
  fun i b => (keys i).get b

theorem pairs_distinct {n : Nat} (keys : Fin n → SecretRelease.Pair) : DistinctPairs (pairs keys) :=
  fun i => (keys i).property

/-- Vector-to-byte views use the same sequence of labels as the old game. -/
theorem input_disclosure (h : SecretRelease.Hash) (keys : IK) (input : Input) :
    challenge.inputs.reveal h keys input = SecretRelease.pack (activeInput (pairs keys) input).toList := by
  simp only [challenge, SecretRelease.Lamport, bitCodec, activeInput, inputBit, pairs,
    Vector.toList_ofFn, List.ofFn_eq_map, Vector.getElem_map]
  rfl

theorem output_disclosure (h : SecretRelease.Hash) (keys : OK) (output : Output) :
    challenge.outputs.reveal h keys output = SecretRelease.pack (activeOutput (pairs keys) output).toList := by
  simp only [challenge, SecretRelease.Lamport, bitCodec, activeOutput, pairs,
    Vector.toList_ofFn, List.ofFn_eq_map, Vector.getElem_map]
  rfl

theorem wins_preserved (h : SecretRelease.Hash) (input : Input) (ik : IK) (ok : OK)
    (guess : Fin 768 × Label) :
    challenge.wins h () input ik ok guess ↔ Legacy.SecretRelease.Wins (pairs ik) (pairs ok) input guess := by
  rfl

/-- Public vector labels are transported to the exact byte channels. -/
def viewBytes (v : Legacy.SecretRelease.View) : SecretRelease.View challenge :=
  ⟨v.inputValue,v.artifact,SecretRelease.pack v.inputs.toList,SecretRelease.pack v.outputs.toList⟩

/-- Any new scheme with the same serialized garbler has the same observations.
No evaluator implementation or gate representation appears in this equality. -/
theorem views_preserved (old : Legacy.Scheme) (new : SecretRelease.Scheme challenge)
    (sameCoins : new.randomnessBytes = old.randomnessBytes)
    (garbles : ∀ h coins ik ok,
      new.garbleBytes h coins () ik ok = old.garbleBytes h (coins.cast sameCoins)
        (pairs ik) (pairs ok)) (x : Input) (sample : SecretRelease.ROM.Sample new) :
    SecretRelease.ROM.view new () x sample = viewBytes (Legacy.ROM.view old x
      (splitKeys.symm (sample.1,sample.2.1),sample.2.2.1.cast sameCoins,sample.2.2.2)) := by
  have hi : Legacy.ROM.inputPairs (splitKeys.symm (sample.1,sample.2.1)) = pairs sample.1 := by
    funext i b
    simp [Legacy.ROM.inputPairs, splitKeys, pairs, SecretRelease.Pair.get, i.isLt]
  have ho : Legacy.ROM.outputPairs (splitKeys.symm (sample.1,sample.2.1)) = pairs sample.2.1 := by
    funext i b
    simp [Legacy.ROM.outputPairs, splitKeys, pairs, SecretRelease.Pair.get]
  unfold SecretRelease.ROM.view Legacy.ROM.view viewBytes
  simp only [hi, ho, garbles]
  exact congrArg₂ (fun a b => (⟨x,
    old.garbleBytes (SecretRelease.ROM.hash sample.2.2.2)
      (sample.2.2.1.cast sameCoins) (pairs sample.1) (pairs sample.2.1),a,b⟩ :
        SecretRelease.View challenge))
    (input_disclosure (SecretRelease.ROM.hash sample.2.2.2) sample.1 x)
    (output_disclosure (SecretRelease.ROM.hash sample.2.2.2) sample.2.1 (reference x))

/-- Legacy bounds on all pairs imply the shared bound on valid distinct pairs.
The discarded invalid-pair cases are outside the declared key space. -/
theorem bound_on_valid_keys (old : Legacy.Scheme) (new : SecretRelease.Scheme challenge)
    (sameCoins : new.randomnessBytes = old.randomnessBytes)
    (garbles : ∀ h coins ik ok,
      new.garbleBytes h coins () ik ok = old.garbleBytes h (coins.cast sameCoins)
        (pairs ik) (pairs ok)) (n : Nat) (bound : Legacy.ArtifactBound old n) :
    SecretRelease.ArtifactBound new n := by
  intro h coins p ik ok
  cases p
  rw [garbles]
  exact bound h _ _ _

example : challenge.withholding = none := rfl
example : challenge.privateLeakage = none := rfl
example : challenge.correctness = .exact := rfl

theorem bound_preserved (q : Nat) : (challenge.rom.error q : ENNReal) = Legacy.ROM.successBound q := by
  simp only [challenge, SecretRelease.Examples.rom128, Legacy.ROM.successBound]
  rw [← ENNReal.coe_nnratCast]
  push_cast
  rfl
end Blake3Prize.Migration
