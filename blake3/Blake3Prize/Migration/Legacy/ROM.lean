import Blake3Prize.Migration.Legacy.SecretRelease
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
-- ProductMeasure supplies infinitePi and its probability instance. Importing
-- derived independence results also loads unused density and moment proofs.
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn

namespace Blake3Prize.Protected.Legacy.ROM
open MeasureTheory ProbabilityTheory OracleSpec OracleComp
open SecretRelease

/-- VCVio supplies the free oracle computation and the adaptive query bound.
All attacker oracle access is explicit; ordinary local computation is free. -/
abbrev OracleProgram (α : Type) := OracleComp (ByteArray →ₒ Label) α

def runProgram (hash : PublicHash) (program : OracleProgram α) : α :=
  Id.run (simulateQ (QueryImpl.ofFn hash) program)

theorem runProgram_pure (hash : PublicHash) (x : α) :
    runProgram hash (pure x) = x := by simp [runProgram]

private theorem bytes_finite (n : Nat) : Finite (Vector UInt8 n) := by
  apply Finite.of_injective (fun bytes : Vector UInt8 n => fun i : Fin n => (bytes.get i).toFin)
  intro left right hequal
  apply Vector.ext
  intro i hi
  apply UInt8.ext
  exact Fin.ext_iff.mp (congrFun hequal ⟨i, hi⟩)

instance (n : Nat) : Finite (Vector UInt8 n) := bytes_finite n
instance (n : Nat) : MeasurableSpace (Vector UInt8 n) := ⊤

/-- Uniform ordered DISTINCT pairs, independently for all 768 bit positions.
This conditioning excludes equal labels within a pair and does not introduce
any correlation between different pairs or the garbler's randomness. -/
abbrev Pair := {p : Label × Label // p.1 ≠ p.2}
instance : Nonempty Pair :=
  ⟨⟨(Vector.replicate 32 0, Vector.replicate 32 1), by decide⟩⟩
instance : MeasurableSpace Pair := ⊤

abbrev LabelMaterial := Fin 768 → Pair
abbrev OracleAddress := List (Fin 256)
abbrev Oracle := OracleAddress → Label
abbrev Sample (n : Nat) := LabelMaterial × (Randomness n × Oracle)

noncomputable def labelLaw : Measure Label := uniformOn Set.univ
noncomputable def pairLaw : Measure Pair := uniformOn Set.univ
noncomputable def coinsLaw (n : Nat) : Measure (Randomness n) := uniformOn Set.univ

instance : IsProbabilityMeasure labelLaw := by unfold labelLaw; infer_instance
instance : IsProbabilityMeasure pairLaw := by unfold pairLaw; infer_instance
instance (n : Nat) : IsProbabilityMeasure (coinsLaw n) := by unfold coinsLaw; infer_instance

noncomputable def materialLaw : Measure LabelMaterial :=
  Measure.infinitePi fun _ => pairLaw
noncomputable def oracleLaw : Measure Oracle :=
  Measure.infinitePi fun _ => labelLaw

instance : IsProbabilityMeasure materialLaw := by unfold materialLaw; infer_instance
instance : IsProbabilityMeasure oracleLaw := by unfold oracleLaw; infer_instance

noncomputable def experimentLaw (n : Nat) : Measure (Sample n) :=
  materialLaw.prod ((coinsLaw n).prod oracleLaw)
instance (n : Nat) : IsProbabilityMeasure (experimentLaw n) := by
  unfold experimentLaw
  infer_instance

def oracleHash (oracle : Oracle) : PublicHash :=
  fun bytes => oracle (bytes.data.toList.map UInt8.toFin)

def inputPairs (material : LabelMaterial) : InputLabelPairs :=
  fun i b => let pair := (material ⟨i.val, by omega⟩).val
             if b then pair.2 else pair.1

def outputPairs (material : LabelMaterial) : OutputLabelPairs :=
  fun i b => let pair := (material ⟨512 + i.val, by omega⟩).val
             if b then pair.2 else pair.1

theorem inputPairs_distinct (material : LabelMaterial) : DistinctPairs (inputPairs material) := by
  intro i
  exact (material ⟨i.val, by omega⟩).property

theorem outputPairs_distinct (material : LabelMaterial) : DistinctPairs (outputPairs material) := by
  intro i
  exact (material ⟨512 + i.val, by omega⟩).property

abbrev Adversary := View → OracleProgram Guess

def view (s : Scheme) (input : Input) (sample : Sample s.randomnessBytes) : View :=
  let inputs := inputPairs sample.1
  let outputs := outputPairs sample.1
  ⟨input, s.garbleBytes (oracleHash sample.2.2) sample.2.1 inputs outputs,
    activeInput inputs input, activeOutput outputs (reference input)⟩

/-- The profile instantiates the common winning predicate with its sampled
secrets and VCVio attacker. One shared random function serves construction
and attacker, so repeated queries return the same answer. -/
def Wins (s : Scheme) (input : Input) (attack : Adversary)
    (sample : Sample s.randomnessBytes) : Prop :=
  let guess := runProgram (oracleHash sample.2.2) (attack (view s input sample))
  SecretRelease.Wins (inputPairs sample.1) (outputPairs sample.1) input guess

/-- Fixed classical profile: 128-bit query-work security, through 2^64 queries.
At q queries the success probability must be at most (q+1)/2^128. -/
def maxQueries : Nat := 2^64
noncomputable def successBound (q : Nat) : ENNReal := (q + 1 : ENNReal) / 2^128

/-- One-shot chosen-message conditional release. The universally quantified
attacker may know the chosen message and perform unlimited local computation;
only oracle access is bounded. There is no unbounded-query secrecy claim. -/
def Secrecy (s : Scheme) : Prop :=
  ∀ input q, q ≤ maxQueries → ∀ attack : Adversary,
    (∀ v, IsTotalQueryBound (attack v) q) →
    MeasurableSet {sample | Wins s input attack sample} ∧
    experimentLaw s.randomnessBytes {sample | Wins s input attack sample} ≤ successBound q

theorem experimentLaw_univ (n : Nat) : experimentLaw n Set.univ = 1 := measure_univ

theorem successBound_zero_lt_one : successBound 0 < 1 := by
  norm_num [successBound]

/-- A guard against vacuous security: a construction which always exposes an
opposite label to a zero-query attacker cannot obtain a secrecy certificate. -/
theorem not_secrecy_of_always_wins (s : Scheme) (input : Input) (attack : Adversary)
    (hqueries : ∀ v, IsTotalQueryBound (attack v) 0)
    (hwins : ∀ sample, Wins s input attack sample) : ¬ Secrecy s := by
  intro hsecure
  have hbound := (hsecure input 0 (Nat.zero_le _) attack hqueries).2
  have hevent : {sample | Wins s input attack sample} = Set.univ :=
    Set.eq_univ_of_forall hwins
  rw [hevent, experimentLaw_univ] at hbound
  exact (not_le_of_gt successBound_zero_lt_one) hbound

end Blake3Prize.Protected.Legacy.ROM
