import WotsLamport.Submission.HonestQueryBudget
import WotsLamport.Protected.Adaptive

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected OracleSpec OracleComp MeasureTheory

abbrev InitialData := Keys × (Fin 256 → Pair) × Bytes randomnessBytes
local instance : MeasurableSpace Keys := ⊤
local instance : MeasurableSpace (Fin 256 → Pair) := ⊤

def selectedOutputBytes (labels : Fin 256 → Pair) (m : Message) : ByteArray :=
  pack ((List.finRange 256).map fun i => (labels i).get (outputCodec.encode m)[i.val])

def releaseViewProgram (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair)
    (m : Message) : Program (View challenge) := do
  let artifact ← wrappedPrepareProgram coins keys labels
  let signature ← signProgram keys m
  pure ⟨m, artifact, signatureBytes signature, selectedOutputBytes labels m⟩

def preReleaseViewProgram (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair)
    (m : Message) : Program (PreReleaseView challenge) := do
  let artifact ← wrappedPrepareProgram coins keys labels
  pure ⟨m, artifact⟩

theorem run_releaseViewProgram (m : Message) (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2)
      (releaseViewProgram (ByteArray.mk ω.2.2.1.toArray) ω.1 ω.2.1 m) =
      ROM.view (wrapped construction) () m ω := by
  simp only [releaseViewProgram, run_bind, run_pure, run_wrappedPrepareProgram, run_signProgram]
  rfl

theorem run_preReleaseViewProgram (m : Message) (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2)
      (preReleaseViewProgram (ByteArray.mk ω.2.2.1.toArray) ω.1 ω.2.1 m) =
      ROM.preReleaseView (wrapped construction) () m ω := by
  simp only [preReleaseViewProgram, run_bind, run_pure, run_wrappedPrepareProgram]
  rfl

def releaseGameProgram (m : Message) (a : View challenge → Program challenge.Claim)
    (initial : InitialData) : Program Bool := do
  let view ← releaseViewProgram (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1 m
  let claim ← a view
  pure (decide (claim.2 = (initial.2.1 claim.1).get (!(outputCodec.encode m)[claim.1.val])))

def withholdingGameProgram (m : Message) (a : PreReleaseView challenge → Program challenge.Claim)
    (initial : InitialData) : Program Bool := do
  let view ← preReleaseViewProgram (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1 m
  let claim ← a view
  pure (decide (claim.2 = (initial.2.1 claim.1).get false ∨ claim.2 = (initial.2.1 claim.1).get true))

def adaptiveGameProgram (a : AdaptiveAdversary) (initial : InitialData) : Program Bool := do
  let artifact ← wrappedPrepareProgram (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1
  let selected ← a.choose artifact
  let signature ← signProgram initial.1 selected.1
  let claim ← a.finish selected.2 ⟨selected.1, artifact, signatureBytes signature,
    selectedOutputBytes initial.2.1 selected.1⟩
  pure (decide (claim.2 = (initial.2.1 claim.1).get (!(outputCodec.encode selected.1)[claim.1.val])))

theorem releaseGame_success (m : Message) (a : View challenge → Program challenge.Claim)
    (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2) (releaseGameProgram m a (ω.1, ω.2.1, ω.2.2.1)) = true ↔
      ω ∈ ROM.winEvent (wrapped construction) () m a := by
  simp only [releaseGameProgram, run_bind, run_pure, run_releaseViewProgram, decide_eq_true_eq]
  rfl

theorem withholdingGame_success (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2) (withholdingGameProgram m a (ω.1, ω.2.1, ω.2.2.1)) = true ↔
      ω ∈ ROM.preReleaseEvent (wrapped construction)
        (fun _ _ _ _ labels claim => claim.2 = (labels claim.1).get false ∨
          claim.2 = (labels claim.1).get true) () m a := by
  simp only [withholdingGameProgram, run_bind, run_pure, run_preReleaseViewProgram, decide_eq_true_eq]
  rfl

theorem adaptiveGame_success (a : AdaptiveAdversary) (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2) (adaptiveGameProgram a (ω.1, ω.2.1, ω.2.2.1)) = true ↔
      ω ∈ adaptiveEvent (wrapped construction) a := by
  simp only [adaptiveGameProgram, run_bind, run_pure, run_wrappedPrepareProgram,
    run_signProgram, decide_eq_true_eq]
  rfl

/-- Initial keys, labels and coins are finite; the oracle remains the protected
infinite product. Program reification establishes measurability without giving
the adversary access to an extra oracle or restricting its local computation. -/
theorem measurable_game_run (game : InitialData → Program Bool) :
    Measurable (fun ω : ROM.Sample (wrapped construction) =>
      ROM.run (ROM.hash ω.2.2.2) (game (ω.1, ω.2.1, ω.2.2.1))) := by
  apply measurable_program_family game
  · exact measurable_snd.snd.snd
  · exact measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst)

theorem measurable_release_event (m : Message) (a : View challenge → Program challenge.Claim) :
    MeasurableSet (ROM.winEvent (wrapped construction) () m a) := by
  have h := measurable_game_run (releaseGameProgram m a) (measurableSet_singleton true)
  convert h using 1
  ext ω
  exact (releaseGame_success m a ω).symm

theorem measurable_withholding_event (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) :
    MeasurableSet (ROM.preReleaseEvent (wrapped construction)
      (fun _ _ _ _ labels claim => claim.2 = (labels claim.1).get false ∨
        claim.2 = (labels claim.1).get true) () m a) := by
  have h := measurable_game_run (withholdingGameProgram m a) (measurableSet_singleton true)
  convert h using 1
  ext ω
  exact (withholdingGame_success m a ω).symm

theorem measurable_adaptive_event (a : AdaptiveAdversary) :
    MeasurableSet (adaptiveEvent (wrapped construction) a) := by
  have h := measurable_game_run (adaptiveGameProgram a) (measurableSet_singleton true)
  convert h using 1
  ext ω
  exact (adaptiveGame_success a ω).symm

theorem releaseViewProgram_query_bound (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair)
    (m : Message) : IsTotalQueryBound (releaseViewProgram coins keys labels m) honestReleaseQueries := by
  exact isTotalQueryBound_bind (wrappedPrepareProgram_query_bound coins keys labels)
    (fun artifact => isTotalQueryBound_bind (signProgram_query_bound keys m)
      (fun signature => pure_query_bound ⟨m, artifact, signatureBytes signature, selectedOutputBytes labels m⟩ 0))

theorem preReleaseViewProgram_query_bound (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair)
    (m : Message) : IsTotalQueryBound (preReleaseViewProgram coins keys labels m) honestSetupQueries := by
  exact isTotalQueryBound_bind (wrappedPrepareProgram_query_bound coins keys labels)
    (fun artifact => pure_query_bound ⟨m, artifact⟩ 0)

theorem withholdingGameProgram_query_bound (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim)
    (q : Nat) (bound : ROM.Bounded a q) (initial : InitialData) :
    IsTotalQueryBound (withholdingGameProgram m a initial) (honestSetupQueries+q) := by
  exact isTotalQueryBound_bind (preReleaseViewProgram_query_bound _ _ _ m)
    (fun view => isTotalQueryBound_bind (bound view) (fun claim => pure_query_bound _ 0))

theorem releaseGameProgram_query_bound (m : Message) (a : View challenge → Program challenge.Claim)
    (q : Nat) (bound : ROM.Bounded a q) (initial : InitialData) :
    IsTotalQueryBound (releaseGameProgram m a initial) (honestReleaseQueries+q) := by
  exact isTotalQueryBound_bind (releaseViewProgram_query_bound _ _ _ m)
    (fun view => isTotalQueryBound_bind (bound view) (fun claim => pure_query_bound _ 0))

theorem adaptiveGameProgram_query_bound (a : AdaptiveAdversary) (q₁ q₂ : Nat)
    (chooseBound : ROM.Bounded a.choose q₁)
    (finishBound : ∀ state, ROM.Bounded (a.finish state) q₂) (initial : InitialData) :
    IsTotalQueryBound (adaptiveGameProgram a initial) (honestReleaseQueries+q₁+q₂) := by
  have h := isTotalQueryBound_bind (wrappedPrepareProgram_query_bound
      (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1)
    (fun artifact => isTotalQueryBound_bind (chooseBound artifact)
      (fun selected => isTotalQueryBound_bind (signProgram_query_bound initial.1 selected.1)
        (fun signature => isTotalQueryBound_bind (finishBound selected.2
          ⟨selected.1, artifact, signatureBytes signature, selectedOutputBytes initial.2.1 selected.1⟩)
          (fun claim => pure_query_bound
            (decide (claim.2 = (initial.2.1 claim.1).get (!(outputCodec.encode selected.1)[claim.1.val]))) 0))))
  simpa only [adaptiveGameProgram, honestReleaseQueries, Nat.add_zero,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

end WotsLamport.Submission
