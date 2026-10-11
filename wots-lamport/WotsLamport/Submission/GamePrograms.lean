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
  have setupRun := run_wrappedPrepareProgram (ROM.hash ω.2.2.2) ω.2.2.1 ω.1 ω.2.1
  have signatureRun := run_signProgram (ROM.hash ω.2.2.2) ω.1 m
  unfold releaseViewProgram
  generalize setupEq : wrappedPrepareProgram (ByteArray.mk ω.2.2.1.toArray) ω.1 ω.2.1 = setup at *
  generalize signatureEq : signProgram ω.1 m = signing at *
  simp only [run_bind, run_map, run_pure, setupRun, signatureRun]
  rfl

theorem run_preReleaseViewProgram (m : Message) (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2)
      (preReleaseViewProgram (ByteArray.mk ω.2.2.1.toArray) ω.1 ω.2.1 m) =
      ROM.preReleaseView (wrapped construction) () m ω := by
  have setupRun := run_wrappedPrepareProgram (ROM.hash ω.2.2.2) ω.2.2.1 ω.1 ω.2.1
  unfold preReleaseViewProgram
  generalize setupEq : wrappedPrepareProgram (ByteArray.mk ω.2.2.1.toArray) ω.1 ω.2.1 = setup at *
  simp only [run_bind, run_map, run_pure, setupRun]
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
  simp only [releaseGameProgram, run_bind, run_map, run_pure, run_releaseViewProgram, decide_eq_true_eq]
  rfl

theorem withholdingGame_success (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2) (withholdingGameProgram m a (ω.1, ω.2.1, ω.2.2.1)) = true ↔
      ω ∈ ROM.preReleaseEvent (wrapped construction)
        (fun _ _ _ _ labels claim => claim.2 = (labels claim.1).get false ∨
          claim.2 = (labels claim.1).get true) () m a := by
  simp only [withholdingGameProgram, run_bind, run_map, run_pure, run_preReleaseViewProgram, decide_eq_true_eq]
  rfl

theorem adaptiveGame_success (a : AdaptiveAdversary) (ω : ROM.Sample (wrapped construction)) :
    ROM.run (ROM.hash ω.2.2.2) (adaptiveGameProgram a (ω.1, ω.2.1, ω.2.2.1)) = true ↔
      ω ∈ adaptiveEvent (wrapped construction) a := by
  have setupRun := run_wrappedPrepareProgram (ROM.hash ω.2.2.2) ω.2.2.1 ω.1 ω.2.1
  have signatureRun := fun m => run_signProgram (ROM.hash ω.2.2.2) ω.1 m
  unfold adaptiveGameProgram
  generalize setupEq : wrappedPrepareProgram (ByteArray.mk ω.2.2.1.toArray) ω.1 ω.2.1 = setup at *
  generalize signatureEq : signProgram ω.1 = signing at *
  simp only [run_bind, run_map, run_pure, setupRun, signatureRun, decide_eq_true_eq]
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
  unfold releaseViewProgram honestReleaseQueries
  with_reducible
    simpa only [pairProgram] using
      (pair_query_bound (wrappedPrepareProgram coins keys labels) (signProgram keys m)
        (fun artifact signature => (⟨m, artifact, signatureBytes signature,
          selectedOutputBytes labels m⟩ : View challenge)) honestSetupQueries (67*15)
        (wrappedPrepareProgram_query_bound coins keys labels) (signProgram_query_bound keys m))

theorem preReleaseViewProgram_query_bound (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair)
    (m : Message) : IsTotalQueryBound (preReleaseViewProgram coins keys labels m) honestSetupQueries := by
  unfold preReleaseViewProgram
  with_reducible exact bind_pure_query_bound (wrappedPrepareProgram coins keys labels)
    (fun artifact => (⟨m, artifact⟩ : PreReleaseView challenge)) honestSetupQueries
    (wrappedPrepareProgram_query_bound coins keys labels)

theorem withholdingGameProgram_query_bound (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim)
    (q : Nat) (bound : ROM.Bounded a q) (initial : InitialData) :
    IsTotalQueryBound (withholdingGameProgram m a initial) (honestSetupQueries+q) := by
  change ∀ view, IsTotalQueryBound (a view) q at bound
  unfold withholdingGameProgram
  with_reducible exact isTotalQueryBound_bind
    (oa := preReleaseViewProgram (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1 m)
    (preReleaseViewProgram_query_bound _ _ _ m)
    (fun view => bind_pure_query_bound (a view)
      (fun claim => decide (claim.2 = (initial.2.1 claim.1).get false ∨
        claim.2 = (initial.2.1 claim.1).get true)) q (bound view))

theorem releaseGameProgram_query_bound (m : Message) (a : View challenge → Program challenge.Claim)
    (q : Nat) (bound : ROM.Bounded a q) (initial : InitialData) :
    IsTotalQueryBound (releaseGameProgram m a initial) (honestReleaseQueries+q) := by
  change ∀ view, IsTotalQueryBound (a view) q at bound
  unfold releaseGameProgram
  with_reducible exact isTotalQueryBound_bind
    (oa := releaseViewProgram (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1 m)
    (releaseViewProgram_query_bound _ _ _ m)
    (fun view => bind_pure_query_bound (a view)
      (fun claim => decide (claim.2 = (initial.2.1 claim.1).get (!(outputCodec.encode m)[claim.1.val])))
      q (bound view))

theorem adaptiveGameProgram_query_bound (a : AdaptiveAdversary) (q₁ q₂ : Nat)
    (chooseBound : ROM.Bounded a.choose q₁)
    (finishBound : ∀ state, ROM.Bounded (a.finish state) q₂) (initial : InitialData) :
    IsTotalQueryBound (adaptiveGameProgram a initial) (honestReleaseQueries+q₁+q₂) := by
  change ∀ artifact, IsTotalQueryBound (a.choose artifact) q₁ at chooseBound
  change ∀ state view, IsTotalQueryBound (a.finish state view) q₂ at finishBound
  have budgetEq : honestReleaseQueries+q₁+q₂ = honestSetupQueries+(q₁+(67*15+q₂)) := by
    unfold honestReleaseQueries
    omega
  rw [budgetEq]
  unfold adaptiveGameProgram
  with_reducible exact isTotalQueryBound_bind
    (oa := wrappedPrepareProgram (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1)
    (wrappedPrepareProgram_query_bound (ByteArray.mk initial.2.2.toArray) initial.1 initial.2.1)
    (fun artifact => isTotalQueryBound_bind (chooseBound artifact)
      (fun selected => isTotalQueryBound_bind (oa := signProgram initial.1 selected.1)
        (signProgram_query_bound initial.1 selected.1)
        (fun signature => bind_pure_query_bound
          (a.finish selected.2 ⟨selected.1, artifact, signatureBytes signature,
            selectedOutputBytes initial.2.1 selected.1⟩)
          (fun claim => decide
            (claim.2 = (initial.2.1 claim.1).get (!(outputCodec.encode selected.1)[claim.1.val])))
          q₂ (finishBound selected.2 _))))

end WotsLamport.Submission
