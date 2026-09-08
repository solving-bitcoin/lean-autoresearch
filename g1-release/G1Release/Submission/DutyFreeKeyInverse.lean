import G1Release.Submission.DutyFreeConditionalKeys
import G1Release.Submission.DutyFreeGuessLaw
import G1Release.Submission.DutyFreeGameViews

/-! After conditioning on all released labels, the ideal adversary view is
constant in the hidden ranks and bridge keys. These identities connect the
finite key decomposition to the concrete serialized view and query game. -/
namespace G1Release.Submission.DutyFreeKeyInverse
open SecretRelease G1Release.Protected DutyFreeConditionalKeys DutyFreeRealIdeal
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def keys (input : Input) (revealed : Revealed input) (hidden : Hidden) : KeyPair :=
  (split input).symm (revealed,hidden)

theorem external_keys (input : Input) (revealed : Revealed input) (hidden : Hidden) :
    (keys input revealed hidden).1 =
      (LamportLaw.keysEquiv (fun wire : Fin 512 => (inputCodec.encode input)[wire.val])).symm
        (revealed.1,hidden.1) := rfl

private theorem pair_active (bit : Bool) (label : Label) (rank : LamportLaw.Rank) :
    ((LamportLaw.pairEquiv bit).symm (label,rank)).get bit = label := by
  cases bit <;> rfl

private theorem pair_opposite (bit : Bool) (label : Label) (rank : LamportLaw.Rank) :
    ((LamportLaw.pairEquiv bit).symm (label,rank)).get (!bit) =
      ((LamportLaw.complementEquiv label).symm rank).val := by
  cases bit <;> rfl

theorem active_keys (input : Input) (revealed : Revealed input) (hidden : Hidden) :
    active (keys input revealed hidden).1 input = revealed.1 := by
  rw [external_keys]
  funext wire
  simp only [active, LamportLaw.keysEquiv, Equiv.coe_fn_symm_mk]
  exact pair_active _ _ _

theorem hot_keys (input : Input) (revealed : Revealed input) (hidden : Hidden) :
    (keys input revealed hidden).2 = (DutyFreeKeySplit.split input).symm (hidden.2,revealed.2) := rfl

theorem secret_keys (input : Input) (revealed : Revealed input) (hidden : Hidden) :
    DutyFreeQueryGuessing.secrets (keys input revealed hidden).1 (keys input revealed hidden).2 input =
      DutyFreeGuessLaw.labels revealed.1 (LamportLaw.hiddenFromRanks revealed.1 hidden.1,hidden.2) := by
  funext index
  cases index with
  | inl wire =>
    simp only [DutyFreeQueryGuessing.secrets, DutyFreeGuessLaw.labels]
    rw [external_keys]
    simp only [LamportLaw.keysEquiv, LamportLaw.hiddenFromRanks, Equiv.coe_fn_symm_mk]
    exact pair_opposite _ _ _
  | inr id =>
    simp only [DutyFreeQueryGuessing.secrets, DutyFreeGuessLaw.labels]
    rw [hot_keys]
    exact DutyFreeKeySplit.selected input hidden.2 revealed.2 id

theorem ideal_independent (privateValue : Private) (random : CosetSampler.Randomness privateValue)
    (input : Input) (revealed : Revealed input) (source target : Hidden) (oracle : ExtendedOracle) :
    DutyFreeGameViews.ideal privateValue random input revealed.1 (keys input revealed source).2 oracle =
      DutyFreeGameViews.ideal privateValue random input revealed.1 (keys input revealed target).2 oracle := by
  unfold DutyFreeGameViews.ideal
  rw [hot_keys, hot_keys, DutyFreeKeySplit.garble_independent _ _ _ _ _ source.2 target.2]

def anchor : Hidden := (fun _ => ⟨0, by norm_num⟩, fun _ => Vector.replicate 32 0)

noncomputable def view (privateValue : Private) (random : CosetSampler.Randomness privateValue)
    (input : Input) (revealed : Revealed input) (oracle : ExtendedOracle) : View challenge :=
  DutyFreeGameViews.ideal privateValue random input revealed.1 (keys input revealed anchor).2 oracle

theorem ideal_eq_view (privateValue : Private) (random : CosetSampler.Randomness privateValue)
    (input : Input) (revealed : Revealed input) (hidden : Hidden) (oracle : ExtendedOracle) :
    DutyFreeGameViews.ideal privateValue random input (active (keys input revealed hidden).1 input)
        (keys input revealed hidden).2 oracle = view privateValue random input revealed oracle := by
  rw [active_keys]
  exact ideal_independent privateValue random input revealed hidden anchor oracle

end G1Release.Submission.DutyFreeKeyInverse
