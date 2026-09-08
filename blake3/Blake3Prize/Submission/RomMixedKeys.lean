import Blake3Prize.Submission.RomLamportLaw

/-! External pairs have the challenge's distinct-pair distribution. Internal
pairs are unrestricted independent labels. Conditioning on each selected
label therefore leaves either a uniform complement or a uniform full label;
no rejection sampler or pseudorandom-generator assumption is needed. -/
namespace Blake3Prize.Submission.RomMixedKeys
open SecretRelease MeasureTheory ProbabilityTheory

abbrev RawPair := Bool → Label
abbrev Keys (external internal : Nat) := (Fin external → Pair) × (Fin internal → RawPair)
abbrev Active (external internal : Nat) := (Fin external → Label) × (Fin internal → Label)
abbrev Ranks (external internal : Nat) :=
  (Fin external → RomLamportLaw.Rank) × (Fin internal → Label)

def rawPairEquiv (bit : Bool) : RawPair ≃ Label × Label where
  toFun key := (key bit,key (!bit))
  invFun pair b := if b = bit then pair.1 else pair.2
  left_inv key := by funext b; cases bit <;> cases b <;> rfl
  right_inv pair := by cases bit <;> rfl

def rawKeysEquiv (bits : Fin n → Bool) :
    (Fin n → RawPair) ≃ (Fin n → Label) × (Fin n → Label) where
  toFun keys := (fun i => keys i (bits i),fun i => keys i (!(bits i)))
  invFun parts i := (rawPairEquiv (bits i)).symm (parts.1 i,parts.2 i)
  left_inv keys := by funext i; exact (rawPairEquiv (bits i)).symm_apply_apply (keys i)
  right_inv parts := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((rawPairEquiv (bits i)).apply_symm_apply (parts.1 i,parts.2 i))
    · exact congrArg Prod.snd ((rawPairEquiv (bits i)).apply_symm_apply (parts.1 i,parts.2 i))

noncomputable def split (externalBits : Fin e → Bool) (internalBits : Fin k → Bool) :
    Keys e k ≃ Active e k × Ranks e k :=
  ((RomLamportLaw.keysEquiv externalBits).prodCongr (rawKeysEquiv internalBits)).trans
    (Equiv.prodProdProdComm _ _ _ _)

theorem split_preserving (externalBits : Fin e → Bool) (internalBits : Fin k → Bool) :
    MeasurePreserving (split externalBits internalBits)
      (uniformOn (Set.univ : Set (Keys e k)))
      ((uniformOn (Set.univ : Set (Active e k))).prod
        (uniformOn (Set.univ : Set (Ranks e k)))) := by
  rw [RomLamportLaw.prod_uniform_univ]
  exact RomFiniteProbability.uniform_equiv (split externalBits internalBits)

theorem split_external_active (externalBits : Fin e → Bool) (internalBits : Fin k → Bool)
    (keys : Keys e k) (i : Fin e) :
    (split externalBits internalBits keys).1.1 i = (keys.1 i).get (externalBits i) := rfl

theorem split_internal_active (externalBits : Fin e → Bool) (internalBits : Fin k → Bool)
    (keys : Keys e k) (i : Fin k) :
    (split externalBits internalBits keys).1.2 i = keys.2 i (internalBits i) := rfl

theorem split_internal_hidden (externalBits : Fin e → Bool) (internalBits : Fin k → Bool)
    (keys : Keys e k) (i : Fin k) :
    (split externalBits internalBits keys).2.2 i = keys.2 i (!(internalBits i)) := rfl

end Blake3Prize.Submission.RomMixedKeys
