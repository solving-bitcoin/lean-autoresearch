import Blake3Prize.Submission.RomMixedGuessing

namespace Blake3Prize.Submission.RomKeyMaterial
open SecretRelease RomMixedKeys RomMixedGuessing

abbrev KeySet := Keys 768 61186
abbrev KeyIndex := Index 768 61186

def boolFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i.val == 1
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rawEquiv : (Fin 2 → Label) ≃ RawPair where
  toFun f b := f (boolFin b)
  invFun f i := f (boolFin.symm i)
  left_inv f := by funext i; simp only [Equiv.apply_symm_apply]
  right_inv f := by funext b; simp only [Equiv.symm_apply_apply]

def coinEquiv (n : Nat) : Bytes (n*64) ≃ (Fin n → RawPair) :=
  (RomFiniteProbability.blockEquiv n 64).trans
    (Equiv.piCongrRight fun _ => (RomFiniteProbability.blockEquiv 2 32).trans rawEquiv)

/-- Read only the requested fixed-size slice. A function-valued cache can
be eta-expanded by the native compiler and recomputed on every lookup;
this direct bijective slice has constant cost per label instead. -/
def sampled (coins : Bytes (n*64)) : Fin n → RawPair := coinEquiv n coins

theorem sampled_eq (coins : Bytes (n*64)) : sampled coins = coinEquiv n coins := rfl

def externalEquiv : ((Fin 512 → Pair) × (Fin 256 → Pair)) ≃ (Fin 768 → Pair) where
  toFun keys i := if h : i.val < 512 then keys.1 ⟨i.val,h⟩
    else keys.2 ⟨i.val-512,by omega⟩
  invFun keys := (fun i => keys ⟨i.val,by omega⟩,fun i => keys ⟨512+i.val,by omega⟩)
  left_inv keys := by
    apply Prod.ext <;> funext i
    · simp [i.isLt]
    · simp
  right_inv keys := by
    funext i
    dsimp only
    split
    · rfl
    · exact congrArg keys (Fin.ext (by change 512+(i.val-512) = i.val; omega))

def assemble (coins : Bytes 3915904) (inputs : Fin 512 → Pair) (outputs : Fin 256 → Pair) :
    KeySet := (externalEquiv (inputs,outputs),sampled (n := 61186) coins)

def wire (n : Nat) : KeyIndex :=
  if h : n < 512 then .inl ⟨n,by omega⟩
  else if h' : n < 61698 then .inr ⟨n-512,by omega⟩ else .inl 0

def out (i : Fin 256) : KeyIndex := .inl ⟨512+i.val,by omega⟩
def wireKeys (keys : KeySet) (n : Nat) : Bool → Label := key keys (wire n)
def outKeys (keys : KeySet) (i : Fin 256) : Bool → Label := key keys (out i)

theorem wire_bit_of (external : Fin 768 → Bool) (internal : Fin 61186 → Bool) (known : Nat → Bool)
    (hi : ∀ i : Fin 512, external ⟨i.val,by omega⟩ = known i.val)
    (hk : ∀ i : Fin 61186, internal i = known (512+i.val)) (n : Nat) (hn : n < 61698) :
    bit external internal (wire n) = known n := by
  by_cases h : n < 512
  · rw [wire,dif_pos h]
    exact hi ⟨n,h⟩
  · rw [wire,dif_neg h,dif_pos hn]
    change internal ⟨n-512,by omega⟩ = known n
    exact (hk ⟨n-512,by omega⟩).trans
      (congrArg known (by change 512+(n-512) = n; omega))

end Blake3Prize.Submission.RomKeyMaterial
