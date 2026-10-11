import WotsLamport.Submission.OraclePrograms
import WotsLamport.Submission.Exposed

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected OracleSpec OracleComp

theorem pure_query_bound {A : Type} (a : A) (n : Nat) :
    IsTotalQueryBound (pure a : Program A) n := by
  exact isQueryBound_pure a n _ _

theorem one_query_bound (input : ByteArray) : IsTotalQueryBound (oracleQuery input : Program Label) 1 := by
  unfold oracleQuery IsTotalQueryBound
  rw [isQueryBound_query_iff]
  decide

theorem listMapM_query_bound {A B : Type} (xs : List A) (f : A → Program B) (q : Nat)
    (bound : ∀ x ∈ xs, IsTotalQueryBound (f x) q) :
    IsTotalQueryBound (xs.mapM f) (xs.length*q) := by
  induction xs with
  | nil => exact pure_query_bound ([] : List B) 0
  | cons x xs ih =>
    have hx := bound x (by simp)
    have ht := ih (fun y hy => bound y (by simp [hy]))
    have h := isTotalQueryBound_bind hx (fun y =>
      isTotalQueryBound_bind ht (fun ys => pure_query_bound (y::ys) 0))
    simpa [List.mapM_cons, List.length_cons, Nat.add_mul, Nat.add_comm] using h

theorem sequenceFin_query_bound {A : Type} (n q : Nat) (f : Fin n → Program A)
    (bound : ∀ i, IsTotalQueryBound (f i) q) :
    IsTotalQueryBound (sequenceFin n f) (n*q) := by
  induction n with
  | zero => exact pure_query_bound (Fin.elim0 : Fin 0 → A) 0
  | succ n ih =>
    have ht := ih (fun i => f i.succ) (fun i => bound i.succ)
    have h := isTotalQueryBound_bind (bound 0) (fun head =>
      isTotalQueryBound_bind ht (fun tail => pure_query_bound (Fin.cases head tail : Fin (n+1) → A) 0))
    simpa [sequenceFin, Nat.add_mul, Nat.add_comm] using h

theorem chainProgram_query_bound (n : Nat) (seed : Label) :
    IsTotalQueryBound (chainProgram n seed) n := by
  induction n with
  | zero => exact pure_query_bound seed 0
  | succ n ih => exact isTotalQueryBound_bind ih (fun node => one_query_bound (ByteArray.mk node.toArray))

theorem maximum_le_fifteen (i : Fin 67) : maximum i ≤ 15 := by
  unfold maximum
  split <;> omega

theorem publicKeyProgram_query_bound (keys : Keys) :
    IsTotalQueryBound (publicKeyProgram keys) (67*15) := by
  apply sequenceFin_query_bound
  intro i
  exact (chainProgram_query_bound (maximum i) (keys i)).mono (maximum_le_fifteen i)

theorem signProgram_query_bound (keys : Keys) (m : Message) :
    IsTotalQueryBound (signProgram keys m) (67*15) := by
  apply sequenceFin_query_bound
  intro i
  exact (chainProgram_query_bound (encodeWord m i) (keys i)).mono
    ((encodeWord_le m i).trans (maximum_le_fifteen i))

theorem maskProgram_query_bound (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) :
    IsTotalQueryBound (maskProgram pk nonce wire value point node) 2 := by
  exact isTotalQueryBound_bind (one_query_bound _) (fun first =>
    isTotalQueryBound_bind (one_query_bound _) (fun second => pure_query_bound
      (ByteArray.mk first.toArray ++ (ByteArray.mk second.toArray).extract 0 16) 0))

theorem slots_chain_depth (i : Fin 256) (value : Bool) (entry : Fin 67 × Nat)
    (member : entry ∈ slots i value) : entry.2 ≤ 14 := by
  unfold slots at member
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp member
  obtain ⟨k, hk, hentry⟩ := List.mem_flatMap.mp hj
  have he := List.eq_of_mem_replicate hentry
  rw [he]
  have hbelow := List.mem_range.mp hk
  have hmax := maximum_le_fifteen j
  omega

theorem labelTableProgram_query_bound (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) :
    IsTotalQueryBound (labelTableProgram coins pk nonce keys i value label) (1984*16) := by
  let polys := (List.range 16).map fun limb => polynomial coins label i.val limb value
  let row : ((Fin 67 × Nat) × Nat) → Program ByteArray := fun ((j,k), index) => do
    let node ← chainProgram k (keys j)
    let pad ← maskProgram pk nonce i.val value (index+1) node
    pure (xorBytes (concatenate (polys.map fun p =>
      writeLE 3 (evaluatePolynomial p (index+1)))) pad)
  have hr : ∀ entry ∈ (slots i value).zipIdx, IsTotalQueryBound (row entry) 16 := by
    intro entry he
    have hk := slots_chain_depth i value entry.1
      (List.fst_mem_of_mem_zipIdx he)
    rcases entry with ⟨⟨j,k⟩,index⟩
    simp only [row, map_eq_bind_pure_comp, Function.comp_def]
    exact isTotalQueryBound_bind ((chainProgram_query_bound k (keys j)).mono hk)
      (fun node => isTotalQueryBound_bind (maskProgram_query_bound pk nonce i.val value (index+1) node)
        (fun pad => pure_query_bound _ 0))
  have hm := listMapM_query_bound (slots i value).zipIdx row 16 hr
  have h := isTotalQueryBound_bind hm (fun rows => pure_query_bound (concatenate rows) 0)
  have hlen : (slots i value).length ≤ 1984 := by rw [slots_length]; cases value <;> decide
  have hb : ((slots i value).zipIdx.length*16)+0 ≤ 1984*16 := by
    simpa using Nat.mul_le_mul_right 16 hlen
  simpa only [labelTableProgram, row, polys, map_eq_bind_pure_comp, Function.comp_def] using h.mono hb

theorem prepareProgram_query_bound (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair) :
    IsTotalQueryBound (prepareProgram coins keys labels)
      (67*15 + 256*2 + 256*(2*1984*16)) := by
  simp only [prepareProgram, map_eq_bind_pure_comp, Function.comp_def, Nat.add_assoc]
  refine isTotalQueryBound_bind (oa := publicKeyProgram keys)
    (n₁ := 67*15) (n₂ := 256*2 + 256*(2*1984*16)) (publicKeyProgram_query_bound keys) ?_
  intro publicKeyValue
  refine isTotalQueryBound_bind (n₁ := 256*2) (n₂ := 256*(2*1984*16)+0) ?_ ?_
  · let f : Fin 256 → Program ByteArray := fun i => do
      let left ← oracleQuery (commitmentQuery (keyCodec.encode publicKeyValue) (coins.extract 0 32)
        i.val false ((labels i).get false))
      let right ← oracleQuery (commitmentQuery (keyCodec.encode publicKeyValue) (coins.extract 0 32)
        i.val true ((labels i).get true))
      pure (ByteArray.mk left.toArray ++ ByteArray.mk right.toArray)
    have h := listMapM_query_bound (List.finRange 256) f 2 (by
      intro i _
      simp only [f, map_eq_bind_pure_comp, Function.comp_def]
      exact isTotalQueryBound_bind (one_query_bound _)
        (fun left => isTotalQueryBound_bind (one_query_bound _)
          (fun right => pure_query_bound (ByteArray.mk left.toArray ++ ByteArray.mk right.toArray) 0)))
    simpa only [List.length_finRange, map_eq_bind_pure_comp, Function.comp_def] using h
  · intro commitments
    refine isTotalQueryBound_bind (n₁ := 256*(2*1984*16)) (n₂ := 0) ?_ ?_
    · let f : Fin 256 → Program ByteArray := fun i => do
        let left ← labelTableProgram coins (keyCodec.encode publicKeyValue) (coins.extract 0 32)
          keys i false ((labels i).get false)
        let right ← labelTableProgram coins (keyCodec.encode publicKeyValue) (coins.extract 0 32)
          keys i true ((labels i).get true)
        pure (left ++ right)
      have h := listMapM_query_bound (List.finRange 256) f (2*1984*16) (by
        intro i _
        simp only [f, map_eq_bind_pure_comp, Function.comp_def]
        exact isTotalQueryBound_bind (labelTableProgram_query_bound _ _ _ keys i false _)
          (fun left => isTotalQueryBound_bind (labelTableProgram_query_bound _ _ _ keys i true _)
            (fun right => pure_query_bound (left ++ right) 0)))
      simpa only [List.length_finRange, map_eq_bind_pure_comp, Function.comp_def] using h
    · intro tables
      exact pure_query_bound _ 0

def honestSetupQueries : Nat := 2*(67*15) + 256*2 + 256*(2*1984*16)
def honestReleaseQueries : Nat := honestSetupQueries + 67*15

theorem wrappedPrepareProgram_query_bound (coins : ByteArray) (keys : Keys) (labels : Fin 256 → Pair) :
    IsTotalQueryBound (wrappedPrepareProgram coins keys labels) honestSetupQueries := by
  have suffix (publicKeyValue : PublicKey) :
      IsTotalQueryBound (do
        let body ← prepareProgram coins keys labels
        pure (keyCodec.encode publicKeyValue ++ body))
        (67*15 + (256*2 + 256*(2*1984*16))) := by
    have h := isTotalQueryBound_bind (prepareProgram_query_bound coins keys labels)
      (fun body => pure_query_bound (keyCodec.encode publicKeyValue ++ body) 0)
    simpa only [Nat.add_zero, Nat.add_assoc] using h
  have h := isTotalQueryBound_bind (publicKeyProgram_query_bound keys) suffix
  simpa only [wrappedPrepareProgram, honestSetupQueries, two_mul, Nat.add_assoc] using h

/-- This counts the reified executable's chain, mask and commitment queries,
including both public-key computations and one signature disclosure. Repeated
queries are counted again, so caching is not needed to justify this ceiling. -/
theorem honest_queries_within_target : honestReleaseQueries ≤ 2^32 := by
  decide +kernel

end WotsLamport.Submission
