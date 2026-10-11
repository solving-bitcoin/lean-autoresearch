import WotsLamport.Submission.ArtifactProgramming

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

def indexedAnswerMask (answers : ArtifactAnswers) (i : Fin 256) (value : Bool)
    (index : Nat) : ByteArray :=
  if bound : index < (if value then 1982 else 1984) then
    answerMask answers ⟨(i,value,⟨index,by cases value <;> simp_all <;> omega⟩),bound⟩
  else ByteArray.empty

def idealLabelTable (coins : ByteArray) (answers : ArtifactAnswers)
    (i : Fin 256) (value : Bool) (label : Label) : ByteArray :=
  let polys := (List.range 16).map fun limb => polynomial coins label i.val limb value
  concatenate ((slots i value).zipIdx.map fun (_, index) =>
    xorBytes (concatenate (polys.map fun p => writeLE 3 (evaluatePolynomial p (index+1))))
      (indexedAnswerMask answers i value index))

/-- An explicit prepared artifact from coins and independently supplied
mask/commitment answers. It uses the executable's exact byte layout. -/
def idealPreparedBody (coins : ByteArray) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) : ByteArray :=
  coins.extract 0 32 ++ concatenate ((List.finRange 256).map fun i =>
    ByteArray.mk (answers (Sum.inr (i,false))).toArray ++
    ByteArray.mk (answers (Sum.inr (i,true))).toArray) ++
  concatenate ((List.finRange 256).map fun i =>
    idealLabelTable coins answers i false ((labels i).get false) ++
    idealLabelTable coins answers i true ((labels i).get true))

theorem labelTable_of_programmed_answers (h : Hash) (tape : ChainTape)
    (consistent : TapeConsistent h tape) (coins pk nonce : ByteArray)
    (answers : ArtifactAnswers)
    (masks : ∀ position : SharePosition,
      mask h pk nonce position.val.1.val position.val.2.1 (position.val.2.2.val+1)
        (sharePositionNode tape position) = answerMask answers position)
    (i : Fin 256) (value : Bool) (label : Label) :
    labelTable h coins pk nonce (tapeKeys tape) i value label =
      idealLabelTable coins answers i value label := by
  unfold labelTable idealLabelTable
  apply congrArg concatenate
  apply List.map_congr_left
  intro entry member
  have bound : entry.2 < (if value then 1982 else 1984) := by
    have hb := List.snd_lt_of_mem_zipIdx member
    simpa only [Nat.add_zero, slots_length] using hb
  have bound' : entry.2 < 1984 := by cases value <;> simp_all <;> omega
  let position : SharePosition := ⟨(i,value,⟨entry.2,bound'⟩),bound⟩
  have sameEntry : entry.1 = sharePositionEntry position := by
    simpa only [Nat.sub_zero, sharePositionEntry, position] using List.fst_eq_of_mem_zipIdx member
  have nonpublic := slot_entry_nonpublic i value entry.1
    (List.fst_mem_of_mem_zipIdx member)
  have chainEq : chain h entry.1.2 (tapeKeys tape entry.1.1) =
      sharePositionNode tape position := by
    rw [chain_tape h tape consistent _ _ (Nat.le_of_lt nonpublic)]
    have same : (⟨entry.1, nonpublic⟩ : {e : Fin 67 × Nat // e.2 < maximum e.1}) =
        ⟨sharePositionEntry position, (sharePositionEdge position).property⟩ :=
      Subtype.ext sameEntry
    exact congrArg (fun e : {e : Fin 67 × Nat // e.2 < maximum e.1} =>
      tape ⟨e.val.1, ⟨e.val.2, Nat.lt_succ_of_lt e.property⟩⟩) same
  change xorBytes _ (mask h pk nonce i.val value (entry.2+1)
    (chain h entry.1.2 (tapeKeys tape entry.1.1))) = _
  rw [chainEq, masks position]
  simp only [indexedAnswerMask, dif_pos bound, position]

theorem prepare_of_programmed_answers (h : Hash) (tape : ChainTape)
    (consistent : TapeConsistent h tape) (coins : ByteArray) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers)
    (masks : ∀ position : SharePosition,
      mask h (keyCodec.encode (tapePublicKey tape)) (coins.extract 0 32)
        position.val.1.val position.val.2.1 (position.val.2.2.val+1)
        (sharePositionNode tape position) = answerMask answers position)
    (commitments : ∀ (i : Fin 256) (value : Bool),
      commitment h (keyCodec.encode (tapePublicKey tape)) (coins.extract 0 32)
        i.val value ((labels i).get value) = answers (Sum.inr (i,value))) :
    prepare h coins (tapeKeys tape) labels = idealPreparedBody coins labels answers := by
  simp only [prepare, publicKey_tape h tape consistent, commitments,
    labelTable_of_programmed_answers h tape consistent coins _ _ answers masks,
    idealPreparedBody]

/-- Exact correspondence for a collision-free programmed tape, including all
48,750,624 body bytes. This is a functional equality; its joint random-oracle
law must be supplied separately. -/
theorem prepare_programmedHash (coins : ByteArray) (tape : ChainTape)
    (labels : Fin 256 → Pair) (answers : ArtifactAnswers) (baseline : Hash)
    (distinct : Function.Injective tape) :
    prepare (programmedHash (coins.extract 0 32) tape labels answers baseline)
      coins (tapeKeys tape) labels = idealPreparedBody coins labels answers := by
  apply prepare_of_programmed_answers _ tape
    (programmedHash_consistent _ tape labels answers baseline distinct) coins labels answers
  · intro position
    exact programArtifactOracle_mask _ _ _ _ _ _ position
  · intro i value
    exact programArtifactOracle_commitment _ _ _ _ _ _ i value

end WotsLamport.Submission
