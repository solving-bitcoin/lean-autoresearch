import Blake3Prize.Protected.Expression
import Blake3Prize.Protected.WordProgram

namespace Blake3Prize.Protected

/-- Evaluation preserves the three word operations in Clean's BLAKE3 spec. -/
structure WordHom (a : WordProgram.Ops α) (b : WordProgram.Ops β) where
  apply : α → β
  add : ∀ x y, apply (a.add x y) = b.add (apply x) (apply y)
  xor : ∀ x y, apply (a.xor x y) = b.xor (apply x) (apply y)
  rotate : ∀ x n, apply (a.rotate x n) = b.rotate (apply x) n

namespace WordHom
variable {a : WordProgram.Ops α} {b : WordProgram.Ops β} (f : WordHom a b)

theorem mix (v : Vector α 16) (i j k l : Fin 16) (x y : α) :
    (WordProgram.mix a v i j k l x y).map f.apply =
      WordProgram.mix b (v.map f.apply) i j k l (f.apply x) (f.apply y) := by
  simp only [WordProgram.mix, Vector.map_set, Fin.getElem_fin, Vector.getElem_map,
    f.add, f.xor, f.rotate]

theorem round (v m : Vector α 16) :
    (WordProgram.round a v m).map f.apply =
      WordProgram.round b (v.map f.apply) (m.map f.apply) := by
  unfold WordProgram.round Vector.foldl
  symm
  apply Array.foldl_hom (Vector.map f.apply)
  intro state indices
  rcases indices with ⟨i,j,k,l,x,y⟩
  simpa only [Fin.getElem_fin, Vector.getElem_map] using (f.mix state i j k l m[x] m[y]).symm

theorem permute (m : Vector α 16) :
    (WordProgram.permute m).map f.apply = WordProgram.permute (m.map f.apply) := by
  ext i hi
  simp [WordProgram.permute]

theorem rounds (v m : Vector α 16) :
    (WordProgram.rounds a v m).map f.apply =
      WordProgram.rounds b (v.map f.apply) (m.map f.apply) := by
  simp only [WordProgram.rounds, round, permute]

theorem finish (v : Vector α 16) :
    (WordProgram.finish a v).map f.apply = WordProgram.finish b (v.map f.apply) := by
  ext i hi
  simp [WordProgram.finish, f.xor]

theorem digest (v m : Vector α 16) :
    (WordProgram.digest a v m).map f.apply =
      WordProgram.digest b (v.map f.apply) (m.map f.apply) := by
  simp only [WordProgram.digest, finish, rounds]

end WordHom

def evalHom (input : Input) : WordHom WordProgram.symbolicOps WordProgram.natOps where
  apply := WordExpr.eval input
  add := WordExpr.eval_add input
  xor := WordExpr.eval_xor input
  rotate := WordExpr.eval_rotate input

def initialExpressions : Vector WordExpr 16 := WordProgram.initialWords.map WordExpr.literal

theorem initialExpressions_eval (input : Input) :
    initialExpressions.map (WordExpr.eval input) = WordProgram.initialWords := by
  apply Vector.ext
  intro i hi
  have h : WordProgram.initialWords[i] < 2^32 := by
    interval_cases i <;> norm_num [WordProgram.initialWords, chainingValue, Specs.BLAKE3.iv]
    all_goals exact UInt32.toNat_lt _
  simpa only [initialExpressions, Vector.getElem_map, WordExpr.eval_literal]
    using Nat.mod_eq_of_lt h

def referenceWordExpressions : Vector WordExpr 8 :=
  WordProgram.digest WordProgram.symbolicOps initialExpressions WordExpr.inputs

theorem referenceWordExpressions_correct (input : Input) :
    referenceWordExpressions.map (WordExpr.eval input) = referenceWords (inputWords input) := by
  have h := (evalHom input).digest initialExpressions WordExpr.inputs
  change referenceWordExpressions.map (WordExpr.eval input) =
    WordProgram.digest WordProgram.natOps
      (initialExpressions.map (WordExpr.eval input))
      (WordExpr.inputs.map (WordExpr.eval input)) at h
  rw [initialExpressions_eval] at h
  have hi : WordExpr.inputs.map (WordExpr.eval input) = inputWords input := by
    ext i hi
    simp [WordExpr.inputs]
  rw [hi, WordProgram.digest_nat] at h
  exact h

def referenceExpressions : Vector BitExpr 256 :=
  Vector.ofFn fun i => BitExpr.wordBit referenceWordExpressions[i.val / 32]
    ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩

theorem referenceExpressions_correct (input : Input) :
    referenceExpressions.map (BitExpr.eval input) = reference input := by
  have h := referenceWordExpressions_correct input
  apply Vector.ext
  intro i hi
  have hv := congrArg (fun v : Vector Nat 8 => v[i / 32]'(by omega)) h
  simp only [Vector.getElem_map] at hv
  simp [referenceExpressions, reference, outputBits, hv]

end Blake3Prize.Protected
