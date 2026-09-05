import Blake3Prize.Protected.Expression

namespace Blake3Prize.Protected
open Challenge.Instances.Blake3CompressGF2Canonical.Interface

/-- Naturality of zk.golf's generic bit semantics. This proves a symbolic
circuit correct compositionally, without expanding the seven-round tree. -/
structure BitHom (α β : Type) [Zero α] [One α] [Add α] [Mul α]
    [Zero β] [One β] [Add β] [Mul β] where
  apply : α → β
  zero : apply 0 = 0
  one : apply 1 = 1
  add : ∀ a b, apply (a + b) = apply a + apply b
  mul : ∀ a b, apply (a * b) = apply a * apply b

namespace BitHom
variable {α β : Type} [Zero α] [One α] [Add α] [Mul α]
  [Zero β] [One β] [Add β] [Mul β] (f : BitHom α β)

@[simp] theorem atWord (x : Blake3Bits.Word α) (i : Nat) :
    Blake3Bits.atWord (x.map f.apply) i = f.apply (Blake3Bits.atWord x i) := by
  simp [Blake3Bits.atWord]

theorem carry (x y : Blake3Bits.Word α) (i : Nat) :
    f.apply (Blake3Bits.carry x y i) = Blake3Bits.carry (x.map f.apply) (y.map f.apply) i := by
  induction i with
  | zero => exact f.zero
  | succ i ih => simp only [Blake3Bits.carry, f.add, f.mul, ih, atWord]

theorem addWord (x y : Blake3Bits.Word α) :
    (Blake3Bits.addWord x y).map f.apply = Blake3Bits.addWord (x.map f.apply) (y.map f.apply) := by
  ext i hi
  simp [Blake3Bits.addWord, f.add, carry]

theorem xorWord (x y : Blake3Bits.Word α) :
    (Blake3Bits.xorWord x y).map f.apply = Blake3Bits.xorWord (x.map f.apply) (y.map f.apply) := by
  ext i hi
  simp [Blake3Bits.xorWord, f.add]

theorem rotRight (x : Blake3Bits.Word α) (n : Nat) :
    (Blake3Bits.rotRight x n).map f.apply = Blake3Bits.rotRight (x.map f.apply) n := by
  ext i hi
  simp [Blake3Bits.rotRight]

theorem stateWord (v : Blake3Bits.State α) (i : Fin 16) :
    (Blake3Bits.stateWord v i).map f.apply = Blake3Bits.stateWord (v.map f.apply) i := by
  ext j hj
  simp [Blake3Bits.stateWord]

theorem setWord (v : Blake3Bits.State α) (i : Fin 16) (x : Blake3Bits.Word α) :
    (Blake3Bits.setWord v i x).map f.apply = Blake3Bits.setWord (v.map f.apply) i (x.map f.apply) := by
  apply Vector.ext
  intro j hj
  by_cases h : j / 32 = i.val <;> simp [Blake3Bits.setWord, h]

def quad (q : Blake3Bits.Quad α) : Blake3Bits.Quad β :=
  ⟨q.a.map f.apply, q.b.map f.apply, q.c.map f.apply, q.d.map f.apply⟩

theorem gFirstValues (q : Blake3Bits.Quad α) (mx : Blake3Bits.Word α) :
    f.quad (Blake3Bits.gFirstValues q mx) =
      Blake3Bits.gFirstValues (f.quad q) (mx.map f.apply) := by
  simp only [Blake3Bits.gFirstValues, quad, addWord, xorWord, rotRight]

theorem gSecondValues (q : Blake3Bits.Quad α) (my : Blake3Bits.Word α) :
    f.quad (Blake3Bits.gSecondValues q my) =
      Blake3Bits.gSecondValues (f.quad q) (my.map f.apply) := by
  simp only [Blake3Bits.gSecondValues, quad, addWord, xorWord, rotRight]

theorem gValues (q : Blake3Bits.Quad α) (mx my : Blake3Bits.Word α) :
    f.quad (Blake3Bits.gValues q mx my) =
      Blake3Bits.gValues (f.quad q) (mx.map f.apply) (my.map f.apply) := by
  simp only [Blake3Bits.gValues, gSecondValues, gFirstValues]

theorem readQuad (v : Blake3Bits.State α) (a b c d : Fin 16) :
    f.quad (Blake3Bits.readQuad v a b c d) =
      Blake3Bits.readQuad (v.map f.apply) a b c d := by
  simp only [quad, Blake3Bits.readQuad, stateWord]

theorem g (v : Blake3Bits.State α) (a b c d : Fin 16) (mx my : Blake3Bits.Word α) :
    (Blake3Bits.g v a b c d mx my).map f.apply =
      Blake3Bits.g (v.map f.apply) a b c d (mx.map f.apply) (my.map f.apply) := by
  have h := f.gValues (Blake3Bits.readQuad v a b c d) mx my
  rw [readQuad] at h
  unfold Blake3Bits.g Blake3Bits.writeQuad
  simp only [setWord]
  have ha := congrArg Blake3Bits.Quad.a h
  have hb := congrArg Blake3Bits.Quad.b h
  have hc := congrArg Blake3Bits.Quad.c h
  have hd := congrArg Blake3Bits.Quad.d h
  simp only [quad] at ha hb hc hd
  rw [ha, hb, hc, hd]

theorem roundState (v m : Blake3Bits.State α) :
    (Blake3Bits.roundState v m).map f.apply = Blake3Bits.roundState (v.map f.apply) (m.map f.apply) := by
  simp only [Blake3Bits.roundState, Blake3Bits.gPairState, g, stateWord]

theorem permuteState (m : Blake3Bits.State α) :
    (Blake3Bits.permuteState m).map f.apply = Blake3Bits.permuteState (m.map f.apply) := by
  ext i hi
  simp [Blake3Bits.permuteState, Blake3Bits.flattenWords, Blake3Bits.permute, Blake3Bits.splitWords]

theorem constWord (n : Nat) :
    (Blake3Bits.constWord n : Blake3Bits.Word α).map f.apply = Blake3Bits.constWord n := by
  apply Vector.ext
  intro i hi
  cases h : n.testBit i <;> simp [Blake3Bits.constWord, h, f.zero, f.one]

@[simp] theorem constAt (n i : Nat) :
    f.apply (Blake3Bits.atWord (Blake3Bits.constWord n) i) =
      Blake3Bits.atWord (Blake3Bits.constWord n) i := by
  rw [← atWord, constWord]

theorem initialState (w : Vector (Blake3Bits.Word α) 28) :
    (Blake3Bits.initialState w).map f.apply = Blake3Bits.initialState (w.map (Vector.map f.apply)) := by
  apply Vector.ext
  intro i hi
  by_cases hcv : i / 32 < 8
  · simp [Blake3Bits.initialState, hcv]
  · by_cases hiv : i / 32 < 12
    · simp [Blake3Bits.initialState, hcv, hiv]
    · simp [Blake3Bits.initialState, hcv, hiv]

theorem initialBlock (w : Vector (Blake3Bits.Word α) 28) :
    (Blake3Bits.initialBlock w).map f.apply = Blake3Bits.initialBlock (w.map (Vector.map f.apply)) := by
  ext i hi
  simp [Blake3Bits.initialBlock]

def config (x : Blake3Bits.Config α) : Blake3Bits.Config β := ⟨x.state.map f.apply, x.block.map f.apply⟩

theorem stepConfig (x : Blake3Bits.Config α) :
    f.config (Blake3Bits.stepConfig x) = Blake3Bits.stepConfig (f.config x) := by
  simp only [config, Blake3Bits.stepConfig, roundState, permuteState]

theorem steps7 (x : Blake3Bits.Config α) : f.config (Blake3Bits.steps7 x) = Blake3Bits.steps7 (f.config x) := by
  simp only [Blake3Bits.steps7, Blake3Bits.steps2, Blake3Bits.steps4, stepConfig]

theorem finalizeState (v initial : Blake3Bits.State α) :
    (Blake3Bits.finalizeState v initial).map f.apply =
      Blake3Bits.finalizeState (v.map f.apply) (initial.map f.apply) := by
  apply Vector.ext
  intro i hi
  by_cases h : i < 256 <;> simp [Blake3Bits.finalizeState, h, f.add]

theorem compressState (w : Vector (Blake3Bits.Word α) 28) :
    (Blake3Bits.compressState w).map f.apply = Blake3Bits.compressState (w.map (Vector.map f.apply)) := by
  have h := congrArg Blake3Bits.Config.state (f.steps7 ⟨Blake3Bits.initialState w, Blake3Bits.initialBlock w⟩)
  simp only [config, initialState, initialBlock] at h
  simp only [Blake3Bits.compressState, finalizeState, initialState, h]

theorem hashWords (input : Vector α 512) :
    (Protected.hashWords input).map (Vector.map f.apply) =
      Protected.hashWords (input.map f.apply) := by
  apply Vector.ext
  intro i hi
  by_cases hcv : i < 8
  · simpa [Protected.hashWords, hcv] using f.constWord (Specs.Blake3.iv[i])
  · by_cases hm : i < 24
    · apply Vector.ext
      intro j hj
      simp [Protected.hashWords, hcv, hm, Blake3Bits.splitWords]
    · simpa [Protected.hashWords, hcv, hm] using
        f.constWord (if i = 26 then 64 else if i = 27 then 11 else 0)

end BitHom

def evalHom (input : Input) : BitHom BitExpr Bit where
  apply := BitExpr.eval input
  zero := BitExpr.eval_zero input
  one := BitExpr.eval_one input
  add := BitExpr.eval_add input
  mul := BitExpr.eval_mul input

/-- Symbolic specialization of the upstream specification. -/
def referenceExpressions : Vector BitExpr 256 :=
  let all := Blake3Bits.compressState (hashWords BitExpr.inputs)
  Vector.ofFn fun i => all[i.val]'(by omega)

theorem referenceExpressions_correct (input : Input) :
    referenceExpressions.map (BitExpr.eval input) = reference input := by
  have h := (evalHom input).compressState (hashWords BitExpr.inputs)
  rw [(evalHom input).hashWords] at h
  have hi : BitExpr.inputs.map (BitExpr.eval input) = input := by
    ext i hi
    simp [BitExpr.inputs]
  change (Blake3Bits.compressState (hashWords BitExpr.inputs)).map (BitExpr.eval input) =
    Blake3Bits.compressState (hashWords (BitExpr.inputs.map (BitExpr.eval input))) at h
  rw [hi] at h
  ext i hi
  have hv := congrArg (fun v => v[i]'(by omega)) h
  simpa [referenceExpressions, reference] using hv

end Blake3Prize.Protected
