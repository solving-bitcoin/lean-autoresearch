import WotsLamport.Submission.JointSampler

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤

def fieldBlock (bytes : Bytes 32) : Fin 65537 :=
  ⟨readLE (ByteArray.mk bytes.toArray) 0 32 % 65537, Nat.mod_lt _ (by decide)⟩

theorem fieldBlock_as_integer (bytes : Bytes 32) :
    fieldBlock bytes = Sampler.reduceInteger (coinBlockEquiv bytes) := by
  apply Fin.ext
  change readLE (ByteArray.mk bytes.toArray) 0 32 % 65537 = (coinBlockEquiv bytes).val % 65537
  rw [coinBlockEquiv_value]

theorem fieldBlock_law :
    (uniformOn (Set.univ : Set (Bytes 32))).map fieldBlock = Sampler.fieldLaw := by
  have hf : fieldBlock = Sampler.reduceInteger ∘ coinBlockEquiv := by
    funext bytes
    exact fieldBlock_as_integer bytes
  rw [hf, ← Measure.map_map measurable_of_discrete measurable_of_discrete,
    uniform_map_equiv coinBlockEquiv]
  rfl

def tableFields (n : Nat) (coins : Bytes (n*32)) : Fin n → Fin 65537 :=
  fun i => fieldBlock (byteBlocksEquiv n coins i)

/-- Exact joint pushforward law for concrete disjoint byte blocks, with the
implementation's modular decoder on every block. -/
theorem tableFields_law (n : Nat) :
    (uniformOn (Set.univ : Set (Bytes (n*32)))).map (tableFields n) =
      Measure.pi (fun _ : Fin n => Sampler.fieldLaw) := by
  letI : IsProbabilityMeasure ((uniformOn (Set.univ : Set (Bytes 32))).map fieldBlock) := by
    rw [fieldBlock_law]
    infer_instance
  have hf : tableFields n = (fun blocks : Fin n → Bytes 32 => fun i => fieldBlock (blocks i)) ∘
      byteBlocksEquiv n := rfl
  rw [hf, ← Measure.map_map measurable_of_discrete measurable_of_discrete,
    uniform_map_equiv (byteBlocksEquiv n), uniform_blocks_product,
    Measure.pi_map_pi (fun _ => measurable_of_discrete.aemeasurable)]
  simp only [fieldBlock_law]

theorem tableFields_event_bounds (n : Nat) (event : Set (Fin n → Fin 65537)) :
    uniformOn (Set.univ : Set (Bytes (n*32))) ((tableFields n) ⁻¹' event) ≤
        (Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set (Fin 65537)))) event +
          (n : ENNReal)*Sampler.exceptionWeight ∧
    (Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set (Fin 65537)))) event ≤
        uniformOn (Set.univ : Set (Bytes (n*32))) ((tableFields n) ⁻¹' event) +
          (n : ENNReal)*Sampler.exceptionWeight := by
  have hlaw : uniformOn (Set.univ : Set (Bytes (n*32))) ((tableFields n) ⁻¹' event) =
      (Measure.pi (fun _ : Fin n => Sampler.fieldLaw)) event := by
    rw [← tableFields_law, Measure.map_apply measurable_of_discrete MeasurableSet.of_discrete]
  rw [hlaw]
  exact Sampler.joint_field_event_bounds n event

end WotsLamport.Submission
