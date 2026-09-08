import Blake3Prize.Submission.RomScheme
import Blake3Prize.Submission.RomOracleLaw

namespace Blake3Prize.Submission.RomSampleLaw
open SecretRelease Blake3Prize.Protected RomKeyMaterial MeasureTheory ProbabilityTheory

abbrev InputKeys := Fin 512 → Pair
abbrev OutputKeys := Fin 256 → Pair
abbrev FiniteSample := InputKeys × OutputKeys × Bytes 3915904

noncomputable def finiteEquiv : FiniteSample ≃ KeySet :=
  (Equiv.prodAssoc InputKeys OutputKeys (Bytes 3915904)).symm.trans
    (externalEquiv.prodCongr (coinEquiv 61186))

theorem finiteEquiv_eq (s : FiniteSample) : finiteEquiv s = assemble s.2.2 s.1 s.2.1 := by
  simp only [assemble,sampled_eq]
  rfl

noncomputable def state (sample : ROM.Sample RomScheme.scheme) : KeySet × ROM.Oracle :=
  (assemble sample.2.2.1 sample.1 sample.2.1,sample.2.2.2)

local instance : MeasurableSpace challenge.inputs.Keys := ⊤
local instance : MeasurableSpace challenge.outputs.Keys := ⊤
local instance : MeasurableSpace InputKeys := ⊤
local instance : MeasurableSpace OutputKeys := ⊤

theorem preserving : MeasurePreserving state (ROM.law RomScheme.scheme)
    ((uniformOn (Set.univ : Set KeySet)).prod (RomOracleLaw.law (List (Fin 256)))) := by
  let il : Measure InputKeys := uniformOn Set.univ
  let ol : Measure OutputKeys := uniformOn Set.univ
  let cl : Measure (Bytes 3915904) := uniformOn Set.univ
  let hl := RomOracleLaw.law (List (Fin 256))
  have h₁ := (MeasurePreserving.id il).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc ol cl hl))
  have h₂ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc il (ol.prod cl) hl)
  have hf : MeasurePreserving finiteEquiv (il.prod (ol.prod cl)) (uniformOn (Set.univ : Set KeySet)) := by
    rw [show il.prod (ol.prod cl) = uniformOn Set.univ by
      dsimp only [il,ol,cl]
      rw [RomLamportLaw.prod_uniform_univ,RomLamportLaw.prod_uniform_univ]]
    exact RomFiniteProbability.uniform_equiv finiteEquiv
  have hm := (hf.prod (MeasurePreserving.id hl)).comp (h₂.comp h₁)
  change MeasurePreserving (fun s : InputKeys × OutputKeys × Bytes 3915904 × ROM.Oracle =>
    (assemble s.2.2.1 s.1 s.2.1,s.2.2.2))
    (il.prod (ol.prod (cl.prod hl))) ((uniformOn (Set.univ : Set KeySet)).prod hl)
  convert hm using 1
  funext s
  exact Prod.ext (finiteEquiv_eq (s.1,s.2.1,s.2.2.1)).symm rfl

end Blake3Prize.Submission.RomSampleLaw
