import G1Release.Submission.DutyFreeWords
import G1Release.Submission.DutyFreeChunkParameters

/-! The complete artifact is 8,192 bridge words followed by 728 affine
tables of 65 words. Every stored word participates in the fixed serializer. -/
namespace G1Release.Submission.DutyFreeArtifact
open GarblingPrize.Protected
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev Label := SecretRelease.Label
abbrev BridgeIndex := Fin 128
abbrev TableIndex := Fin 728
abbrev Artifact := DutyFreeWords.Block 55512

def ofParts (bridges : BridgeIndex → DutyFreeWords.Block 64)
    (tables : TableIndex → DutyFreeWords.Block 65) : Artifact :=
  Vector.ofFn fun i =>
    if h : i.val < 8192 then
      (bridges ⟨i.val/64, by omega⟩).get ⟨i.val%64, Nat.mod_lt _ (by decide)⟩
    else
      (tables ⟨(i.val-8192)/65, by have := i.isLt; omega⟩).get
        ⟨(i.val-8192)%65, Nat.mod_lt _ (by decide)⟩

def bridge (artifact : Artifact) (i : BridgeIndex) : DutyFreeWords.Block 64 :=
  Vector.ofFn fun j => artifact.get ⟨i.val*64+j.val, by have := i.isLt; have := j.isLt; omega⟩

def table (artifact : Artifact) (i : TableIndex) : DutyFreeWords.Block 65 :=
  Vector.ofFn fun j => artifact.get ⟨8192+i.val*65+j.val,
    by have := i.isLt; have := j.isLt; omega⟩

theorem bridge_ofParts (bridges : BridgeIndex → DutyFreeWords.Block 64)
    (tables : TableIndex → DutyFreeWords.Block 65) (i : BridgeIndex) :
    bridge (ofParts bridges tables) i = bridges i := by
  ext j hj
  have hlt : i.val*64+j < 8192 := by have := i.isLt; omega
  have hd : (i.val*64+j)/64 = i.val := by omega
  have hm : (i.val*64+j)%64 = j := by omega
  simp only [bridge, ofParts, Vector.getElem_ofFn, Vector.get_ofFn, dif_pos hlt]
  simp only [hd, hm, Vector.get_eq_getElem]

theorem table_ofParts (bridges : BridgeIndex → DutyFreeWords.Block 64)
    (tables : TableIndex → DutyFreeWords.Block 65) (i : TableIndex) :
    table (ofParts bridges tables) i = tables i := by
  ext j hj
  have hn : ¬8192+i.val*65+j < 8192 := by omega
  have hd : (8192+i.val*65+j-8192)/65 = i.val := by omega
  have hm : (8192+i.val*65+j-8192)%65 = j := by omega
  simp only [table, ofParts, Vector.getElem_ofFn, Vector.get_ofFn, dif_neg hn]
  simp only [hd, hm, Vector.get_eq_getElem]

def encode : Artifact → ByteArray := DutyFreeWords.encode
def decode (bytes : ByteArray) : Option Artifact := (DutyFreeWords.decode 55512 bytes).toOption

@[simp] theorem encode_size (artifact : Artifact) : (encode artifact).size = 1776384 :=
  DutyFreeWords.encode_size artifact

@[simp] theorem decode_encode (artifact : Artifact) : decode (encode artifact) = some artifact := by
  unfold decode encode
  rw [DutyFreeWords.decode_encode]
  rfl

theorem encode_decode {bytes : ByteArray} {artifact : Artifact}
    (h : decode bytes = some artifact) : encode artifact = bytes := by
  unfold decode at h
  cases hd : DutyFreeWords.decode 55512 bytes with
  | error error =>
    rw [hd] at h
    change none = some artifact at h
    cases h
  | ok result =>
    rw [hd] at h
    have he : result = artifact := Option.some.inj h
    subst result
    exact DutyFreeWords.encode_decode hd

end G1Release.Submission.DutyFreeArtifact
