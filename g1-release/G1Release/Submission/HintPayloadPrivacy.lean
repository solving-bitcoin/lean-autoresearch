import G1Release.Submission.HintPayload
namespace G1Release.Submission.HintPayloadPrivacy
open GarblingPrize.Protected HintPayload
def translatePad (oldPayload newPayload pad : WordBytes) : WordBytes :=
  Bytes.xor newPayload (Bytes.xor oldPayload pad)

@[simp] theorem translatePad_source_target_source
    (oldPayload newPayload pad : WordBytes) :
    translatePad newPayload oldPayload
        (translatePad oldPayload newPayload pad) = pad := by
  unfold translatePad
  rw [Bytes.xor_cancel_left, Bytes.xor_cancel_left]

theorem payload_xor_translatePad
    (oldPayload newPayload pad : WordBytes) :
    Bytes.xor newPayload (translatePad oldPayload newPayload pad) =
      Bytes.xor oldPayload pad := by
  exact Bytes.xor_cancel_left newPayload (Bytes.xor oldPayload pad)


end G1Release.Submission.HintPayloadPrivacy
