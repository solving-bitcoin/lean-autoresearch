import WotsLamport.Submission.DomainSeparation
import WotsLamport.Submission.LabelBridge

namespace WotsLamport.Submission
open SecretRelease

/-- Parsers for the complete hidden values retained in the actual oracle
inputs. They intentionally accept extra inputs: a trace union bound only
needs to include every programmed address, not characterize honest queries. -/
def chainQueryTarget (input : ByteArray) : Option Label :=
  (Codec.byteVector 32).bytes.decode input

def maskQueryTarget (pk nonce input : ByteArray) : Option Label :=
  if input.size = nonce.size+pk.size+58 then
    (Codec.byteVector 32).bytes.decode (input.extract (input.size-33) (input.size-1))
  else none

def commitmentQueryTarget (pk nonce input : ByteArray) : Option Label :=
  if input.size = nonce.size+pk.size+56 then
    (Codec.byteVector 32).bytes.decode (input.extract (input.size-32) input.size)
  else none

theorem chainQueryTarget_complete (node : Label) :
    chainQueryTarget (ByteArray.mk node.toArray) = some node :=
  byteVector_decode_raw node

theorem maskQueryTarget_complete (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) (block : Nat) :
    maskQueryTarget pk nonce (maskQuery pk nonce wire value point node block) = some node := by
  let header := domain "WOTS-LAMPORT/mask/v1" pk nonce wire value ++ writeLE 2 point
  have hs : (maskQuery pk nonce wire value point node block).size = header.size+33 := by
    simp only [maskQuery, ByteArray.size_append, vectorBytes_size, writeLE_size, header]
    omega
  unfold maskQueryTarget
  rw [if_pos (maskQuery_size pk nonce wire value point node block), hs]
  have hstart : header.size+33-33 = header.size := by omega
  have hend : header.size+33-1 = header.size+32 := by omega
  rw [hstart, hend]
  change (Codec.byteVector 32).bytes.decode
    (((header ++ ByteArray.mk node.toArray) ++ writeLE 1 block).extract
      header.size (header.size+32)) = some node
  rw [extract_label_between]
  exact byteVector_decode_raw node

theorem commitmentQueryTarget_complete (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (label : Label) :
    commitmentQueryTarget pk nonce (commitmentQuery pk nonce wire value label) = some label := by
  let header := domain "WOTS-LAMPORT/label/v1" pk nonce wire value
  have hs : (commitmentQuery pk nonce wire value label).size = header.size+32 := by
    simp only [commitmentQuery, ByteArray.size_append, vectorBytes_size, header]
  unfold commitmentQueryTarget
  rw [if_pos (commitmentQuery_size pk nonce wire value label), hs]
  have hstart : header.size+32-32 = header.size := by omega
  rw [hstart]
  change (Codec.byteVector 32).bytes.decode
    ((header ++ ByteArray.mk label.toArray).extract header.size (header.size+32)) = some label
  rw [ByteArray.extract_append_eq_right rfl (by rw [vectorBytes_size])]
  exact byteVector_decode_raw label

end WotsLamport.Submission
