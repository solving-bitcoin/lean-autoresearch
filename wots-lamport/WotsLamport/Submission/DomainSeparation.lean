import WotsLamport.Submission.ArtifactBridge

namespace WotsLamport.Submission
open SecretRelease

def maskQuery (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) (block : Nat) : ByteArray :=
  domain "WOTS-LAMPORT/mask/v1" pk nonce wire value ++ writeLE 2 point ++
    ByteArray.mk node.toArray ++ writeLE 1 block

def commitmentQuery (pk nonce : ByteArray) (wire : Nat) (value : Bool) (label : Label) : ByteArray :=
  domain "WOTS-LAMPORT/label/v1" pk nonce wire value ++ ByteArray.mk label.toArray

theorem mask_as_queries (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) :
    mask h pk nonce wire value point node =
      ByteArray.mk (h (maskQuery pk nonce wire value point node 0)).toArray ++
      (ByteArray.mk (h (maskQuery pk nonce wire value point node 1)).toArray).extract 0 16 := rfl

theorem commitment_as_query (h : Hash) (pk nonce : ByteArray) (wire : Nat)
    (value : Bool) (label : Label) :
    commitment h pk nonce wire value label = h (commitmentQuery pk nonce wire value label) := rfl

theorem domain_size (tag : String) (pk nonce : ByteArray) (wire : Nat) (value : Bool) :
    (domain tag pk nonce wire value).size = tag.toUTF8.size+nonce.size+pk.size+3 := by
  simp only [domain, ByteArray.size_append, writeLE_size]
  omega

theorem maskQuery_size (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) (block : Nat) :
    (maskQuery pk nonce wire value point node block).size = nonce.size+pk.size+58 := by
  have htag : "WOTS-LAMPORT/mask/v1".toUTF8.size = 20 := by decide +kernel
  simp only [maskQuery, ByteArray.size_append, domain_size, writeLE_size, vectorBytes_size, htag]
  omega

theorem commitmentQuery_size (pk nonce : ByteArray) (wire : Nat) (value : Bool) (label : Label) :
    (commitmentQuery pk nonce wire value label).size = nonce.size+pk.size+56 := by
  have htag : "WOTS-LAMPORT/label/v1".toUTF8.size = 21 := by decide +kernel
  simp only [commitmentQuery, ByteArray.size_append, domain_size, vectorBytes_size, htag]
  omega

theorem maskQuery_ne_chain (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node chainNode : Label) (block : Nat) :
    maskQuery pk nonce wire value point node block ≠ ByteArray.mk chainNode.toArray := by
  intro he
  have hs := congrArg ByteArray.size he
  rw [maskQuery_size, vectorBytes_size] at hs
  omega

theorem commitmentQuery_ne_chain (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (label chainNode : Label) :
    commitmentQuery pk nonce wire value label ≠ ByteArray.mk chainNode.toArray := by
  intro he
  have hs := congrArg ByteArray.size he
  rw [commitmentQuery_size, vectorBytes_size] at hs
  omega

theorem maskQuery_ne_commitmentQuery (pk nonce : ByteArray) (wire wire' : Nat)
    (value value' : Bool) (point : Nat) (node label : Label) (block : Nat) :
    maskQuery pk nonce wire value point node block ≠ commitmentQuery pk nonce wire' value' label := by
  intro he
  have hs := congrArg ByteArray.size he
  rw [maskQuery_size, commitmentQuery_size] at hs
  omega

theorem extract_label_between (prefix suffix : ByteArray) (label : Label) :
    ((prefix ++ ByteArray.mk label.toArray) ++ suffix).extract prefix.size (prefix.size+32) =
      ByteArray.mk label.toArray := by
  rw [extract_append_left_of_le _ _ _ _ (by simp only [ByteArray.size_append, vectorBytes_size])]
  exact ByteArray.extract_append_eq_right rfl (by rw [vectorBytes_size])

/-- A mask query retains the complete 256-bit hidden node. There is no
truncation or non-injective hash-input serialization at this boundary. -/
theorem maskQuery_node_injective (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point block : Nat) : Function.Injective (fun node => maskQuery pk nonce wire value point node block) := by
  intro a b he
  let prefix := domain "WOTS-LAMPORT/mask/v1" pk nonce wire value ++ writeLE 2 point
  have hs := congrArg (fun bytes : ByteArray => bytes.extract prefix.size (prefix.size+32)) he
  change ((prefix ++ ByteArray.mk a.toArray) ++ writeLE 1 block).extract _ _ =
    ((prefix ++ ByteArray.mk b.toArray) ++ writeLE 1 block).extract _ _ at hs
  rw [extract_label_between, extract_label_between] at hs
  apply Vector.toArray_inj.mp
  exact congrArg ByteArray.data hs

end WotsLamport.Submission
