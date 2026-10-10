import WotsLamport.Submission.Sharing

/-! Structural size obligations for the actual serializers. These lemmas do
not yet prove the length of the complete nested Prepare accumulation. -/
namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

@[simp] theorem writeLE_size (length n : Nat) : (writeLE length n).size = length := by
  simp [writeLE, ByteArray.size]

@[simp] theorem xorBytes_size (a b : ByteArray) : (xorBytes a b).size = a.size := by
  simp [xorBytes, ByteArray.size]

theorem mask_size (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) : (mask h pk nonce wire value point node).size = 48 := by
  simp [mask, ByteArray.size_append, ByteArray.size_extract, ByteArray.size]

theorem polynomial_length (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : (polynomial coins label wire limb value).length = threshold value := by
  simp [polynomial]

/-- Finite geometry only: this kernel reduction has no cryptographic inputs.
Unlike native_decide it does not add an executable-code axiom to the proof. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem slots_length (i : Fin 256) (value : Bool) :
    (slots i value).length = if value then 1982 else 1984 := by
  revert i value
  decide

theorem serialized_layout_arithmetic :
    2144 + 32 + 512*32 + 256*(1984+1982)*48 = artifactBytes := by rfl

end WotsLamport.Submission
