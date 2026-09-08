import G1Release.Submission.FixedCodec

/-! Concrete, cached 32-byte words and an exact fixed-width serializer.
Field canonicality is checked by the evaluator; arbitrary ciphertext words
remain valid serialized artifacts. No instance-dependent data is omitted. -/
namespace G1Release.Submission.DutyFreeWords
open GarblingPrize.Protected

abbrev Word := Bytes 32
abbrev Block (n : Nat) := Vector Word n

def wordCodec : FixedCodec Word 32 where
  encode := id
  decode := .ok
  decode_encode := fun _ => rfl
  encode_decode := by intro bytes value h; exact (Except.ok.inj h).symm

/-- Traverse the stored array length. Keeping that length opaque until the
array is available avoids unfolding tens of thousands of static fold steps
when the scheme's encoder projection is checked by the kernel. -/
def encode (words : Block n) : ByteArray :=
  FixedCodec.encodeFin wordCodec words.toArray.size (fun i => words.toArray[i.val])

theorem encode_eq (words : Block n) :
    encode words = FixedCodec.encodeFin wordCodec n words.get := by
  cases words with
  | mk array h =>
    cases h
    rfl

def decode (n : Nat) (bytes : ByteArray) : Except WireDecodeError (Block n) := do
  let words ← FixedCodec.decodeFin wordCodec n bytes
  pure (Vector.ofFn words)

theorem encode_size (words : Block n) : (encode words).size = n*32 := by
  rw [encode_eq]
  exact FixedCodec.encodeFin_size wordCodec _

@[simp] theorem ofFn_get (words : Block n) : Vector.ofFn words.get = words := by
  ext i hi
  simp only [Vector.getElem_ofFn, Vector.get_eq_getElem]

@[simp] theorem decode_encode (words : Block n) : decode n (encode words) = .ok words := by
  unfold decode
  rw [encode_eq]
  rw [FixedCodec.decodeFin_encode]
  simp only [Except.bind, bind, Except.pure, pure, ofFn_get]

theorem encode_decode {bytes : ByteArray} {words : Block n}
    (h : decode n bytes = .ok words) : encode words = bytes := by
  unfold decode at h
  cases hw : FixedCodec.decodeFin wordCodec n bytes with
  | error error => simp [hw, Except.bind, bind] at h
  | ok decoded =>
    have he : Vector.ofFn decoded = words := by
      simpa only [hw, Except.bind, bind, Except.pure, pure, Except.ok.injEq] using h
    rw [← he]
    rw [encode_eq]
    have hg : (Vector.ofFn decoded).get = decoded := by funext i; simp
    rw [hg]
    exact FixedCodec.encodeFin_decode wordCodec hw

end G1Release.Submission.DutyFreeWords
