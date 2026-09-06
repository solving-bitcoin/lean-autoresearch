import SecretRelease
import Batteries.Data.Nat.Lemmas
import Batteries.Data.Vector.Lemmas
import Batteries.Data.Fin.Lemmas

/-! Canonical wire codecs. These transport laws do not assume a construction
or a cryptographic primitive; the mathematical contract remains byte-agnostic. -/
namespace SecretRelease

structure ByteCodec (A : Type) where
  encode : A → ByteArray
  decode : ByteArray → Option A
  decode_encode : ∀ a, decode (encode a) = some a
  encode_decode : ∀ b a, decode b = some a → encode a = b

/-- Re-encoding rejects noncanonical alternatives, including nonzero padding. -/
def ByteCodec.checked (encode : A → ByteArray) (parse : ByteArray → Option A)
    (roundtrip : ∀ a, parse (encode a) = some a) : ByteCodec A where
  encode := encode
  decode := fun b => (parse b).bind fun a => if encode a = b then some a else none
  decode_encode := by intro a; simp [roundtrip a]
  encode_decode := by
    intro b a h
    obtain ⟨a', _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases Option.some.inj h; assumption
    · contradiction

/-- Byte-major LSB-first, with zero padding to the next byte. -/
def packBits (bits : Vector Bool n) : ByteArray :=
  ⟨(Vector.ofFn fun i : Fin ((n+7)/8) => UInt8.ofNat (Nat.ofBits fun j : Fin 8 =>
    if h : 8*i.val+j.val < n then bits[8*i.val+j.val] else false)).toArray⟩

def unpackBits (n : Nat) (bytes : ByteArray) : Option (Vector Bool n) :=
  if h : bytes.size = (n+7)/8 then
    some (Vector.ofFn fun i => bytes[i.val/8].toNat.testBit (i.val%8))
  else none

@[simp] theorem unpackBits_packBits (bits : Vector Bool n) :
    unpackBits n (packBits bits) = some bits := by
  unfold unpackBits
  rw [dif_pos (show (packBits bits).size = (n+7)/8 by simp [packBits, ByteArray.size])]
  apply congrArg some
  apply Vector.ext
  intro i hi
  have hm : i%8 < 8 := Nat.mod_lt _ (by decide)
  have he : 8*(i/8)+i%8 = i := by omega
  simp only [Vector.getElem_ofFn, packBits, ByteArray.getElem_eq_getElem_data,
    Vector.toArray_ofFn, Array.getElem_ofFn, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _), Nat.testBit_ofBits_lt _ _ hm]
  simp [he, hi]

/-- The existing fixed bit codec determines all input/private wire bytes. -/
def Codec.bytes (c : Codec A) : ByteCodec A :=
  ByteCodec.checked (fun a => packBits (c.encode a))
    (fun b => (unpackBits c.width b).bind c.decode) (by
      intro a; simp [c.decode_encode])

def Codec.prod (a : Codec A) (b : Codec B) : Codec (A × B) where
  width := a.width + b.width
  encode := fun p => a.encode p.1 ++ b.encode p.2
  decode := fun v => do
    let x ← a.decode (Vector.ofFn fun i : Fin a.width => v[i.val])
    let y ← b.decode (Vector.ofFn fun i : Fin b.width => v[a.width+i.val])
    pure (x,y)
  decode_encode := by
    intro p
    simp [a.decode_encode, b.decode_encode]
  encode_decode := by
    intro v p h
    obtain ⟨x,hx,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y,hy,h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    rw [a.encode_decode _ _ hx, b.encode_decode _ _ hy]
    apply Vector.ext
    intro i hi
    by_cases h : i < a.width <;> simp_all

/-- Fixed-size arrays of arbitrary canonical values, including zero-bit keys. -/
def Codec.pi (n : Nat) (c : Codec A) : Codec (Fin n → A) where
  width := n*c.width
  encode := fun a => Vector.ofFn fun i => (c.encode (a i.divNat)).get i.modNat
  decode := fun v =>
    let decoded := Vector.ofFn fun i : Fin n => c.decode (Vector.ofFn fun j => v.get (Fin.mkDivMod i j))
    if h : ∀ i, (decoded.get i).isSome then some (fun i => (decoded.get i).get (h i)) else none
  decode_encode := by
    intro a
    have get_roundtrip (v : Vector Bool c.width) : Vector.ofFn v.get = v := by
      apply Vector.ext; intro i hi; simp [Vector.get_eq_getElem]
    simp only [Vector.get_ofFn, Fin.divNat_mkDivMod, Fin.modNat_mkDivMod,
      get_roundtrip, c.decode_encode, Option.isSome_some, implies_true, dite_true]
    rfl
  encode_decode := by
    intro v a h
    dsimp only at h
    simp only [Vector.get_ofFn] at h
    split at h
    next hv =>
      cases Option.some.inj h
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      have hd := c.encode_decode _ _ (Option.some_get (hv (⟨i,hi⟩ : Fin (n*c.width)).divNat)).symm
      rw [hd]
      change (Vector.ofFn fun j => v.get ((⟨i,hi⟩ : Fin (n*c.width)).divNat.mkDivMod j)).get
        (⟨i,hi⟩ : Fin (n*c.width)).modNat = v.get ⟨i,hi⟩
      simp only [Vector.get_ofFn, Fin.divNat_mkDivMod_modNat]
    next => contradiction

/-- Restrict a codec to valid values without changing their encodings. -/
def Codec.subtype (c : Codec A) (valid : A → Prop) [DecidablePred valid] :
    Codec {a // valid a} where
  width := c.width
  encode := fun a => c.encode a.val
  decode := fun b => (c.decode b).bind fun a => if h : valid a then some ⟨a,h⟩ else none
  decode_encode := by intro a; simp [c.decode_encode, a.property]
  encode_decode := by
    intro b a h
    obtain ⟨x,hx,h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases Option.some.inj h; exact c.encode_decode _ _ hx
    · contradiction

/-- A byte vector's bit representation. -/
def Codec.byteVector (n : Nat) : Codec (Bytes n) where
  width := n*8
  encode := fun b => Vector.ofFn fun i => b[i.val/8].toNat.testBit (i.val%8)
  decode := fun bits => some (Vector.ofFn fun i => UInt8.ofNat
    (Nat.ofBits fun j : Fin 8 => bits[i.val*8+j.val]))
  decode_encode := by
    intro b
    apply congrArg some
    ext i hi
    simp only [Vector.getElem_ofFn]
    have he : (fun j : Fin 8 => b[(i*8+j.val)/8].toNat.testBit ((i*8+j.val)%8)) =
        (fun j : Fin 8 => b[i].toNat.testBit j.val) := by
      funext j
      simp [Nat.add_div, Nat.add_mod, Nat.mod_eq_of_lt j.isLt, Nat.div_eq_of_lt j.isLt, Nat.not_le_of_lt j.isLt]
    rw [he, Nat.ofBits_testBit, Nat.mod_eq_of_lt (show b[i].toNat < 2^8 from b[i].toFin.isLt)]
    simp
  encode_decode := by
    intro bits a h
    cases Option.some.inj h
    ext i hi
    simp only [Vector.getElem_ofFn, UInt8.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _),
      Nat.testBit_ofBits_lt _ _ (Nat.mod_lt i (by decide))]
    dsimp only
    congr 1
    omega

abbrev labelCodec : Codec Label := Codec.byteVector 32
abbrev pairCodec : Codec Pair :=
  (labelCodec.prod labelCodec).subtype (fun p => p.1 ≠ p.2)

/-- Built-ins keep the pair/label order of their disclosure definitions. -/
def lamportKeys (c : Codec A) : ByteCodec (Lamport c).Keys :=
  ((pairCodec.pi c.width)).bytes

def horsKeys (n : Nat) (select : Hash → A → Fin n → Bool) : ByteCodec (HORS n select).Keys :=
  (labelCodec.pi n).bytes

def onesOnlyKeys (c : Codec A) : ByteCodec (OnesOnly c).Keys :=
  horsKeys c.width _
def preimageKeys (condition : A → Bool) : ByteCodec (Preimage condition).Keys := labelCodec.bytes

def plainKeys (encode : A → ByteArray) : ByteCodec (Plain encode).Keys := Codec.unit.bytes

end SecretRelease
