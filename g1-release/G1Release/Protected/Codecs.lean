import SecretRelease.Encoding
import G1Release.Math.G1
import Batteries.Data.Nat.Lemmas

set_option maxHeartbeats 800000

namespace G1Release.Protected
open SecretRelease
open G1Release.Math
open G1Release.Math (CanonicalFq CanonicalScalar baseFieldModulus scalarFieldModulus)

abbrev Input := {xy : CanonicalFq × CanonicalFq // BN254.OnCurve xy.1 xy.2}
abbrev Output := BN254.CanonicalOutput
abbrev Private := Output × CanonicalScalar

private theorem fq_fits (x : CanonicalFq) : x.val < 2^256 :=
  lt_trans x.isLt (by decide)
private theorem scalar_fits (r : CanonicalScalar) : r.val < 2^256 :=
  lt_trans r.isLt (by decide)

def readNat (bits : Vector Bool n) (offset width : Nat) (h : offset + width ≤ n) : Nat :=
  Nat.ofBits fun i : Fin width => bits[offset + i.val]

private theorem readNat_eq (bits : Vector Bool n) (offset width x : Nat)
    (h : offset + width ≤ n) (hx : x < 2^width)
    (hb : ∀ i : Fin width, bits[offset + i.val] = x.testBit i.val) :
    readNat bits offset width h = x := by
  unfold readNat
  rw [show (fun i : Fin width => bits[offset + i.val]) = (fun i => x.testBit i.val) from funext hb]
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hx]

instance (x y : CanonicalFq) : Decidable (BN254.OnCurve x y) := by
  unfold BN254.OnCurve
  infer_instance

def encodeInput (a : Input) : Vector Bool 512 := Vector.ofFn fun i =>
  if i.val < 256 then a.val.1.val.testBit i.val else a.val.2.val.testBit (i.val - 256)

def affine? (x y : Nat) : Option Input :=
  if hx : x < baseFieldModulus then
    if hy : y < baseFieldModulus then
      if hc : BN254.OnCurve ⟨x, hx⟩ ⟨y, hy⟩ then some ⟨(⟨x, hx⟩, ⟨y, hy⟩), hc⟩ else none
    else none
  else none

def parseInput (b : Vector Bool 512) : Option Input :=
  affine? (readNat b 0 256 (by decide)) (readNat b 256 256 (by decide))

private theorem parseInput_encode (a : Input) : parseInput (encodeInput a) = some a := by
  have hx : readNat (encodeInput a) 0 256 (by decide) = a.val.1.val := by
    apply readNat_eq _ _ _ _ _ (fq_fits a.val.1)
    intro i; simp [encodeInput, i.isLt]
  have hy : readNat (encodeInput a) 256 256 (by decide) = a.val.2.val := by
    apply readNat_eq _ _ _ _ _ (fq_fits a.val.2)
    intro i; simp [encodeInput]
  simp [parseInput, hx, hy, affine?, a.val.1.isLt, a.val.2.isLt, a.property]

abbrev inputCodec : Codec Input := Codec.ofParser 512 encodeInput parseInput parseInput_encode

def encodeOutputBits : Output → Vector Bool 520
  | .infinity => Vector.replicate 520 false
  | .affine x y _ => Vector.ofFn fun i =>
    if i.val < 8 then (1 : Nat).testBit i.val
    else if i.val < 264 then x.val.testBit (i.val - 8)
    else y.val.testBit (i.val - 264)

def parseOutput (b : Vector Bool 520) : Option Output :=
  let tag := readNat b 0 8 (by decide)
  if tag = 0 then some .infinity else if tag = 1 then
    (affine? (readNat b 8 256 (by decide)) (readNat b 264 256 (by decide))).map fun a =>
      .affine a.val.1 a.val.2 a.property
  else none

private theorem parseOutput_encode (a : Output) : parseOutput (encodeOutputBits a) = some a := by
  cases a with
  | infinity =>
    have ht : readNat (encodeOutputBits .infinity) 0 8 (by decide) = 0 := by
      apply readNat_eq _ _ _ _ _ (by decide)
      intro i; simp [encodeOutputBits]
    simp [parseOutput, ht]
  | affine x y h =>
    have ht : readNat (encodeOutputBits (.affine x y h)) 0 8 (by decide) = 1 := by
      apply readNat_eq _ _ _ _ _ (by decide)
      intro i; simp [encodeOutputBits, i.isLt]
    have hx : readNat (encodeOutputBits (.affine x y h)) 8 256 (by decide) = x.val := by
      apply readNat_eq _ _ _ _ _ (fq_fits x)
      intro i
      have hi : 8 + i.val < 264 := by omega
      simp [encodeOutputBits, hi]
    have hy : readNat (encodeOutputBits (.affine x y h)) 264 256 (by decide) = y.val := by
      apply readNat_eq _ _ _ _ _ (fq_fits y)
      intro i
      have hi : ¬264 + i.val < 8 := by omega
      simp [encodeOutputBits, hi]
    simp [parseOutput, ht, hx, hy, affine?, x.isLt, y.isLt, h]

abbrev outputCodec : Codec Output := Codec.ofParser 520 encodeOutputBits parseOutput parseOutput_encode

def encodePrivate (p : Private) : Vector Bool 776 := Vector.ofFn fun i =>
  if h : i.val < 520 then (encodeOutputBits p.1)[i.val]
  else p.2.val.testBit (i.val - 520)

def parsePrivate (b : Vector Bool 776) : Option Private := do
  let q ← outputCodec.decode (Vector.ofFn fun i : Fin 520 => b[i.val])
  let r := readNat b 520 256 (by decide)
  if hr : r < scalarFieldModulus then some (q, ⟨r, hr⟩) else none

private theorem parsePrivate_encode (p : Private) : parsePrivate (encodePrivate p) = some p := by
  have hq : (Vector.ofFn fun i : Fin 520 => (encodePrivate p)[i.val]) = encodeOutputBits p.1 := by
    ext i hi; simp [encodePrivate]
  have hr : readNat (encodePrivate p) 520 256 (by decide) = p.2.val := by
    apply readNat_eq _ _ _ _ _ (scalar_fits p.2)
    intro i; simp [encodePrivate]
  unfold parsePrivate
  rw [hq, show encodeOutputBits p.1 = outputCodec.encode p.1 from rfl,
      outputCodec.decode_encode]
  simp [hr, p.2.isLt]

abbrev privateCodec : Codec Private := Codec.ofParser 776 encodePrivate parsePrivate parsePrivate_encode

def encodeOutput (out : Output) : ByteArray := packBits (outputCodec.encode out)

end G1Release.Protected
