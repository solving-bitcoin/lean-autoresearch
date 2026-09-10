import G1Release.Submission.HintAffineTable
import G1Release.Submission.FastPacking

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace G1Release.Submission.FastHintRow
open G1Release.Math HintAffineTable
open scoped BigOperators

/-- The last byte contains six ciphertext bits and the public hint. -/
def packHint (bytes : WordBytes) (hint : Bool) : WordBytes :=
  Vector.ofFn fun i =>
    if i.val = 31 then (bytes.get i &&& 63) ||| (if hint then 64 else 0)
    else bytes.get i

theorem packHint_eq (bytes : WordBytes) (hint : Bool) :
    packHint bytes hint = pack (fun i => HintPayload.lowBit bytes i) hint := by
  apply Vector.ext
  intro i hi
  rw [← UInt8.toBitVec_inj]
  apply BitVec.eq_of_getElem_eq
  intro b hb
  simp only [← BitVec.getLsbD_eq_getElem hb]
  unfold packHint pack PackedBits.encode
  simp only [Bytes.ofFn, Vector.getElem_ofFn]
  rw [PackedBits.encodeByte_getLsbD_nat _ b hb]
  have hdiv : (8*i+b)/8 = i := by omega
  have hmod : (8*i+b)%8 = b := by omega
  by_cases hl : i = 31
  · subst i
    cases hint <;> interval_cases b <;>
      simp [HintPayload.tableWidth, HintPayload.lowBit, HintCodec.byteBitsLE, Vector.get_eq_getElem,
        UInt8.toBitVec_and, UInt8.toBitVec_or, BitVec.getLsbD_and, BitVec.getLsbD_or]
  · have hlow : 8*i+b < HintPayload.tableWidth := by
      change 8*i+b < 254
      omega
    simp only [hl, ↓reduceIte, hlow, ↓reduceDIte]
    simp only [HintPayload.lowBit, HintCodec.byteBitsLE, hdiv, hmod, Vector.get_eq_getElem]

def ciphertext (value : Word) (pad : WordBytes) (hint : Bool) : WordBytes :=
  packHint (FastPacking.encrypt value.val pad) hint

theorem ciphertext_eq (value : Word) (pad : WordBytes) (hint : Bool) :
    ciphertext value pad hint = pack (HintPayload.encrypt (HintPayload.encodeWord value) pad) hint := by
  rw [ciphertext, packHint_eq, FastPacking.encrypt_eq, HintPayload.encrypt_eq]
  rfl

def rowData (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) (index : RowIndex) : Word × WordBytes :=
  let falsePad := pairs index false purpose
  let truePad := pairs index true purpose
  let hint := padHint falsePad (coins index)
  let mask := maskFromPad falsePad hint
  (mask, ciphertext (HintPayload.share params mask index true) truePad hint)

theorem rowData_eq (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) (index : RowIndex) :
    rowData purpose pairs params coins index =
      HintAffineTable.rowData purpose pairs params coins index := by
  simp only [rowData, HintAffineTable.rowData, ciphertext_eq]

def garble (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) : Table :=
  let rows := Vector.ofFn (rowData purpose pairs params coins)
  let constant := FastPacking.encode (params.constant - ∑ i, (rows.get i).1).val
  Table.ofWords (prependWord constant fun i => (rows.get i).2)

theorem garble_eq (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) :
    garble purpose pairs params coins = HintAffineTable.garble purpose pairs params coins := by
  have hr : rowData purpose pairs params coins = HintAffineTable.rowData purpose pairs params coins :=
    funext fun index => rowData_eq purpose pairs params coins index
  unfold garble HintAffineTable.garble
  rw [hr]
  dsimp only
  rw [FastPacking.encode_eq]
  rfl

end G1Release.Submission.FastHintRow
