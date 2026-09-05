import GarblingPrize.Submission.CosetAffineMap

namespace GarblingPrize.Submission.CosetHintMap

/-!
Each of the four affine K openings is two affine Fp openings because its
input is embedded from Fp. The eight concrete hint tables below therefore
encode exactly the quotient already proved in CosetAffineMap. Their codec
has a fixed length of 8 * 8160 = 65280 bytes and both inverse laws.
-/

open GarblingPrize.Protected
open CosetCoordinates FourAffineQuotient
open scoped QuadraticAlgebra

abbrev TableKind := Fin 8
abbrev RowIndex := HintAffineTable.RowIndex
abbrev Params := IdealAffineTable.Params
abbrev Coins := TableKind → RowIndex → HintAffineTable.Coin

@[ext] structure Artifact where
  tables : TableKind → HintAffineTable.Table

def componentParams (imaginary : Bool) (coefficient constant : K) : Params :=
  if imaginary then ⟨coefficient.im, constant.im⟩ else ⟨coefficient.re, constant.re⟩

def params (base : Base K) (state : State K) (kind : TableKind) : Params :=
  let r := (state.1 : K)
  match kind.val with
  | 0 => componentParams false (r ^ 2 * base.x2) state.2.1
  | 1 => componentParams true (r ^ 2 * base.x2) state.2.1
  | 2 => componentParams false (r ^ 2 * base.x1 - state.2.1) state.2.2
  | 3 => componentParams true (r ^ 2 * base.x1 - state.2.1) state.2.2
  | 4 => componentParams false (r ^ 2 * base.y1) (r ^ 2 * base.constant - state.2.2)
  | 5 => componentParams true (r ^ 2 * base.y1) (r ^ 2 * base.constant - state.2.2)
  | 6 => componentParams false (r * base.denominatorX) (r * base.denominatorConstant)
  | _ => componentParams true (r * base.denominatorX) (r * base.denominatorConstant)

def inputFor {A : Type*} (kind : TableKind) (x y : A) : A :=
  if kind.val = 4 ∨ kind.val = 5 then y else x

def openedWords (values : Opened K) : TableKind → Word :=
  ![values.quadratic.re, values.quadratic.im, values.linear.re, values.linear.im,
    values.y.re, values.y.im, values.denominator.re, values.denominator.im]

theorem params_opened (base : Base K) (state : State K) (x y : Word) (kind : TableKind) :
    (params base state kind).coefficient * inputFor kind x y +
      (params base state kind).constant =
        openedWords (opened base state (C x) (C y)) kind := by
  fin_cases kind <;>
    simp [params, componentParams, inputFor, openedWords, opened,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

def purpose (mapIndex : Nat) (kind : TableKind) : Purpose := 8 * mapIndex + kind.val

def garble (mapIndex : Nat) (xPairs yPairs : RowIndex → Bool → Label)
    (base : Base K) (state : State K) (coins : Coins) : Artifact where
  tables := fun kind => HintAffineTable.garble (purpose mapIndex kind)
    (inputFor kind xPairs yPairs) (params base state kind) (coins kind)

def evaluateTable (mapIndex : Nat) (artifact : Artifact) (kind : TableKind)
    (xBits yBits : RowIndex → Bool) (xLabels yLabels : RowIndex → Label) : Option Word :=
  HintAffineTable.evaluate (purpose mapIndex kind) (artifact.tables kind)
    (inputFor kind xBits yBits) (inputFor kind xLabels yLabels)

theorem evaluateTable_garble (mapIndex : Nat) (xPairs yPairs : RowIndex → Bool → Label)
    (base : Base K) (state : State K) (coins : Coins) (kind : TableKind)
    (xBits yBits : RowIndex → Bool) :
    evaluateTable mapIndex (garble mapIndex xPairs yPairs base state coins) kind xBits yBits
      (fun i => xPairs i (xBits i)) (fun i => yPairs i (yBits i)) =
      some (openedWords (opened base state (C (IdealAffineTable.decodeBits xBits))
        (C (IdealAffineTable.decodeBits yBits))) kind) := by
  rw [← params_opened]
  by_cases hk : kind.val = 4 ∨ kind.val = 5 <;>
    simp [evaluateTable, garble, inputFor, hk, HintAffineTable.evaluate_garble]

def evaluate (mapIndex : Nat) (artifact : Artifact) (xBits yBits : RowIndex → Bool)
    (xLabels yLabels : RowIndex → Label) : Option (Opened K) := do
  let q0 ← evaluateTable mapIndex artifact 0 xBits yBits xLabels yLabels
  let q1 ← evaluateTable mapIndex artifact 1 xBits yBits xLabels yLabels
  let l0 ← evaluateTable mapIndex artifact 2 xBits yBits xLabels yLabels
  let l1 ← evaluateTable mapIndex artifact 3 xBits yBits xLabels yLabels
  let y0 ← evaluateTable mapIndex artifact 4 xBits yBits xLabels yLabels
  let y1 ← evaluateTable mapIndex artifact 5 xBits yBits xLabels yLabels
  let d0 ← evaluateTable mapIndex artifact 6 xBits yBits xLabels yLabels
  let d1 ← evaluateTable mapIndex artifact 7 xBits yBits xLabels yLabels
  pure ⟨⟨q0, q1⟩, ⟨l0, l1⟩, ⟨y0, y1⟩, ⟨d0, d1⟩⟩

theorem evaluate_garble (mapIndex : Nat) (xPairs yPairs : RowIndex → Bool → Label)
    (base : Base K) (state : State K) (coins : Coins) (xBits yBits : RowIndex → Bool) :
    evaluate mapIndex (garble mapIndex xPairs yPairs base state coins) xBits yBits
      (fun i => xPairs i (xBits i)) (fun i => yPairs i (yBits i)) =
      some (opened base state (C (IdealAffineTable.decodeBits xBits))
        (C (IdealAffineTable.decodeBits yBits))) := by
  simp only [evaluate, evaluateTable_garble, openedWords]
  rfl

def byteCount : Nat := 8 * HintAffineTable.tableByteCount

theorem byteCount_eq : byteCount = 65280 := by decide

set_option maxRecDepth 4096 in
def tableCodec : FixedCodec HintAffineTable.Table HintAffineTable.tableByteCount where
  encode := fun table => ⟨table.encode.data, table.encode_size⟩
  decode := fun bytes => HintAffineTable.Table.decode bytes.toByteArray
  decode_encode := HintAffineTable.Table.decode_encode
  encode_decode := by
    intro bytes table h
    apply Bytes.toByteArray_injective
    exact HintAffineTable.Table.encode_decode h

def encode (artifact : Artifact) : ByteArray := FixedCodec.encodeFin tableCodec 8 artifact.tables

@[simp] theorem encode_size (artifact : Artifact) : (encode artifact).size = byteCount :=
  FixedCodec.encodeFin_size tableCodec _

def decode (input : ByteArray) : Except WireDecodeError Artifact := do
  let tables ← FixedCodec.decodeFin tableCodec 8 input
  pure ⟨tables⟩

@[simp] theorem decode_encode (artifact : Artifact) : decode (encode artifact) = .ok artifact := by
  unfold decode encode
  rw [FixedCodec.decodeFin_encode]
  rfl

theorem encode_decode {bytes : ByteArray} {artifact : Artifact}
    (h : decode bytes = .ok artifact) : encode artifact = bytes := by
  unfold decode at h
  cases htables : FixedCodec.decodeFin tableCodec 8 bytes with
  | error error => simp [htables, Except.bind, bind] at h
  | ok tables =>
      have ha : ({ tables := tables } : Artifact) = artifact := by
        simp only [htables, Except.bind, bind] at h
        exact Except.ok.inj h
      rw [← ha]
      exact FixedCodec.encodeFin_decode tableCodec htables

end GarblingPrize.Submission.CosetHintMap
