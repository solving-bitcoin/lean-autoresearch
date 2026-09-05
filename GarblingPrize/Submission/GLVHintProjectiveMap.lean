import GarblingPrize.Submission.GLVProjectiveMap
import GarblingPrize.Submission.HintAffineTable

namespace GarblingPrize.Submission.GLVHintProjectiveMap

/-! The established eleven-table GLV polynomial encoding with exact one-hint
rows. Its chain-mask mathematics is unchanged; each table now uses 8160 bytes. -/

open GarblingPrize.Protected

abbrev Word := GLVProjectiveMap.Word
abbrev Table := HintAffineTable.Table
abbrev Coefficients := GLVProjectiveMap.Coefficients
abbrev Coordinates := GLVProjectiveMap.Coordinates
abbrev TableKind := GLVProjectiveMap.TableKind
abbrev Hidden := GLVProjectiveMap.Hidden

@[ext] structure Artifact where
  tables : TableKind → Table

def labelsFor (xLabels yLabels : Fin IdealAffineTable.tableWidth → Label) :
    TableKind → Fin IdealAffineTable.tableWidth → Label
  | .xLinear | .xCross | .yCubic | .yQuadratic | .yLinear |
      .zCross | .zCubic => xLabels
  | .xOuter | .xCorrection | .zLinear | .zOuter => yLabels

def pairsFor
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label) :
    TableKind → Fin IdealAffineTable.tableWidth → Bool → Label
  | .xLinear | .xCross | .yCubic | .yQuadratic | .yLinear |
      .zCross | .zCubic => xPairs
  | .xOuter | .xCorrection | .zLinear | .zOuter => yPairs

def purpose (mapIndex : Nat) (kind : TableKind) : Purpose :=
  11 * mapIndex + kind.index

def garble (mapIndex : Nat)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : Hidden)
    (coins : TableKind → HintAffineTable.RowIndex → HintAffineTable.Coin) :
    Artifact where
  tables := fun kind => HintAffineTable.garble (purpose mapIndex kind)
    (pairsFor xPairs yPairs kind) (hidden.params kind) (coins kind)

def evaluate (mapIndex : Nat) (artifact : Artifact) (x y : Word)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (xLabels yLabels : Fin IdealAffineTable.tableWidth → Label) :
    Option Coordinates := do
  let xLinear ← HintAffineTable.evaluate (purpose mapIndex .xLinear)
    (artifact.tables .xLinear) xBits xLabels
  let xCross ← HintAffineTable.evaluate (purpose mapIndex .xCross)
    (artifact.tables .xCross) xBits xLabels
  let xOuter ← HintAffineTable.evaluate (purpose mapIndex .xOuter)
    (artifact.tables .xOuter) yBits yLabels
  let xCorrection ← HintAffineTable.evaluate (purpose mapIndex .xCorrection)
    (artifact.tables .xCorrection) yBits yLabels
  let yCubic ← HintAffineTable.evaluate (purpose mapIndex .yCubic)
    (artifact.tables .yCubic) xBits xLabels
  let yQuadratic ← HintAffineTable.evaluate (purpose mapIndex .yQuadratic)
    (artifact.tables .yQuadratic) xBits xLabels
  let yLinear ← HintAffineTable.evaluate (purpose mapIndex .yLinear)
    (artifact.tables .yLinear) xBits xLabels
  let zCross ← HintAffineTable.evaluate (purpose mapIndex .zCross)
    (artifact.tables .zCross) xBits xLabels
  let zCubic ← HintAffineTable.evaluate (purpose mapIndex .zCubic)
    (artifact.tables .zCubic) xBits xLabels
  let zLinear ← HintAffineTable.evaluate (purpose mapIndex .zLinear)
    (artifact.tables .zLinear) yBits yLabels
  let zOuter ← HintAffineTable.evaluate (purpose mapIndex .zOuter)
    (artifact.tables .zOuter) yBits yLabels
  pure
    { x := xLinear + (xCross + xOuter) * y + xCorrection
      y := (yCubic * x + yQuadratic) * x + yLinear
      z := zCross * y + zCubic * x ^ 2 + zLinear + zOuter * y }

theorem evaluate_garble (mapIndex : Nat)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : Hidden)
    (coins : TableKind → HintAffineTable.RowIndex → HintAffineTable.Coin)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (hcurve : IdealAffineTable.decodeBits yBits ^ 2 =
      IdealAffineTable.decodeBits xBits ^ 3 + 3) :
    evaluate mapIndex (garble mapIndex xPairs yPairs hidden coins)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      some (ProjectiveMap.polynomial hidden.coefficients
        (IdealAffineTable.decodeBits xBits)
        (IdealAffineTable.decodeBits yBits)) := by
  have tableCorrect (kind : TableKind)
      (bits : Fin IdealAffineTable.tableWidth → Bool)
      (pairs : Fin IdealAffineTable.tableWidth → Bool → Label) :
      HintAffineTable.evaluate (purpose mapIndex kind)
          (HintAffineTable.garble (purpose mapIndex kind) pairs
            (hidden.params kind) (coins kind)) bits
          (fun i => pairs i (bits i)) =
        some ((hidden.params kind).coefficient *
          IdealAffineTable.decodeBits bits + (hidden.params kind).constant) :=
    HintAffineTable.evaluate_garble _ _ _ _ _
  have hxLinear := tableCorrect .xLinear xBits xPairs
  have hxCross := tableCorrect .xCross xBits xPairs
  have hxOuter := tableCorrect .xOuter yBits yPairs
  have hxCorrection := tableCorrect .xCorrection yBits yPairs
  have hyCubic := tableCorrect .yCubic xBits xPairs
  have hyQuadratic := tableCorrect .yQuadratic xBits xPairs
  have hyLinear := tableCorrect .yLinear xBits xPairs
  have hzCross := tableCorrect .zCross xBits xPairs
  have hzCubic := tableCorrect .zCubic xBits xPairs
  have hzLinear := tableCorrect .zLinear yBits yPairs
  have hzOuter := tableCorrect .zOuter yBits yPairs
  unfold evaluate
  simp only [garble, pairsFor]
  rw [hxLinear, hxCross, hxOuter, hxCorrection,
    hyCubic, hyQuadratic, hyLinear, hzCross,
    hzCubic, hzLinear, hzOuter]
  apply congrArg some
  apply ProjectiveMap.Coordinates.ext <;>
    simp [ProjectiveMap.polynomial, GLVProjectiveMap.Hidden.params]
  · ring
  · linear_combination -hidden.coefficients.yYY * hcurve
  · linear_combination -hidden.chainMasks.zCubic * hcurve

def tableByteCount : Nat := HintAffineTable.tableByteCount
def mapByteCount : Nat := 11 * tableByteCount

theorem mapByteCount_eq : mapByteCount = 89760 := by decide

abbrev tableKindAt := GLVProjectiveMap.tableKindAt

set_option maxRecDepth 4096 in
private def tableCodec : FixedCodec Table tableByteCount where
  encode := fun table => ⟨table.encode.data, table.encode_size⟩
  decode := fun bytes => HintAffineTable.Table.decode bytes.toByteArray
  decode_encode := HintAffineTable.Table.decode_encode
  encode_decode := by
    intro bytes table h
    apply Bytes.toByteArray_injective
    exact HintAffineTable.Table.encode_decode h

def encode (artifact : Artifact) : ByteArray :=
  FixedCodec.encodeFin tableCodec 11
    (fun index => artifact.tables (tableKindAt index))

@[simp] theorem encode_size (artifact : Artifact) :
    (encode artifact).size = mapByteCount := by
  exact FixedCodec.encodeFin_size tableCodec _

def decode (input : ByteArray) : Except WireDecodeError Artifact := do
  let tables ← FixedCodec.decodeFin tableCodec 11 input
  pure ⟨fun kind => tables kind.finIndex⟩

@[simp] theorem decode_encode (artifact : Artifact) :
    decode (encode artifact) = .ok artifact := by
  unfold decode encode
  rw [FixedCodec.decodeFin_encode]
  apply congrArg Except.ok
  apply Artifact.ext
  funext kind
  simp

theorem encode_decode {bytes : ByteArray} {artifact : Artifact}
    (h : decode bytes = .ok artifact) : encode artifact = bytes := by
  unfold decode at h
  cases htables : FixedCodec.decodeFin tableCodec 11 bytes with
  | error error => simp [htables, Except.bind, bind] at h
  | ok tables =>
      have hartifact :
          ({ tables := fun kind => tables kind.finIndex } : Artifact) =
            artifact := by
        simp only [htables, Except.bind, bind] at h
        exact Except.ok.inj h
      rw [← hartifact]
      unfold encode
      have hfunctions :
          (fun index =>
              (fun kind => tables kind.finIndex) (tableKindAt index)) =
            tables := by
        funext index
        simp
      rw [hfunctions]
      exact FixedCodec.encodeFin_decode tableCodec htables

end GarblingPrize.Submission.GLVHintProjectiveMap
