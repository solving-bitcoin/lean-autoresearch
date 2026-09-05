import GarblingPrize.Submission.ProjectiveMap
import GarblingPrize.Submission.RCBMatrixEncoding

namespace GarblingPrize.Submission.GLVProjectiveMap

open GarblingPrize.Protected

abbrev Word := BN254.Fq
abbrev Table := IdealAffineTable.Table
abbrev MaskFiber := IdealAffineTable.MaskFiber
abbrev Coefficients := ProjectiveMap.Coefficients Word
abbrev Coordinates := ProjectiveMap.Coordinates Word

/-- Substitute `scale * x` for `x` in a general quadratic bivariate RCB
polynomial.  This is the coefficient transport used for the coordinate
endomorphisms `x |-> beta*x` and `x |-> beta^2*x`. -/
def substituteX (scale : Word) (coefficients : Coefficients) : Coefficients :=
  { x0 := coefficients.x0
    xX := coefficients.xX * scale
    xY := coefficients.xY
    xXY := coefficients.xXY * scale
    xYY := coefficients.xYY
    y0 := coefficients.y0
    yX := coefficients.yX * scale
    yXX := coefficients.yXX * scale ^ 2
    yYY := coefficients.yYY
    z0 := coefficients.z0
    zY := coefficients.zY
    zXX := coefficients.zXX * scale ^ 2
    zXY := coefficients.zXY * scale
    zYY := coefficients.zYY }

theorem polynomial_substituteX (scale : Word) (coefficients : Coefficients)
    (x y : Word) :
    ProjectiveMap.polynomial (substituteX scale coefficients) x y =
      ProjectiveMap.polynomial coefficients (scale * x) y := by
  apply ProjectiveMap.Coordinates.ext <;>
    simp [ProjectiveMap.polynomial, substituteX] <;> ring

/-- Eleven affine tables evaluate a general GLV-scaled RCB output polynomial.

The Z coordinate uses four openings rather than the usual five.  Its three
chain masks exploit `y^2 = x^3 + 3` through the exact identity

`y(zXY*x+m1) + x^2(m2*x+zXX) + (m3*y+z0+3*m2) +
  y((zYY-m2)*y+zY-m1-m3)`.

This removes one full affine table while retaining three independent mask
directions at every valid BN254 input. -/
inductive TableKind where
  | xLinear | xCross | xOuter | xCorrection
  | yCubic | yQuadratic | yLinear
  | zCross | zCubic | zLinear | zOuter
  deriving DecidableEq, Repr

instance : Fintype TableKind where
  elems := {.xLinear, .xCross, .xOuter, .xCorrection,
    .yCubic, .yQuadratic, .yLinear,
    .zCross, .zCubic, .zLinear, .zOuter}
  complete kind := by cases kind <;> simp

def TableKind.index : TableKind → Nat
  | .xLinear => 0 | .xCross => 1 | .xOuter => 2 | .xCorrection => 3
  | .yCubic => 4 | .yQuadratic => 5 | .yLinear => 6
  | .zCross => 7 | .zCubic => 8 | .zLinear => 9 | .zOuter => 10

@[ext] structure ChainMasks where
  xLinear : Word
  xCross : Word
  xOuter : Word
  yCubic : Word
  yQuadratic : Word
  zCross : Word
  zCubic : Word
  zLinear : Word

@[ext] structure Hidden where
  coefficients : Coefficients
  chainMasks : ChainMasks

def Hidden.params (hidden : Hidden) : TableKind → IdealAffineTable.Params
  | .xLinear =>
      ⟨hidden.coefficients.xX, hidden.chainMasks.xLinear⟩
  | .xCross =>
      ⟨hidden.coefficients.xXY, hidden.chainMasks.xCross⟩
  | .xOuter =>
      ⟨hidden.coefficients.xYY,
        hidden.coefficients.xY - hidden.chainMasks.xCross +
          hidden.chainMasks.xOuter⟩
  | .xCorrection =>
      ⟨-hidden.chainMasks.xOuter,
        hidden.coefficients.x0 - hidden.chainMasks.xLinear⟩
  | .yCubic =>
      ⟨hidden.coefficients.yYY, hidden.chainMasks.yCubic⟩
  | .yQuadratic =>
      ⟨hidden.coefficients.yXX - hidden.chainMasks.yCubic,
        hidden.chainMasks.yQuadratic⟩
  | .yLinear =>
      ⟨hidden.coefficients.yX - hidden.chainMasks.yQuadratic,
        hidden.coefficients.y0 + 3 * hidden.coefficients.yYY⟩
  | .zCross =>
      ⟨hidden.coefficients.zXY, hidden.chainMasks.zCross⟩
  | .zCubic =>
      ⟨hidden.chainMasks.zCubic, hidden.coefficients.zXX⟩
  | .zLinear =>
      ⟨hidden.chainMasks.zLinear,
        hidden.coefficients.z0 + 3 * hidden.chainMasks.zCubic⟩
  | .zOuter =>
      ⟨hidden.coefficients.zYY - hidden.chainMasks.zCubic,
        hidden.coefficients.zY - hidden.chainMasks.zCross -
          hidden.chainMasks.zLinear⟩

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
    (masks : (kind : TableKind) → MaskFiber (hidden.params kind).constant) :
    Artifact where
  tables := fun kind => IdealAffineTable.garble (purpose mapIndex kind)
    (pairsFor xPairs yPairs kind) (hidden.params kind) (masks kind)

def evaluate (mapIndex : Nat) (artifact : Artifact) (x y : Word)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (xLabels yLabels : Fin IdealAffineTable.tableWidth → Label) :
    Option Coordinates := do
  let xLinear ← IdealAffineTable.evaluate (purpose mapIndex .xLinear)
    (artifact.tables .xLinear) xBits xLabels
  let xCross ← IdealAffineTable.evaluate (purpose mapIndex .xCross)
    (artifact.tables .xCross) xBits xLabels
  let xOuter ← IdealAffineTable.evaluate (purpose mapIndex .xOuter)
    (artifact.tables .xOuter) yBits yLabels
  let xCorrection ← IdealAffineTable.evaluate (purpose mapIndex .xCorrection)
    (artifact.tables .xCorrection) yBits yLabels
  let yCubic ← IdealAffineTable.evaluate (purpose mapIndex .yCubic)
    (artifact.tables .yCubic) xBits xLabels
  let yQuadratic ← IdealAffineTable.evaluate (purpose mapIndex .yQuadratic)
    (artifact.tables .yQuadratic) xBits xLabels
  let yLinear ← IdealAffineTable.evaluate (purpose mapIndex .yLinear)
    (artifact.tables .yLinear) xBits xLabels
  let zCross ← IdealAffineTable.evaluate (purpose mapIndex .zCross)
    (artifact.tables .zCross) xBits xLabels
  let zCubic ← IdealAffineTable.evaluate (purpose mapIndex .zCubic)
    (artifact.tables .zCubic) xBits xLabels
  let zLinear ← IdealAffineTable.evaluate (purpose mapIndex .zLinear)
    (artifact.tables .zLinear) yBits yLabels
  let zOuter ← IdealAffineTable.evaluate (purpose mapIndex .zOuter)
    (artifact.tables .zOuter) yBits yLabels
  pure
    { x := xLinear + (xCross + xOuter) * y + xCorrection
      y := (yCubic * x + yQuadratic) * x + yLinear
      z := zCross * y + zCubic * x ^ 2 + zLinear + zOuter * y }

theorem evaluate_garble (mapIndex : Nat)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : Hidden)
    (masks : (kind : TableKind) → MaskFiber (hidden.params kind).constant)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (hcurve : IdealAffineTable.decodeBits yBits ^ 2 =
      IdealAffineTable.decodeBits xBits ^ 3 + 3) :
    evaluate mapIndex (garble mapIndex xPairs yPairs hidden masks)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      some (ProjectiveMap.polynomial hidden.coefficients
        (IdealAffineTable.decodeBits xBits)
        (IdealAffineTable.decodeBits yBits)) := by
  have tableCorrect (kind : TableKind)
      (bits : Fin IdealAffineTable.tableWidth → Bool)
      (pairs : Fin IdealAffineTable.tableWidth → Bool → Label) :
      IdealAffineTable.evaluate (purpose mapIndex kind)
          (IdealAffineTable.garble (purpose mapIndex kind) pairs
            (hidden.params kind) (masks kind)) bits
          (fun i => pairs i (bits i)) =
        some ((hidden.params kind).coefficient *
          IdealAffineTable.decodeBits bits + (hidden.params kind).constant) :=
    IdealAffineTable.evaluate_garble _ _ _ _ _
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
    simp [ProjectiveMap.polynomial, Hidden.params]
  · ring
  · linear_combination -hidden.coefficients.yYY * hcurve
  · linear_combination -hidden.chainMasks.zCubic * hcurve

def tableByteCount : Nat := IdealAffineTable.tableByteCount
def mapByteCount : Nat := 11 * tableByteCount

theorem mapByteCount_eq : mapByteCount = 177419 := by decide

def TableKind.finIndex (kind : TableKind) : Fin 11 :=
  ⟨kind.index, by cases kind <;> decide⟩

def tableKindAt (index : Fin 11) : TableKind :=
  match index.val with
  | 0 => .xLinear | 1 => .xCross | 2 => .xOuter | 3 => .xCorrection
  | 4 => .yCubic | 5 => .yQuadratic | 6 => .yLinear
  | 7 => .zCross | 8 => .zCubic | 9 => .zLinear | _ => .zOuter

@[simp] theorem tableKindAt_finIndex (kind : TableKind) :
    tableKindAt kind.finIndex = kind := by cases kind <;> rfl

@[simp] theorem finIndex_tableKindAt (index : Fin 11) :
    (tableKindAt index).finIndex = index := by
  apply Fin.ext
  have h := index.isLt
  interval_cases hvalue : index.val <;>
    simp [tableKindAt, TableKind.finIndex, TableKind.index, hvalue]

set_option maxRecDepth 4096 in
private def tableCodec : FixedCodec Table tableByteCount where
  encode := fun table => ⟨table.encode.data, table.encode_size⟩
  decode := fun bytes => IdealAffineTable.Table.decode bytes.toByteArray
  decode_encode := IdealAffineTable.Table.decode_encode
  encode_decode := by
    intro bytes table h
    apply Bytes.toByteArray_injective
    exact IdealAffineTable.Table.encode_decode h

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

end GarblingPrize.Submission.GLVProjectiveMap
