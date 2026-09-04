import GarblingPrize.Submission.HomogeneousRCB
import GarblingPrize.Submission.IdealAffineTable

namespace GarblingPrize.Submission.ProjectiveMap

open GarblingPrize.Protected
open GarblingPrize.Submission

abbrev Word := BN254.Fq
abbrev Table := IdealAffineTable.Table
abbrev MaskFiber := IdealAffineTable.MaskFiber

inductive TableKind where
  | shared
  | xXY | xYY | xCorrection
  | yCubic | yQuadratic | yLinear
  | zSquare | zCross | zLinear | zCorrection
  deriving DecidableEq, Repr

instance : Fintype TableKind where
  elems := {.shared, .xXY, .xYY, .xCorrection,
    .yCubic, .yQuadratic, .yLinear,
    .zSquare, .zCross, .zLinear, .zCorrection}
  complete kind := by cases kind <;> simp

def TableKind.index : TableKind → Nat
  | .shared => 0
  | .xXY => 1 | .xYY => 2 | .xCorrection => 3
  | .yCubic => 4 | .yQuadratic => 5 | .yLinear => 6
  | .zSquare => 7 | .zCross => 8 | .zLinear => 9
  | .zCorrection => 10

/-- The RCB parameter `3b` for the protected BN254 curve `y² = x³ + 3`. -/
def curveC : Word := 3 * 3

@[ext] structure Coefficients (R : Type*) where
  x0 : R
  xX : R
  xY : R
  xXY : R
  xYY : R
  y0 : R
  yX : R
  yXX : R
  yYY : R
  z0 : R
  zY : R
  zXX : R
  zXY : R
  zYY : R

@[ext] structure ChainMasks (R : Type*) where
  shared : R
  xCross : R
  xOuter : R
  yCubic : R
  yQuadratic : R
  zSquare : R
  zCross : R
  zLinear : R

@[ext] structure Hidden where
  coefficients : Coefficients Word
  chainMasks : ChainMasks Word

/-- Eleven-table randomized encoding of one RCB map.

The shared X-input table packages `zYY*x + 3*xYY + mask`.  RCB gives
`xX = -2*(3b)*zYY` and `zXX = 3*xYY`, so the same selected opening supplies
the X linear term and the Z cubic/quadratic terms.  The valid-input identity
`y² = x³ + 3` turns Y into a three-stage X Horner chain and lets Z consume
the shared cubic.  The remaining eight constants are independent threaded
masks, exactly one for every selected opening beyond the three output
coordinates. -/
def Hidden.params (hidden : Hidden) : TableKind → IdealAffineTable.Params
  | .shared => ⟨hidden.coefficients.zYY,
      3 * hidden.coefficients.xYY + hidden.chainMasks.shared⟩
  | .xXY => ⟨hidden.coefficients.xXY, hidden.chainMasks.xCross⟩
  | .xYY => ⟨hidden.coefficients.xYY,
      hidden.coefficients.xY - hidden.chainMasks.xCross +
        hidden.chainMasks.xOuter⟩
  | .xCorrection => ⟨-hidden.chainMasks.xOuter,
      hidden.coefficients.x0 + 6 * curveC * hidden.coefficients.xYY +
        2 * curveC * hidden.chainMasks.shared⟩
  | .yCubic => ⟨hidden.coefficients.yYY, hidden.chainMasks.yCubic⟩
  | .yQuadratic => ⟨hidden.coefficients.yXX - hidden.chainMasks.yCubic,
      hidden.chainMasks.yQuadratic⟩
  | .yLinear => ⟨hidden.coefficients.yX - hidden.chainMasks.yQuadratic,
      hidden.coefficients.y0 + 3 * hidden.coefficients.yYY⟩
  | .zSquare => ⟨-hidden.chainMasks.shared, hidden.chainMasks.zSquare⟩
  | .zCross => ⟨hidden.coefficients.zXY, hidden.chainMasks.zCross⟩
  | .zLinear => ⟨-hidden.chainMasks.zSquare,
      hidden.chainMasks.zLinear⟩
  | .zCorrection => ⟨hidden.coefficients.zY - hidden.chainMasks.zCross,
      hidden.coefficients.z0 + 3 * hidden.coefficients.zYY -
        hidden.chainMasks.zLinear⟩

@[ext] structure Coordinates (R : Type*) where
  x : R
  y : R
  z : R

def Coordinates.ofHomogeneous (point : HomogeneousRCB.Point R) : Coordinates R :=
  ⟨point.x, point.y, point.z⟩

def polynomial {R : Type*} [CommRing R]
    (coefficients : Coefficients R) (x y : R) : Coordinates R where
  x := coefficients.x0 + coefficients.xX * x + coefficients.xY * y +
    coefficients.xXY * (x * y) + coefficients.xYY * (y * y)
  y := coefficients.y0 + coefficients.yX * x +
    coefficients.yXX * (x * x) + coefficients.yYY * (y * y)
  z := coefficients.z0 + coefficients.zY * y +
    coefficients.zXX * (x * x) + coefficients.zXY * (x * y) +
    coefficients.zYY * (y * y)

def Coefficients.scale {R : Type*} [CommRing R]
    (factor : R) (coefficients : Coefficients R) : Coefficients R where
  x0 := factor * coefficients.x0
  xX := factor * coefficients.xX
  xY := factor * coefficients.xY
  xXY := factor * coefficients.xXY
  xYY := factor * coefficients.xYY
  y0 := factor * coefficients.y0
  yX := factor * coefficients.yX
  yXX := factor * coefficients.yXX
  yYY := factor * coefficients.yYY
  z0 := factor * coefficients.z0
  zY := factor * coefficients.zY
  zXX := factor * coefficients.zXX
  zXY := factor * coefficients.zXY
  zYY := factor * coefficients.zYY

theorem polynomial_scale {R : Type*} [CommRing R]
    (factor : R) (coefficients : Coefficients R) (x y : R) :
    polynomial (coefficients.scale factor) x y =
      Coordinates.ofHomogeneous
        (HomogeneousRCB.randomize factor
          { x := (polynomial coefficients x y).x
            y := (polynomial coefficients x y).y
            z := (polynomial coefficients x y).z }) := by
  apply Coordinates.ext <;>
    simp [polynomial, Coefficients.scale, Coordinates.ofHomogeneous,
      HomogeneousRCB.randomize] <;> ring

def coefficients {R : Type*} [CommRing R]
    (c : R) (offset : HomogeneousRCB.Point R)
    (selector : Bool) (sign : HomogeneousRCB.Sign) : Coefficients R :=
  let a := HomogeneousRCB.selectorValue (F := R) selector
  let epsilon := sign.value (F := R)
  { x0 := (1 - a) * offset.x * offset.y - a * c * offset.x * offset.y
    xX := -(2 * a * c * offset.y * offset.z)
    xY := -(2 * a * epsilon * c * offset.x * offset.z)
    xXY := a * epsilon * (offset.y ^ 2 - c * offset.z ^ 2)
    xYY := a * offset.x * offset.y
    y0 := (1 - a) * offset.y ^ 2 - a * c ^ 2 * offset.z ^ 2
    yX := 3 * a * c * offset.x ^ 2
    yXX := 3 * a * c * offset.x * offset.z
    yYY := a * offset.y ^ 2
    z0 := (1 - a) * offset.y * offset.z + a * c * offset.y * offset.z
    zY := a * epsilon * (offset.y ^ 2 + c * offset.z ^ 2)
    zXX := 3 * a * offset.x * offset.y
    zXY := 3 * a * epsilon * offset.x ^ 2
    zYY := a * offset.y * offset.z }

theorem coefficients_xX {R : Type*} [CommRing R]
    (c : R) (offset : HomogeneousRCB.Point R) (selector : Bool)
    (sign : HomogeneousRCB.Sign) :
    (coefficients c offset selector sign).xX =
      -(2 * c * (coefficients c offset selector sign).zYY) := by
  cases selector <;> cases sign <;>
    simp [coefficients, HomogeneousRCB.selectorValue,
      HomogeneousRCB.Sign.value] <;> ring

theorem coefficients_zXX {R : Type*} [CommRing R]
    (c : R) (offset : HomogeneousRCB.Point R) (selector : Bool)
    (sign : HomogeneousRCB.Sign) :
    (coefficients c offset selector sign).zXX =
      3 * (coefficients c offset selector sign).xYY := by
  cases selector <;> cases sign <;>
    simp [coefficients, HomogeneousRCB.selectorValue,
      HomogeneousRCB.Sign.value] <;> ring

theorem scale_xX {R : Type*} [CommRing R] (factor c : R)
    (coefficients : Coefficients R)
    (h : coefficients.xX = -(2 * c * coefficients.zYY)) :
    (coefficients.scale factor).xX =
      -(2 * c * (coefficients.scale factor).zYY) := by
  simp [Coefficients.scale, h]
  ring

theorem scale_zXX {R : Type*} [CommRing R] (factor : R)
    (coefficients : Coefficients R)
    (h : coefficients.zXX = 3 * coefficients.xYY) :
    (coefficients.scale factor).zXX =
      3 * (coefficients.scale factor).xYY := by
  simp [Coefficients.scale, h]
  ring

theorem polynomial_coefficients {R : Type*} [CommRing R] (c : R)
    (offset : HomogeneousRCB.Point R) (selector : Bool)
    (sign : HomogeneousRCB.Sign) (x y : R) :
    polynomial (coefficients c offset selector sign) x y =
      Coordinates.ofHomogeneous (HomogeneousRCB.formula c offset
        (HomogeneousRCB.selectedInput selector sign ⟨x, y, 1⟩)) := by
  rw [HomogeneousRCB.formula_selectedInput]
  apply Coordinates.ext
  · cases selector <;> cases sign <;>
      simp [polynomial, coefficients, Coordinates.ofHomogeneous,
        HomogeneousRCB.selectedX, HomogeneousRCB.selectorValue,
        HomogeneousRCB.Sign.value] <;> ring
  · cases selector <;> cases sign <;>
      simp [polynomial, coefficients, Coordinates.ofHomogeneous,
        HomogeneousRCB.selectedY, HomogeneousRCB.selectorValue,
        HomogeneousRCB.Sign.value] <;> ring
  · cases selector <;> cases sign <;>
      simp [polynomial, coefficients, Coordinates.ofHomogeneous,
        HomogeneousRCB.selectedZ, HomogeneousRCB.selectorValue,
        HomogeneousRCB.Sign.value] <;> ring

@[ext] structure Artifact where
  tables : TableKind → Table

def labelsFor (xLabels yLabels : Fin IdealAffineTable.tableWidth → Label) :
    TableKind → Fin IdealAffineTable.tableWidth → Label
  | .shared | .xXY | .yCubic | .yQuadratic | .yLinear |
      .zSquare | .zCross | .zLinear => xLabels
  | .xYY | .xCorrection | .zCorrection => yLabels

def pairsFor (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label) :
    TableKind → Fin IdealAffineTable.tableWidth → Bool → Label
  | .shared | .xXY | .yCubic | .yQuadratic | .yLinear |
      .zSquare | .zCross | .zLinear => xPairs
  | .xYY | .xCorrection | .zCorrection => yPairs

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
    (xLabels yLabels : Fin IdealAffineTable.tableWidth → Label) : Option (Coordinates Word) := do
  let shared ← IdealAffineTable.evaluate (purpose mapIndex .shared)
    (artifact.tables .shared) xBits xLabels
  let xXY ← IdealAffineTable.evaluate (purpose mapIndex .xXY)
    (artifact.tables .xXY) xBits xLabels
  let xYY ← IdealAffineTable.evaluate (purpose mapIndex .xYY)
    (artifact.tables .xYY) yBits yLabels
  let xCorrection ← IdealAffineTable.evaluate (purpose mapIndex .xCorrection)
    (artifact.tables .xCorrection) yBits yLabels
  let yCubic ← IdealAffineTable.evaluate (purpose mapIndex .yCubic)
    (artifact.tables .yCubic) xBits xLabels
  let yQuadratic ← IdealAffineTable.evaluate (purpose mapIndex .yQuadratic)
    (artifact.tables .yQuadratic) xBits xLabels
  let yLinear ← IdealAffineTable.evaluate (purpose mapIndex .yLinear)
    (artifact.tables .yLinear) xBits xLabels
  let zSquare ← IdealAffineTable.evaluate (purpose mapIndex .zSquare)
    (artifact.tables .zSquare) xBits xLabels
  let zCross ← IdealAffineTable.evaluate (purpose mapIndex .zCross)
    (artifact.tables .zCross) xBits xLabels
  let zLinear ← IdealAffineTable.evaluate (purpose mapIndex .zLinear)
    (artifact.tables .zLinear) xBits xLabels
  let zCorrection ← IdealAffineTable.evaluate (purpose mapIndex .zCorrection)
    (artifact.tables .zCorrection) yBits yLabels
  pure
    { x := (xXY + xYY) * y + xCorrection - 2 * curveC * shared
      y := (yCubic * x + yQuadratic) * x + yLinear
      z := shared * x ^ 2 + zSquare * x + zCross * y + zLinear + zCorrection }

theorem evaluate_garble (mapIndex : Nat)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : Hidden)
    (masks : (kind : TableKind) → MaskFiber (hidden.params kind).constant)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (hcurve : IdealAffineTable.decodeBits yBits ^ 2 =
      IdealAffineTable.decodeBits xBits ^ 3 + 3)
    (hxX : hidden.coefficients.xX =
      -(2 * curveC * hidden.coefficients.zYY))
    (hzXX : hidden.coefficients.zXX = 3 * hidden.coefficients.xYY) :
    evaluate mapIndex (garble mapIndex xPairs yPairs hidden masks)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      some (polynomial hidden.coefficients
        (IdealAffineTable.decodeBits xBits)
        (IdealAffineTable.decodeBits yBits)) := by
  have tableCorrect (kind : TableKind) (bits : Fin IdealAffineTable.tableWidth → Bool)
      (pairs : Fin IdealAffineTable.tableWidth → Bool → Label) :
      IdealAffineTable.evaluate (purpose mapIndex kind)
          (IdealAffineTable.garble (purpose mapIndex kind) pairs
            (hidden.params kind) (masks kind)) bits
          (fun i => pairs i (bits i)) =
        some ((hidden.params kind).coefficient *
          IdealAffineTable.decodeBits bits + (hidden.params kind).constant) :=
    IdealAffineTable.evaluate_garble _ _ _ _ _
  have hshared := tableCorrect .shared xBits xPairs
  have hxXY := tableCorrect .xXY xBits xPairs
  have hxYY := tableCorrect .xYY yBits yPairs
  have hxCorrection := tableCorrect .xCorrection yBits yPairs
  have hyCubic := tableCorrect .yCubic xBits xPairs
  have hyQuadratic := tableCorrect .yQuadratic xBits xPairs
  have hyLinear := tableCorrect .yLinear xBits xPairs
  have hzSquare := tableCorrect .zSquare xBits xPairs
  have hzCross := tableCorrect .zCross xBits xPairs
  have hzLinear := tableCorrect .zLinear xBits xPairs
  have hzCorrection := tableCorrect .zCorrection yBits yPairs
  unfold evaluate
  simp only [garble, pairsFor]
  rw [hshared, hxXY, hxYY, hxCorrection,
    hyCubic, hyQuadratic, hyLinear,
    hzSquare, hzCross, hzLinear, hzCorrection]
  apply congrArg some
  apply Coordinates.ext <;>
    simp [polynomial, Hidden.params]
  · rw [hxX]
    ring
  · linear_combination -hidden.coefficients.yYY * hcurve
  · rw [hzXX]
    linear_combination -hidden.coefficients.zYY * hcurve

/-- Postcompose a successful map opening without re-normalizing the eleven
nested option binds in downstream refinement proofs. -/
theorem match_evaluate_garble (mapIndex : Nat)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : Hidden)
    (masks : (kind : TableKind) → MaskFiber (hidden.params kind).constant)
    (xBits yBits : Fin IdealAffineTable.tableWidth → Bool)
    (hcurve : IdealAffineTable.decodeBits yBits ^ 2 =
      IdealAffineTable.decodeBits xBits ^ 3 + 3)
    (hxX : hidden.coefficients.xX =
      -(2 * curveC * hidden.coefficients.zYY))
    (hzXX : hidden.coefficients.zXX = 3 * hidden.coefficients.xYY)
    {Result : Type*} (failure : Result)
    (success : Coordinates Word → Result) :
    (match evaluate mapIndex (garble mapIndex xPairs yPairs hidden masks)
        (IdealAffineTable.decodeBits xBits) (IdealAffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) with
      | none => failure
      | some coordinates => success coordinates) =
      success (polynomial hidden.coefficients
        (IdealAffineTable.decodeBits xBits)
        (IdealAffineTable.decodeBits yBits)) := by
  exact congrArg
    (fun result => match result with
      | none => failure
      | some coordinates => success coordinates)
    (evaluate_garble mapIndex xPairs yPairs hidden masks xBits yBits
      hcurve hxX hzXX)

def tableByteCount : Nat := IdealAffineTable.tableByteCount
def mapByteCount : Nat := 11 * tableByteCount

theorem mapByteCount_eq : mapByteCount = 177419 := by decide

def TableKind.finIndex (kind : TableKind) : Fin 11 :=
  ⟨kind.index, by cases kind <;> decide⟩

def tableKindAt (index : Fin 11) : TableKind :=
  match index.val with
  | 0 => .shared
  | 1 => .xXY | 2 => .xYY | 3 => .xCorrection
  | 4 => .yCubic | 5 => .yQuadratic | 6 => .yLinear
  | 7 => .zSquare | 8 => .zCross | 9 => .zLinear
  | _ => .zCorrection

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
      have hartifact : ({ tables := fun kind => tables kind.finIndex } :
          Artifact) = artifact := by
        simp only [htables, Except.bind, bind] at h
        change Except.ok
          ({ tables := fun kind => tables kind.finIndex } : Artifact) =
            Except.ok artifact at h
        exact Except.ok.inj h
      rw [← hartifact]
      unfold encode
      have htableFunctions :
          (fun index : Fin 11 => tables (tableKindAt index).finIndex) = tables := by
        funext index
        simp
      rw [htableFunctions]
      exact FixedCodec.encodeFin_decode tableCodec htables

end GarblingPrize.Submission.ProjectiveMap
