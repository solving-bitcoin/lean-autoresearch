import G1Release.Math.Bytes
import G1Release.Submission.HomogeneousRCB
import G1Release.Submission.AffineTable

namespace G1Release.Submission.ProjectiveMap

open G1Release.Math

abbrev Word := BN254.Fq
abbrev Table := AffineTable.Table
abbrev MaskFiber := AffineTable.MaskFiber
abbrev Label := SecretRelease.Label
abbrev Hash := SecretRelease.Hash

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
def Hidden.params (hidden : Hidden) : TableKind → AffineTable.Params
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

def labelsFor (xLabels yLabels : Fin 254 → Label) :
    TableKind → Fin 254 → Label
  | .shared | .xXY | .yCubic | .yQuadratic | .yLinear |
      .zSquare | .zCross | .zLinear => xLabels
  | .xYY | .xCorrection | .zCorrection => yLabels

def pairsFor (xPairs yPairs : Fin 254 → Bool → Label) :
    TableKind → Fin 254 → Bool → Label
  | .shared | .xXY | .yCubic | .yQuadratic | .yLinear |
      .zSquare | .zCross | .zLinear => xPairs
  | .xYY | .xCorrection | .zCorrection => yPairs

def purpose (mapIndex : Nat) (kind : TableKind) : Nat :=
  11 * mapIndex + kind.index

def garble (hash : Hash) (mapIndex : Nat)
    (xPairs yPairs : Fin 254 → Bool → Label)
    (hidden : Hidden)
    (masks : (kind : TableKind) → MaskFiber (hidden.params kind).constant) :
    Artifact where
  tables := fun kind => AffineTable.garble hash (purpose mapIndex kind)
    (pairsFor xPairs yPairs kind) (hidden.params kind) (masks kind)

@[irreducible] def evaluate (hash : Hash) (mapIndex : Nat) (artifact : Artifact) (x y : Word)
    (xBits yBits : Fin 254 → Bool)
    (xLabels yLabels : Fin 254 → Label) : Option (Coordinates Word) := do
  let shared ← AffineTable.evaluate hash (purpose mapIndex .shared)
    (artifact.tables .shared) xBits xLabels
  let xXY ← AffineTable.evaluate hash (purpose mapIndex .xXY)
    (artifact.tables .xXY) xBits xLabels
  let xYY ← AffineTable.evaluate hash (purpose mapIndex .xYY)
    (artifact.tables .xYY) yBits yLabels
  let xCorrection ← AffineTable.evaluate hash (purpose mapIndex .xCorrection)
    (artifact.tables .xCorrection) yBits yLabels
  let yCubic ← AffineTable.evaluate hash (purpose mapIndex .yCubic)
    (artifact.tables .yCubic) xBits xLabels
  let yQuadratic ← AffineTable.evaluate hash (purpose mapIndex .yQuadratic)
    (artifact.tables .yQuadratic) xBits xLabels
  let yLinear ← AffineTable.evaluate hash (purpose mapIndex .yLinear)
    (artifact.tables .yLinear) xBits xLabels
  let zSquare ← AffineTable.evaluate hash (purpose mapIndex .zSquare)
    (artifact.tables .zSquare) xBits xLabels
  let zCross ← AffineTable.evaluate hash (purpose mapIndex .zCross)
    (artifact.tables .zCross) xBits xLabels
  let zLinear ← AffineTable.evaluate hash (purpose mapIndex .zLinear)
    (artifact.tables .zLinear) xBits xLabels
  let zCorrection ← AffineTable.evaluate hash (purpose mapIndex .zCorrection)
    (artifact.tables .zCorrection) yBits yLabels
  pure
    { x := (xXY + xYY) * y + xCorrection - 2 * curveC * shared
      y := (yCubic * x + yQuadratic) * x + yLinear
      z := shared * x ^ 2 + zSquare * x + zCross * y + zLinear + zCorrection }

theorem evaluate_garble (hash : Hash) (mapIndex : Nat)
    (xPairs yPairs : Fin 254 → Bool → Label)
    (hidden : Hidden)
    (masks : (kind : TableKind) → MaskFiber (hidden.params kind).constant)
    (xBits yBits : Fin 254 → Bool)
    (hcurve : AffineTable.decodeBits yBits ^ 2 =
      AffineTable.decodeBits xBits ^ 3 + 3)
    (hxX : hidden.coefficients.xX =
      -(2 * curveC * hidden.coefficients.zYY))
    (hzXX : hidden.coefficients.zXX = 3 * hidden.coefficients.xYY) :
    evaluate hash mapIndex (garble hash mapIndex xPairs yPairs hidden masks)
        (AffineTable.decodeBits xBits) (AffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) =
      some (polynomial hidden.coefficients
        (AffineTable.decodeBits xBits)
        (AffineTable.decodeBits yBits)) := by
  have tableCorrect (kind : TableKind) (bits : Fin 254 → Bool)
      (pairs : Fin 254 → Bool → Label) :
      AffineTable.evaluate hash (purpose mapIndex kind)
          (AffineTable.garble hash (purpose mapIndex kind) pairs
            (hidden.params kind) (masks kind)) bits
          (fun i => pairs i (bits i)) =
        some ((hidden.params kind).coefficient *
          AffineTable.decodeBits bits + (hidden.params kind).constant) :=
    AffineTable.evaluate_garble hash _ _ _ _ _
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
theorem match_evaluate_garble (hash : Hash) (mapIndex : Nat)
    (xPairs yPairs : Fin 254 → Bool → Label)
    (hidden : Hidden)
    (masks : (kind : TableKind) → MaskFiber (hidden.params kind).constant)
    (xBits yBits : Fin 254 → Bool)
    (hcurve : AffineTable.decodeBits yBits ^ 2 =
      AffineTable.decodeBits xBits ^ 3 + 3)
    (hxX : hidden.coefficients.xX =
      -(2 * curveC * hidden.coefficients.zYY))
    (hzXX : hidden.coefficients.zXX = 3 * hidden.coefficients.xYY)
    {Result : Type*} (failure : Result)
    (success : Coordinates Word → Result) :
    (match evaluate hash mapIndex (garble hash mapIndex xPairs yPairs hidden masks)
        (AffineTable.decodeBits xBits) (AffineTable.decodeBits yBits)
        xBits yBits (fun i => xPairs i (xBits i))
        (fun i => yPairs i (yBits i)) with
      | none => failure
      | some coordinates => success coordinates) =
      success (polynomial hidden.coefficients
        (AffineTable.decodeBits xBits)
        (AffineTable.decodeBits yBits)) := by
  exact @congrArg (Option (Coordinates Word)) Result
    (evaluate hash mapIndex (garble hash mapIndex xPairs yPairs hidden masks)
      (AffineTable.decodeBits xBits) (AffineTable.decodeBits yBits)
      xBits yBits (fun i => xPairs i (xBits i)) (fun i => yPairs i (yBits i)))
    (some (polynomial hidden.coefficients
      (AffineTable.decodeBits xBits) (AffineTable.decodeBits yBits)))
    (fun result : Option (Coordinates Word) => match result with
      | none => failure
      | some coordinates => success coordinates)
    (evaluate_garble hash mapIndex xPairs yPairs hidden masks xBits yBits
      hcurve hxX hzXX)

def tableByteCount : Nat := AffineTable.tableByteCount
def mapByteCount : Nat := 11 * tableByteCount

theorem mapByteCount_eq : mapByteCount = 178816 := by decide

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

def encodeVec (artifact : Artifact) : G1Release.Math.Bytes 178816 :=
  G1Release.Math.Bytes.ofFn fun k =>
    let ti : Fin 11 := ⟨k.val / 16256, by omega⟩
    let off : Fin 16256 := ⟨k.val % 16256, Nat.mod_lt _ (by decide)⟩
    (artifact.tables (tableKindAt ti)).get off

def encode (artifact : Artifact) : ByteArray :=
  G1Release.Math.Bytes.toByteArray (encodeVec artifact)

@[simp] theorem encode_size (artifact : Artifact) :
    (encode artifact).size = mapByteCount := by
  simp [encode, encodeVec, mapByteCount, tableByteCount, AffineTable.tableByteCount]

def decode (input : ByteArray) : Option Artifact :=
  (G1Release.Math.Bytes.ofByteArray? 178816 input).map fun vec =>
    { tables := fun kind =>
        G1Release.Math.Bytes.ofFn fun off =>
          vec.get ⟨kind.finIndex.val * 16256 + off.val, by
            have hk := kind.finIndex.isLt
            have ho := off.isLt
            omega⟩ }

private theorem tableOffset_div (kind : TableKind) (j : Nat) (hj : j < 16256) :
    (kind.finIndex.val * 16256 + j) / 16256 = kind.finIndex.val := by omega

private theorem tableOffset_mod (kind : TableKind) (j : Nat) (hj : j < 16256) :
    (kind.finIndex.val * 16256 + j) % 16256 = j := by omega

theorem decode_encode (artifact : Artifact) :
    decode (encode artifact) = some artifact := by
  unfold decode encode
  rw [G1Release.Math.Bytes.ofByteArray?_toByteArray]
  simp only [Option.map_some]
  apply congrArg some
  apply Artifact.ext
  funext kind
  apply Vector.ext
  intro j hj
  have hdiv := tableOffset_div kind j hj
  have hmod := tableOffset_mod kind j hj
  have hlt : (kind.finIndex.val * 16256 + j) / 16256 < 11 := by
    rw [hdiv]; exact kind.finIndex.isLt
  have hidx : (⟨(kind.finIndex.val * 16256 + j) / 16256, hlt⟩ : Fin 11) =
      kind.finIndex := Fin.ext hdiv
  have hjmod : j % 16256 = j := Nat.mod_eq_of_lt hj
  simp [encodeVec, G1Release.Math.Bytes.ofFn, Vector.getElem_ofFn,
    hidx, tableKindAt_finIndex, Vector.get_eq_getElem, hjmod]

set_option maxRecDepth 4096 in
theorem encode_decode {bytes : ByteArray} {artifact : Artifact}
    (h : decode bytes = some artifact) : encode artifact = bytes := by
  unfold decode at h
  cases hvec : G1Release.Math.Bytes.ofByteArray? 178816 bytes with
  | none => simp [hvec] at h
  | some vec =>
      simp only [hvec, Option.map_some, Option.some.injEq] at h
      subst artifact
      have hb : bytes = G1Release.Math.Bytes.toByteArray vec :=
        G1Release.Math.Bytes.ofByteArray?_eq_some_iff.mp hvec
      rw [hb, encode]
      apply congrArg G1Release.Math.Bytes.toByteArray
      apply Vector.ext
      intro k hk
      unfold encodeVec
      simp only [G1Release.Math.Bytes.ofFn, Vector.getElem_ofFn,
        finIndex_tableKindAt, Vector.get_eq_getElem]
      congr 1
      rw [Nat.mul_comm]
      exact Nat.div_add_mod k 16256

end G1Release.Submission.ProjectiveMap
