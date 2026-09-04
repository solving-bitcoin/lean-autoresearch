import GarblingPrize.Protected.SHA256Vectors
import GarblingPrize.Protected.Executable

namespace GarblingPrize.Protected.Runner

/-!
# Protected executable runner

This entire runner is elaborated before any untrusted submission is imported.
The executable bridge supplies only the audited scheme and its proved byte
bound. The protected runner owns internal-seed expansion, while its test-only
label provider uses a separate seed.
-/

def usage : String :=
  "usage:\n" ++
  "  g1-challenge selftest\n" ++
  "  g1-challenge pad <64-hex-seed> label <wire> <0|1> <purpose>\n" ++
  "  g1-challenge sample <64-hex-seed> <positive-modulus> <purpose>\n" ++
  "  g1-challenge run-case --randomness-seed <hex> --label-seed <hex> " ++
    "--q <infinity|x,y> " ++
    "--r <decimal> --a <x,y>\n" ++
  "  g1-challenge benchmark --cases <N>"

private def hexDigit? : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9
  | 'a' | 'A' => some 10 | 'b' | 'B' => some 11
  | 'c' | 'C' => some 12 | 'd' | 'D' => some 13
  | 'e' | 'E' => some 14 | 'f' | 'F' => some 15
  | _ => none

private def parseHexBytes : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let high ← hexDigit? high
      let low ← hexDigit? low
      let tail ← parseHexBytes rest
      pure (UInt8.ofNat (16 * high + low) :: tail)
  | _ => none

def parseSeed (value : String) : Option MasterSeed := do
  if value.length = 64 then pure () else none
  let bytes ← parseHexBytes value.toList
  Bytes.ofByteArray? 32 (ByteArray.mk bytes.toArray)

def requireSeed (value : String) : Except String MasterSeed :=
  match parseSeed value with
  | some seed => .ok seed
  | none => .error "seed must contain exactly 64 hexadecimal digits"

def byteHex (value : UInt8) : String :=
  String.ofList
    [Nat.digitChar (value.toNat / 16), Nat.digitChar (value.toNat % 16)]

def bytesHex (value : Bytes n) : String :=
  String.join ((List.finRange n).map fun index => byteHex (value.get index))

def parseNat (name value : String) : Except String Nat :=
  match value.toNat? with
  | some number =>
      if toString number = value then .ok number
      else .error (name ++ " must be a canonical decimal natural")
  | none => .error (name ++ " must be a canonical decimal natural")

def parseBit (value : String) : Except String Bool :=
  if value = "0" then .ok false
  else if value = "1" then .ok true
  else .error "bit must be 0 or 1"

def parseWire (value : String) : Except String BitIndex := do
  let wire ← parseNat "wire" value
  if h : wire < coordinateBitCount then
    pure ⟨wire, h⟩
  else
    throw ("wire must be below " ++ toString coordinateBitCount)

def runPad : List String → Except String SeedLabel
  | [seedText, "label", wireText, bitText, purposeText] => do
      let seed ← requireSeed seedText
      let wire ← parseWire wireText
      let bit ← parseBit bitText
      let purpose ← parseNat "purpose" purposeText
      pure (TestLabelOracle.pad seed wire bit purpose)
  | _ => .error usage

def runSample : List String → Except String Nat
  | [seedText, modulusText, purposeText] => do
      let seed ← requireSeed seedText
      let modulus ← parseNat "modulus" modulusText
      if hpositive : 0 < modulus then
        if hfits : modulus ≤ 2 ^ 3072 then
          let purpose ← parseNat "purpose" purposeText
          pure (SeededInternalOracle.sample seed
            ⟨modulus, hpositive, hfits⟩ purpose).val
        else
          throw "modulus must be at most 2^3072"
      else
        throw "modulus must be positive"
  | _ => .error usage

def selftest : Bool :=
  SHA256.fipsVectorsPass && HMACSHA256.vectorsPass &&
    let seed := Bytes.zero 32
    HMACSHA256.hash seed "abc".toUTF8 !=
      TestLabelOracle.pad seed ⟨0, by decide⟩ false 0

abbrev Profile := BN254.bn254
abbrev Input := AffineInput Profile
abbrev Hidden := HiddenInput Profile
abbrev Output := BN254.CanonicalOutput

def parseBounded (name : String) (bound : Nat) (value : String) :
    Except String (Fin bound) := do
  let parsed ← parseNat name value
  if h : parsed < bound then pure ⟨parsed, h⟩
  else throw (name ++ " must be below " ++ toString bound)

def parseCoordinates (name value : String) :
    Except String (CanonicalFq × CanonicalFq) :=
  match value.splitOn "," with
  | [xText, yText] => do
      let x ← parseBounded (name ++ ".x") baseFieldModulus xText
      let y ← parseBounded (name ++ ".y") baseFieldModulus yText
      pure (x, y)
  | _ => .error (name ++ " must be encoded as x,y")

def parseInput (value : String) : Except String Input := do
  let (x, y) ← parseCoordinates "a" value
  if hcurve : ((y.val : BN254.Fq) ^ 2 = (x.val : BN254.Fq) ^ 3 + 3) then
    pure ⟨x, y, hcurve⟩
  else
    throw "a is not a valid BN254 G1 affine point"

def parseOutput (value : String) : Except String Output :=
  if value = "infinity" then .ok .infinity
  else do
    let (x, y) ← parseCoordinates "q" value
    if hcurve : ((y.val : BN254.Fq) ^ 2 = (x.val : BN254.Fq) ^ 3 + 3) then
      pure (.affine x y hcurve)
    else
      throw "q is not a valid BN254 G1 affine point"

def parseHidden (qText rText : String) : Except String Hidden := do
  let Q ← parseOutput qText
  let r ← parseBounded "r" scalarFieldModulus rText
  pure ⟨Q, r⟩

def outputEq : Output → Output → Bool
  | .infinity, .infinity => true
  | .affine x y _, .affine x' y' _ =>
      x.val == x'.val && y.val == y'.val
  | _, _ => false

def expectedOutput (hidden : Hidden) (input : Input) : Output :=
  BN254.CanonicalOutput.ofPoint
    (GarblingPrize.Protected.reference Profile hidden input)

def concreteOutput (output : Profile.Output) : Output := output

def outputSummary : Output → String
  | .infinity => "infinity"
  | .affine x y _ => toString x.val ++ "," ++ toString y.val

def resultSummary : Except EvalError Profile.Output → String
  | .ok output => "ok:" ++ outputSummary (concreteOutput output)
  | .error .malformedArtifact => "error:malformedArtifact"
  | .error .invalidLabels => "error:invalidLabels"
  | .error .internalFailure => "error:internalFailure"

structure CaseMeasurement where
  correct : Bool
  artifactBytes : Nat
  garbleMilliseconds : Nat
  evaluateMilliseconds : Nat

def measureCase (scheme : Scheme Profile)
    (randomnessSeed labelSeed : MasterSeed)
    (hidden : Hidden) (input : Input) :
    IO CaseMeasurement := do
  let pairs := TestLabelOracle.labelPairs labelSeed
  let garbleStart ← IO.monoMsNow
  let artifact := scheme.garbleWithSeedAndLabelPairs randomnessSeed hidden pairs
  -- The native digest plus observable checkpoint force every serialized byte
  -- before the timestamp; pure Lean computations may otherwise be floated
  -- across adjacent clock reads.
  let artifactBytes := artifact.size
  IO.eprintln ("garble-ready:" ++ toString artifactBytes ++ ":" ++
    bytesHex (SHA256.hash artifact))
  let garbleEnd ← IO.monoMsNow
  let evaluateStart ← IO.monoMsNow
  let result := scheme.evaluateWithLabels artifact input
    (activeLabels pairs input)
  -- The observable summary forces the complete canonical evaluator result.
  -- The independent reference computation below is verifier overhead, not
  -- candidate time.
  IO.eprintln ("evaluate-ready:" ++ resultSummary result)
  let evaluateEnd ← IO.monoMsNow
  let expected := expectedOutput hidden input
  let correct := match result with
    | .ok output => outputEq (concreteOutput output) expected
    | .error _ => false
  pure {
    correct
    artifactBytes
    garbleMilliseconds := garbleEnd - garbleStart
    evaluateMilliseconds := evaluateEnd - evaluateStart }

def measurementJson (measurement : CaseMeasurement) : String :=
  "{\"correct\":" ++ (if measurement.correct then "true" else "false") ++
    ",\"artifactBytes\":" ++ toString measurement.artifactBytes ++
    ",\"garbleMilliseconds\":" ++ toString measurement.garbleMilliseconds ++
    ",\"evaluateMilliseconds\":" ++
      toString measurement.evaluateMilliseconds ++
    ",\"peakMemoryBytes\":null," ++
    "\"peakMemoryMeasurement\":\"external-verifier\"}"

def runCase (scheme : Scheme Profile) : List String → IO UInt32
  | ["--randomness-seed", randomnessSeedText,
      "--label-seed", labelSeedText,
      "--q", qText, "--r", rText, "--a", aText] =>
      match requireSeed randomnessSeedText, requireSeed labelSeedText,
          parseHidden qText rText, parseInput aText with
      | .ok randomnessSeed, .ok labelSeed, .ok hidden, .ok input => do
          let measurement ← measureCase scheme randomnessSeed labelSeed hidden input
          IO.println (measurementJson measurement)
          pure (if measurement.correct then 0 else 1)
      | .error message, _, _, _ | _, .error message, _, _ |
          _, _, .error message, _ | _, _, _, .error message =>
          IO.eprintln message *> pure 2
  | _ => IO.eprintln usage *> pure 2

def benchmarkRandomnessSeed (index : Nat) : MasterSeed :=
  SHA256.hash ("internal".toUTF8 ++ (Codec.natLE 32 index).toByteArray)

def benchmarkLabelSeed (index : Nat) : MasterSeed :=
  SHA256.hash ("labels".toUTF8 ++ (Codec.natLE 32 index).toByteArray)

def generatorInput : Input :=
  ⟨⟨1, by norm_num [baseFieldModulus]⟩,
    ⟨2, by norm_num [baseFieldModulus]⟩, by
      change BN254.OnCurve _ _
      norm_num [BN254.OnCurve]⟩

def benchmarkHidden (index : Nat) : Hidden :=
  { Q := if index % 2 = 0 then .infinity else
      .affine ⟨1, by norm_num [baseFieldModulus]⟩
        ⟨2, by norm_num [baseFieldModulus]⟩ (by norm_num [BN254.OnCurve])
    r := ⟨index % scalarFieldModulus, Nat.mod_lt _ (by
      norm_num [scalarFieldModulus])⟩ }

structure BenchmarkTotals where
  correct : Bool := true
  artifactMin : Option Nat := none
  artifactMax : Nat := 0
  artifactTotal : Nat := 0
  garbleTotal : Nat := 0
  evaluateTotal : Nat := 0

def BenchmarkTotals.record (totals : BenchmarkTotals)
    (measurement : CaseMeasurement) : BenchmarkTotals :=
  { totals with
    artifactMin := some <| match totals.artifactMin with
      | none => measurement.artifactBytes
      | some current => min current measurement.artifactBytes
    artifactMax := max totals.artifactMax measurement.artifactBytes
    artifactTotal := totals.artifactTotal + measurement.artifactBytes
    garbleTotal := totals.garbleTotal + measurement.garbleMilliseconds
    evaluateTotal := totals.evaluateTotal + measurement.evaluateMilliseconds }

def benchmarkLoop (scheme : Scheme Profile) (claimedBytes : Nat) :
    Nat → Nat → BenchmarkTotals → IO BenchmarkTotals
  | 0, _, totals => pure totals
  | remaining + 1, index, totals => do
      let measurement ← measureCase scheme (benchmarkRandomnessSeed index)
        (benchmarkLabelSeed index) (benchmarkHidden index) generatorInput
      let updated := totals.record measurement
      if measurement.correct && decide (measurement.artifactBytes ≤ claimedBytes)
      then
        benchmarkLoop scheme claimedBytes remaining (index + 1) updated
      else
        pure { updated with correct := false }

def runBenchmark (scheme : Scheme Profile) (claimedBytes : Nat) :
    List String → IO UInt32
  | ["--cases", countText] =>
      match parseNat "cases" countText with
      | .error message => IO.eprintln message *> pure 2
      | .ok 0 => IO.eprintln "cases must be positive" *> pure 2
      | .ok count => do
          let totals ← benchmarkLoop scheme claimedBytes
            count 0 {}
          let artifactMin := totals.artifactMin.getD 0
          IO.println ("{\"correct\":" ++
            (if totals.correct then "true" else "false") ++
            ",\"cases\":" ++ toString count ++
            ",\"claimedBytes\":" ++ toString claimedBytes ++
            ",\"artifactBytesMin\":" ++ toString artifactMin ++
            ",\"artifactBytesMax\":" ++ toString totals.artifactMax ++
            ",\"artifactBytesTotal\":" ++ toString totals.artifactTotal ++
            ",\"garbleMillisecondsTotal\":" ++ toString totals.garbleTotal ++
            ",\"evaluateMillisecondsTotal\":" ++
              toString totals.evaluateTotal ++
            ",\"peakMemoryBytes\":null," ++
            "\"peakMemoryMeasurement\":\"external-verifier\"}")
          pure (if totals.correct then 0 else 1)
  | _ => IO.eprintln usage *> pure 2

def main (scheme : Scheme Profile) (claimedBytes : Nat)
    (args : List String) : IO UInt32 := do
  match args with
  | ["selftest"] =>
      if selftest then
        IO.println "SELFTEST PASS" *> pure 0
      else
        IO.eprintln "SELFTEST FAIL" *> pure 1
  | "pad" :: rest =>
      match runPad rest with
      | .ok pad => IO.println (bytesHex pad) *> pure 0
      | .error message => IO.eprintln message *> pure 2
  | "sample" :: rest =>
      match runSample rest with
      | .ok value => IO.println (toString value) *> pure 0
      | .error message => IO.eprintln message *> pure 2
  | "run-case" :: rest => runCase scheme rest
  | "benchmark" :: rest => runBenchmark scheme claimedBytes rest
  | _ => IO.eprintln usage *> pure 2

end GarblingPrize.Protected.Runner
