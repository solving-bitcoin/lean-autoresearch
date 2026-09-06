import G1Release.Protected.Target
import G1Release.Protected.NativeHash

open G1Release.Protected

def main (args : List String) : IO UInt32 := do
  match args with
  | ["reference", privatePath, inputPath, outputPath] =>
    let rawPrivate ← IO.FS.readBinFile privatePath
    let rawInput ← IO.FS.readBinFile inputPath
    let some p := (bytesToBits 97 rawPrivate).bind privateCodec.decode
      | throw (IO.userError "invalid private encoding")
    let some a := (bytesToBits 64 rawInput).bind inputCodec.decode
      | throw (IO.userError "invalid finite-affine encoding")
    IO.FS.writeBinFile outputPath (encodeOutput (reference p a))
    return 0
  | ["roundtrip", kind, inputPath, outputPath] =>
    let bytes ← IO.FS.readBinFile inputPath
    let decoded := match kind with
      | "input" => do
        let a ← (bytesToBits 64 bytes).bind inputCodec.decode
        pure (bitsToBytes (n := 64) (inputCodec.encode a))
      | "private" => do
        let p ← (bytesToBits 97 bytes).bind privateCodec.decode
        pure (bitsToBytes (n := 97) (privateCodec.encode p))
      | "output" => do
        let p ← (bytesToBits 65 bytes).bind outputCodec.decode
        pure (encodeOutput p)
      | _ => none
    let some encoded := decoded | throw (IO.userError "invalid canonical encoding")
    IO.FS.writeBinFile outputPath encoded
    return 0
  | ["sha256", inputPath, outputPath] =>
    let bytes ← IO.FS.readBinFile inputPath
    IO.FS.writeBinFile outputPath (sha256 bytes)
    return 0
  | _ => throw (IO.userError "expected reference, roundtrip, or sha256")
