import G1Release.Protected.Target

open SecretRelease G1Release.Protected

-- Keep the challenge's public choices explicit and kernel-checked.
example : challenge.inputCodec.width = 512 := rfl
example : challenge.privateCodec.width = 776 := rfl
example : challenge.inputs.Keys = (Fin 512 → SecretRelease.Pair) := rfl
example : challenge.outputs.Keys = Unit := rfl
example : challenge.correctness = .exact := rfl
example : challenge.withholding = none := rfl
example : challenge.rom.maxQueries = 2^64 := rfl
example (q : Nat) : challenge.rom.error q = (q+1 : ℚ≥0) / 2^128 := rfl
example (p : Private) (a : Input) :
    challenge.privateLeakage = some (fun p a => encodeOutput (reference p a)) := rfl
example (h : SecretRelease.Hash) (p : Private) (a : Input)
    (keys : Fin 512 → SecretRelease.Pair) (i : Fin 512) (label : SecretRelease.Label) :
    challenge.wins h p a keys () (i,label) ↔
      label = (keys i).get (!(inputCodec.encode a)[i.val]) := Iff.rfl
