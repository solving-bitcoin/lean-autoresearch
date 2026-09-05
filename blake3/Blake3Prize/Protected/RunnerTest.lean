import Blake3Prize.Protected.Runner

namespace Blake3Prize.Protected.RunnerTest

private def labelAt (bytes : ByteArray) (index : Nat) : Label :=
  Vector.ofFn fun j => bytes[index*32+j.val]!

/-- Deliberately INSECURE protocol fixture: all pairs are serialized. This
checks that native correctness tests do not masquerade as a secrecy proof.
It has no ValidCandidate certificate and is never eligible for ranking. Its
custom header and coin bytes exercise complete, submission-owned framing. -/
def fixture : Scheme where
  Artifact := ByteArray
  randomnessBytes := 7
  garble := fun _ coins inputs outputs =>
    let pairs := (List.finRange 768).toArray.flatMap fun i =>
      let pair := if h : i.val < 512 then inputs ⟨i.val,h⟩
                  else outputs ⟨i.val-512,by omega⟩
      (pair false).toArray ++ (pair true).toArray
    ⟨pairs ++ coins.toArray⟩
  encode := fun a => ByteArray.append ⟨#[76,69,65]⟩ a
  decode := fun bytes =>
    if bytes.size ≥ 3 && bytes[0]! == 76 && bytes[1]! == 69 && bytes[2]! == 65
    then some (bytes.extract 3 bytes.size) else none
  evaluate := fun _ bytes input active => do
    if bytes.size != 49159 then none else do
      if !(List.finRange 512).all (fun i =>
          active[i] == labelAt bytes (2*i.val + if inputBit input i then 1 else 0))
        then none else do
        let pairs : OutputLabelPairs := fun i b => labelAt bytes (2*(512+i.val)+if b then 1 else 0)
        some (activeOutput pairs (reference input))

end Blake3Prize.Protected.RunnerTest

def main (args : List String) : IO UInt32 := do
  if args = ["describe"] then
    IO.println "{\"status\":\"insecure-test-fixture\",\"claimedBytes\":49162,\"randomnessBytes\":7}"
    return 0
  Blake3Prize.Protected.Runner.runScheme Blake3Prize.Protected.RunnerTest.fixture 49162 args
