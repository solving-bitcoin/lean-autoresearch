import SecretRelease

namespace Blake3Prize.Submission.RomViewEquality
open SecretRelease

theorem ext {c : Challenge} {a b : View c}
    (input : a.input = b.input) (artifact : a.artifact = b.artifact)
    (inputs : a.activeInputs = b.activeInputs) (outputs : a.activeOutputs = b.activeOutputs) :
    a = b := by
  cases a
  cases b
  cases input
  cases artifact
  cases inputs
  cases outputs
  rfl

end Blake3Prize.Submission.RomViewEquality
