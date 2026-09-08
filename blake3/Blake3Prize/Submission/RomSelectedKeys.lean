import Blake3Prize.Submission.RomMixedGuessing

namespace Blake3Prize.Submission.RomSelectedKeys
open SecretRelease RomMixedKeys RomMixedGuessing

/-- Selecting keys commutes with the exact active/hidden split. Keeping this
fact polymorphic prevents kernel reduction of a concrete circuit trace. -/
theorem selected_key (external : Fin e → Bool) (internal : Fin k → Bool)
    (keys : Keys e k) (i : Index e k) :
    activeLabel (split external internal keys).1 i = key keys i (bit external internal i) := by
  cases i <;> rfl

end Blake3Prize.Submission.RomSelectedKeys
