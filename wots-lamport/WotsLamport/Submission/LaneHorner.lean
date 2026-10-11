import WotsLamport.Submission.LaneImplementation
import WotsLamport.Submission.MachineHorner
import Mathlib.Tactic.IntervalCases

namespace WotsLamport.Submission

theorem HornerLanes.get_ofFn (f : Fin 16 → UInt32) (i : Fin 16) :
    (HornerLanes.ofFn f).get i = f i := by
  rcases i with ⟨i,hi⟩
  interval_cases i <;> rfl

theorem lanesHorner_correspondence (rows : List HornerLanes) (x : UInt32)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : UInt32) (i : Fin 16) :
    (lanesHorner x rows s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15).get i =
      machineHorner (rows.map fun row => row.get i) x
        ((⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩ : HornerLanes).get i) := by
  induction rows generalizing s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 with
  | nil => rfl
  | cons row rest ih =>
    simp only [lanesHorner, ih, List.map_cons, machineHorner]
    apply congrArg (machineHorner (rest.map fun row => row.get i) x)
    rcases i with ⟨i,hi⟩
    interval_cases i <;> rfl


end WotsLamport.Submission
