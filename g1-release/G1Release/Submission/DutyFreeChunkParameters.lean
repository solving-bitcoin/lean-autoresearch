import G1Release.Submission.DutyFreeBridge

/-! A direct-field duty-free layout. The one-hot bridge is shared by every
affine opening of the same coordinate. Each opening stores 64 plain joins
and a single final decoding field element; no per-bit field table remains. -/
namespace G1Release.Submission.DutyFreeChunkParameters

def chunks : Nat := 64
def fields : Nat := 91*8
def inputBytes : Nat := 2*chunks*DutyFreeBridge.byteCount
def outputBytes : Nat := (chunks+1)*fields*32
def plannedBytes : Nat := inputBytes+outputBytes

theorem plannedBytes_value : plannedBytes = 1776384 := by decide
theorem plannedBytes_lt_old : plannedBytes < 5940480 := by decide

end G1Release.Submission.DutyFreeChunkParameters
