import WotsLamport.Submission.Sharing
import WotsLamport.Submission.Shamir
import WotsLamport.Submission.Layout
import WotsLamport.Submission.Geometry
import WotsLamport.Submission.InverseBridge
import WotsLamport.Submission.FieldBridge
import WotsLamport.Submission.Exposed

namespace WotsLamport.Submission
open WotsLamport.Protected

/-- Research candidate only. No certificate, score or security theorem. -/
def submission : Option Entry := some ⟨construction, artifactBytes, none⟩
def entry : Option (SecretRelease.Candidate challenge) := submission.map Entry.candidate

end WotsLamport.Submission
