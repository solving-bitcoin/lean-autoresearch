import WotsLamport.Submission.ChainTape
import WotsLamport.Submission.CachedSharing
import WotsLamport.Submission.ChainCollisionLaw
import WotsLamport.Submission.ChainProgrammingLaw
import WotsLamport.Submission.ChainPartitionLaw
import WotsLamport.Submission.DomainInjectivity
import WotsLamport.Submission.JointOracleTrace
import WotsLamport.Submission.LabelGuessing
import WotsLamport.Submission.MaskLaw
import WotsLamport.Submission.MaskedViewLaw
import WotsLamport.Submission.AdaptiveMaskedView
import WotsLamport.Submission.MachineHorner
import WotsLamport.Submission.MachineFieldReduction
import WotsLamport.Submission.MachineSharing
import WotsLamport.Submission.MultiTargetTrace
import WotsLamport.Submission.QueryTargets
import WotsLamport.Submission.RestrictedOracleProgram
import WotsLamport.Submission.FreshOracleProgramming
import WotsLamport.Submission.OracleOverlay
import WotsLamport.Submission.Sharing
import WotsLamport.Submission.Shamir
import WotsLamport.Submission.Layout
import WotsLamport.Submission.Geometry
import WotsLamport.Submission.InverseBridge
import WotsLamport.Submission.FieldBridge
import WotsLamport.Submission.Exposed
import WotsLamport.Submission.InterpolationBridge
import WotsLamport.Submission.ByteBridge
import WotsLamport.Submission.DecodingBridge
import WotsLamport.Submission.LabelBridge
import WotsLamport.Submission.Expansion
import WotsLamport.Submission.VisiblePrivacy
import WotsLamport.Submission.SamplerLaw
import WotsLamport.Submission.CoefficientIndices
import WotsLamport.Submission.NonceEnvironmentLaw
import WotsLamport.Submission.NonceTableLaw
import WotsLamport.Submission.ActualPolynomialTable
import WotsLamport.Submission.DomainSeparation
import WotsLamport.Submission.GameReductions
import WotsLamport.Submission.GamePrograms
import WotsLamport.Submission.OracleTrace
import WotsLamport.Submission.OracleSupport
import WotsLamport.Submission.JointSampler
import WotsLamport.Submission.FieldTableLaw
import WotsLamport.Submission.PolynomialLaw
import WotsLamport.Submission.PolynomialEncoding
import WotsLamport.Submission.SamplerMixture

namespace WotsLamport.Submission
open WotsLamport.Protected

/-- Research candidate only. No certificate, score or security theorem. -/
def submission : Option Entry := some ⟨construction, artifactBytes, none⟩
def entry : Option (SecretRelease.Candidate challenge) := submission.map Entry.candidate

end WotsLamport.Submission
