import SecretRelease
import VCVio.Interaction.UC.Computational
import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
import VCVio.CryptoFoundations.Asymptotics.ReductionCost

/-!
Optional infrastructure for authoring simulation-based proof profiles.

VCVio supplies `Interaction.UC.ObservedCompUCSecure`, real/ideal emulation and
composition, `OracleComp.Complexity.StrictPPTWitness` / `PureCertificate`, and
`SecurityGame.ReductionWithCost`. Use these upstream definitions directly.

This import does not strengthen `SecretRelease.Certified`: its ROM experiments
and equal-leakage privacy remain unchanged. A new challenge must fix the ideal
functionality, allowed leakage, execution semantics, and a reviewed quantitative
backend, and connect its scheme to those games. In particular, a query bound
alone does not bound pure local computation. A simulator's efficiency and its
real/ideal theorem are separate obligations; neither follows from this import.
-/
