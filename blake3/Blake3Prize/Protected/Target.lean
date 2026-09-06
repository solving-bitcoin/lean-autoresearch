import Blake3Prize.Protected.Challenge

namespace Blake3Prize.Protected
abbrev Scheme := SecretRelease.Scheme challenge
abbrev CertifiedScheme := SecretRelease.Certified challenge
abbrev Candidate := SecretRelease.Candidate challenge
-- No gates, native hash implementation, or legacy predicate is imported here.
end Blake3Prize.Protected
