# Security Policy

## Project status

This repository contains experimental research software. It is not production
ready, has not been independently audited, and may contain defects in its
proofs, specifications, native code, executable boundary, or documentation.
Interfaces, artifact formats, assumptions, and implementation details may
change without notice.

The presence of machine-checked Lean proofs does not establish end-to-end
security. The proofs cover only the properties and idealized assumptions stated
by the protected challenge contract. In particular, they do not prove the
security of SHA-256 or HMAC, seed generation or handling, side-channel
resistance, the native C implementation, external label derivation,
multi-artifact composition, or integration into BABE or another protocol.

Do not use this software to protect funds, production secrets, or other
high-value assets without an independent security review.

## Supported versions

There are currently no stable or long-term-supported releases. Security fixes
are made on a best-effort basis against the default branch and may include
breaking changes. Older commits and generated artifacts should be considered
unsupported.

## Reporting a vulnerability

Do not report a suspected vulnerability in a public issue, discussion, pull
request, or social-media post.

Use GitHub's private vulnerability-reporting form:

<https://github.com/solving-bitcoin/lean-autoresearch/security/advisories/new>

If that form is unavailable, open a public issue that contains **no security
details** and asks the maintainers to provide a private disclosure channel.
Wait for that channel before sharing technical information.

Please include, where applicable:

- the affected commit or version;
- the affected component and threat model;
- the security impact;
- minimal reproduction steps or a proof of concept using synthetic data;
- any known mitigations; and
- your intended disclosure timeline.

Do not include real private keys, production seeds, credentials, or other
sensitive data in a report. The maintainers will coordinate disclosure and a
fix on a best-effort basis. This project does not currently offer a bug bounty
or guarantee a response or remediation deadline.

Ordinary correctness bugs that have no security impact may be reported through
the public issue tracker.
