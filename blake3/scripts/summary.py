"""Report certification separately from optional implementation measurements."""
import json
from pathlib import Path
import sys

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'.yukon/blake3-64-labeled-hash-score.json').read_text())
if r['status']=='authoring-preview':
    status=('**Authoring preview only — no accepted score.** This run checks PR-owned '
            'challenge changes; it cannot establish submission acceptance.\n')
elif r['status']=='accepted':
    status=(f"**Accepted universal artifact bound: {r['score']:,} bytes**\n\n"
            f"Measured artifact: {r['artifactBytes']:,} bytes. "
            f"Profile: `{r['securityProfile']}`.\n")
else:
    status='**No ranked submission.** The neutral contract and runner checks passed; the complete scheme-level certificate is still required.\n'
text=f'''## BLAKE3 conditional release

{status}
Known 64-byte message · 512 active input labels → 256 active output labels · 32-byte labels.
The common game protects all **768 opposite input/output labels**.

The initial ClassicalBoundedQueryROM profile requires, for every `q ≤ 2^64`,
`Pr[recover any opposite label] ≤ (q+1)/2^128`.
The SHA-256 instantiation of the ideal oracle remains **heuristic / unproved**.

The submission owns its construction, evaluator, artifact type, and codec.
Every instance-dependent public artifact byte is counted. The fixed active-label
traffic is 24,576 bytes; the already-known message adds 64 bytes to total API I/O.

Clean reference cases: {r['cleanReferenceCases']}; SHA-256 implementation cases: {r['nativeHashCases']};
generic runner/custom framing cases: {r['runnerSelfTestCases']}.
Exact certificate-type, axiom-closure, and missing-secrecy rejection checks passed.

Build peak RSS: {r['compilerPeakMemoryBytes']/2**20:.1f} MiB (cap 4096 MiB).
Native check peak RSS: {r['nativePeakMemoryBytes']/2**20:.1f} MiB (cap 1024 MiB).
'''
p=root/'.yukon/half-gates-baseline.json'
if p.exists():
    baseline=json.loads(p.read_text())
    if baseline.get('protectedDigest')==r['protectedDigest']:
        text+=f'''
### Optional half-gates baseline — uncertified

**{baseline['artifactBytes']:,} measured artifact bytes**
(`49,696 + 64 × {baseline['andGates']:,}`; {baseline['xorGates']:,} XOR gates).
This example's expression proofs and local gate identity do **not** constitute
the required complete serialized-correctness and secrecy certificate. Its size
is not an accepted score under the neutral challenge.
'''
with Path(sys.argv[1]).open('a') as stream:stream.write(text)
