"""Publish the measured artifact breakdown, rather than a gate-count estimate."""
import json
from pathlib import Path
import sys

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'.yukon/blake3-64-labeled-hash-score.json').read_text())
text=f'''## BLAKE3 64-byte labeled hash

**{r['artifactBytes']:,} artifact bytes** · 512 input bits → 256 output bits · 32-byte labels

| Component | Bytes |
| --- | ---: |
| Constant label | {r['constantLabelBytes']:,} |
| Input adapters | {r['inputAdapterBytes']:,} |
| {r['andGates']:,} AND gates | {r['andTableBytes']:,} |
| Output adapters | {r['outputAdapterBytes']:,} |
| **Scored artifact** | **{r['artifactBytes']:,}** |
| Fixed active input/output label traffic | 24,576 |
| Total artifact and active-label traffic | {r['totalTransferredBytes']:,} |

Reference: `{r['referenceModule']}` (MIT, Clean `{r['cleanRevision'][:7]}`).
Direct Clean reference cases: {r['cleanReferenceCases']}; word-lowering cases: {r['wordLoweringCases']}.

Lean semantic certificate and axiom audit passed. Native output labels matched
BLAKE3; isolated evaluation and malformed-framing checks passed.

Build peak RSS: {r['compilerPeakMemoryBytes']/2**20:.1f} MiB (cap 4096 MiB).
Native export/test peak RSS: {r['nativePeakMemoryBytes']/2**20:.1f} MiB (cap 1024 MiB).

This circuit track assumes the protected half-gates backend and hash model;
it does not claim a Lean proof of native cryptographic security.
'''
with Path(sys.argv[1]).open('a') as stream:stream.write(text)
