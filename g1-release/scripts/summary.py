import json
from pathlib import Path
import sys
root=Path(__file__).resolve().parents[1]
r=json.loads((root/'.yukon/g1-release-score.json').read_text())
score=r['score']
text=(f"### Q + [r]A shared-contract challenge\n\n"
      f"Status: **{r['status']}**. "
      + (f"Certified universal artifact bound: **{score:,} bytes**.\n\n" if score is not None
         else "No accepted size.\n\n")
      + "Private Q and r; 512 Lamport input bits; canonical plaintext BN254 output.\n\n"
      + f"Build peak: {r['compilerPeakMemoryBytes']:,} bytes; native peak: {r['nativePeakMemoryBytes']:,} bytes.\n\n"
      + "SHA-256 is a heuristic instantiation of the ideal oracle. The old ideal-pad score is not a certificate here.\n")
with Path(sys.argv[1]).open('a') as f:f.write(text)
