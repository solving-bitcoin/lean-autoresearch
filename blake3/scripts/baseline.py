"""Optional half-gates demonstration, never a scheme-level accepted score."""
import json
from pathlib import Path
import sys
import tempfile
from resources import ROOT,guarded
from policy import check_protected,dependencies

check_protected();dependencies()
peaks=[]
for target in ('blake3-half-gates-checks','blake3-half-gates'):
    r=guarded(['lake','build',target]);peaks.append(r['peakMemoryBytes'])
    print(f"PASS: optional baseline build {target}; peak {r['peakMemoryBytes']} bytes",flush=True)
dependencies(snapshot=True)
r=guarded(['lake','env','lean','-j1',ROOT/'scripts/BaselineAudit.lean'])
print(r['stdout'],end='',flush=True)
with tempfile.TemporaryDirectory(prefix='blake3-half-gates-') as directory:
    directory=Path(directory)
    for executable,name in (('blake3-half-gates','circuit.json'),('blake3-half-gates-checks','checks.json')):
        r=guarded([ROOT/'.lake/build/bin'/executable],native=True)
        (directory/name).write_text(r['stdout'])
    r=guarded([sys.executable,ROOT/'examples/half_gates/check_runtime.py',directory/'circuit.json',
               '--clean-checks',directory/'checks.json','--result',directory/'result.json'],native=True)
    print(r['stdout'],end='',flush=True)
    report=json.loads((directory/'result.json').read_text())
    report.update(status='uncertified-baseline',score=None,compilerPeakMemoryBytes=max(peaks),
                  runtimePeakMemoryBytes=r['peakMemoryBytes'],
                  protectedDigest=(ROOT/'protected.sha256').read_text().strip())
    (ROOT/'.yukon/half-gates-baseline.json').write_text(json.dumps(report,indent=2)+'\n')
dependencies()
print(f'BASELINE ONLY: {report["artifactBytes"]} bytes; end-to-end secrecy certificate absent',flush=True)
