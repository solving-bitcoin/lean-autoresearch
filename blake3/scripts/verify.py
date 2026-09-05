"""Isolated Lean certificate + guarded real label-to-label artifact measurement."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

from resources import ROOT,guarded
from policy import check_protected,check_source,dependencies
from render_benchmark_challenge import parse_score


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--submission',type=Path,default=ROOT/'Blake3Prize/Submission')
    args=parser.parse_args()
    check_protected();check_source(args.submission);dependencies()
    score=parse_score(args.submission/'score.txt')
    r=guarded([sys.executable,ROOT/'scripts/check_policy.py'],native=True)
    print(r['stdout'],end='',flush=True)
    with tempfile.TemporaryDirectory(prefix='blake3-certified-') as temporary:
        project=Path(temporary)
        for name in ('lakefile.lean','lake-manifest.json','lean-toolchain','Blake3Prize.lean'):
            shutil.copy2(ROOT/name,project/name)
        shutil.copytree(ROOT/'Blake3Prize/Protected',project/'Blake3Prize/Protected')
        shutil.copy2(ROOT/'Blake3Prize/Main.lean',project/'Blake3Prize/Main.lean')
        shutil.copytree(args.submission,project/'Blake3Prize/Submission')
        (project/'.lake').mkdir()
        (project/'.lake/packages').symlink_to(ROOT/'.lake/packages',target_is_directory=True)
        measurements=[]
        # Build the protected bridge first, before importing the submission.
        for target in ('blake3-trusted','blake3-circuit'):
            r=guarded(['lake','build',target],project)
            measurements.append(r['peakMemoryBytes'])
            print(f"PASS: build {target}; peak {r['peakMemoryBytes']} bytes",flush=True)
        shutil.copy2(ROOT/'scripts/Audit.lean',project/'Audit.lean')
        r=guarded(['lake','env','lean','-j1','Audit.lean'],project)
        print(r['stdout'],end='',flush=True);measurements.append(r['peakMemoryBytes'])
        r=guarded([project/'.lake/build/bin/blake3-trusted'],project,native=True)
        reference_peak=r['peakMemoryBytes']
        clean_path=project/'clean-checks.json'
        clean_path.write_text(r['stdout'])
        r=guarded([project/'.lake/build/bin/blake3-circuit'],project,native=True)
        export_peak=r['peakMemoryBytes']
        circuit=json.loads(r['stdout'])
        if circuit['claimedBytes']!=score:
            raise SystemExit('score.txt differs from the checked submission byte claim')
        circuit_path=project/'circuit.json'
        circuit_path.write_text(json.dumps(circuit))
        r=guarded([sys.executable,ROOT/'scripts/check_runtime.py',circuit_path,
                   '--clean-checks',clean_path,
                   '--result',project/'result.json'],project,native=True)
        print(r['stdout'],end='',flush=True)
        report=json.loads((project/'result.json').read_text())
        report['compilerPeakMemoryBytes']=max(measurements)
        report['exportPeakMemoryBytes']=export_peak
        report['referencePeakMemoryBytes']=reference_peak
        report['runtimePeakMemoryBytes']=r['peakMemoryBytes']
        report['nativePeakMemoryBytes']=max(export_peak,reference_peak,r['peakMemoryBytes'])
        report['score']=score
        report['direction']='minimize'
        report['unit']='bytes'
        report['metric']='universal_artifact_byte_bound_under_protected_backend'
        report['submissionDigest']=hashlib.sha256(b''.join(
            p.name.encode()+b'\0'+p.read_bytes()+b'\0'
            for p in sorted(args.submission.iterdir()))).hexdigest()
        dependencies()
        output=ROOT/'.yukon/blake3-64-labeled-hash-score.json'
        output.parent.mkdir(exist_ok=True)
        output.write_text(json.dumps(report,indent=2)+'\n')
        print(f'ACCEPTED: {score} artifact bytes; score file {output}',flush=True)

if __name__=='__main__':main()
