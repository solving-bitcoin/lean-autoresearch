"""Available source/Python/Rust checks, with the normal sequential guards.

Deliberately does not report a Lean/pipeline/security pass. Generated-tool tests
are skipped ONLY in this local compiler-unavailable check, never by benchmark.
"""
import argparse
import json
from pathlib import Path
import sys
from limits import guarded, ROOT, REPO

def run(command,cwd=ROOT,native=True,echo_stdout=True):
    result=guarded(command,cwd,native=native)
    if echo_stdout: print(result['stdout'],end='',flush=True)
    print(result['stderr'],end='',flush=True)
    print('Peak RSS:',result['peakMemoryBytes'],flush=True)
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--full-reference',action='store_true')
    args=parser.parse_args()
    for script in ['check_model.py','check_vectors.py','check_security_arithmetic.py','check_boundary.py',
                   'check_bitcoin_cost.py']:
        run([sys.executable,ROOT/'scripts'/script])
    run([sys.executable,REPO/'scripts/check_cache_trust.py'])
    workspace=REPO/'secret-release/rust'
    result=run(['cargo','test','--no-run','--locked','--jobs','1','--message-format=json','-p','wots-lamport-tests'],workspace,native=False,echo_stdout=False)
    binaries=[]
    for line in result['stdout'].splitlines():
        item=json.loads(line)
        if item.get('reason')=='compiler-artifact' and item.get('executable') and item.get('profile',{}).get('test'):
            binaries.append(item['executable'])
    assert binaries
    for executable in sorted(set(binaries)):
        run([executable,'--test-threads=1','--nocapture','--skip','generated_lean_tools_when_bundle_is_supplied'],workspace)
        if args.full_reference:
            run([executable,'--test-threads=1','--nocapture','--ignored','full_fixed_artifact_multiple_later_messages'],workspace)
    print('NOT CHECKED: Lean elaboration/kernel proofs, generated-tool correspondence, ROM security, actual Bitcoin Script execution')

if __name__=='__main__': main()
