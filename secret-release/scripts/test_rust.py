"""Build with the build cap, then run with the aggregate native cap."""
import argparse
import json
import os
from pathlib import Path
import sys
REPO=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(REPO/'blake3/scripts'))
from resources import guarded


def run_tests(project, bundle):
    package=json.loads((project/'challenge.json').read_text())['rustPackage']
    workspace=REPO/'secret-release/rust'
    r=guarded(['cargo','test','--no-run','--locked','--jobs','1',
               '--message-format=json','-p','secret-release','-p',package],workspace)
    executables=[]
    for line in r['stdout'].splitlines():
        item=json.loads(line)
        if item.get('reason')=='compiler-artifact' and item.get('executable') and item.get('profile',{}).get('test'):
            executables.append(item['executable'])
    if not executables: raise SystemExit('Cargo produced no tests')
    os.environ['SECRET_RELEASE_BUNDLE']=str(bundle.resolve())
    state=workspace/'.yukon';state.mkdir(exist_ok=True)
    metrics=state/'metrics.jsonl';metrics.write_text('')
    os.environ['SECRET_RELEASE_METRICS_FILE']=str(metrics)
    native=[]
    for executable in sorted(set(executables)):
        result=guarded([executable,'--test-threads=1','--nocapture'],workspace,native=True)
        native.append(result['peakMemoryBytes']); print(result['stdout'],end='',flush=True)
    measured=[json.loads(line) for line in metrics.read_text().splitlines()]
    return {'observedArtifactBytes':max((r['artifactBytes'] for r in measured),default=None),
            'pipelineCases':len(measured), 'measurements':measured, 'rustBuildPeakMemoryBytes':r['peakMemoryBytes'],
            'rustNativePeakMemoryBytes':max(native),'rustTestExecutables':len(set(executables))}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('project',type=Path);p.add_argument('bundle',type=Path)
    a=p.parse_args();print(json.dumps(run_tests(a.project.resolve(),a.bundle)))
