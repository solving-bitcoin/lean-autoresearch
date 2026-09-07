"""Opt-in framework integration checks, separate from challenge acceptance."""
import argparse
import importlib
from pathlib import Path
import sys

repo=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('project',choices=('blake3','g1-release'))
args=parser.parse_args()
sys.path.insert(0,str(repo/args.project/'scripts'))
boundary=importlib.import_module('policy' if args.project=='blake3' else 'boundary')
from resources import guarded

boundary.check_protected(); boundary.dependencies()
for module, audit in [('Examples','ExamplesAudit.lean'),('Simulation','SimulationAudit.lean')]:
    for command in (['lake','build','SecretRelease.'+module],
                    ['lake','env','lean','-j1',repo/'secret-release/SecretReleaseTests'/audit]):
        result=guarded(command,repo/args.project)
        print(result['stdout'],end='',flush=True)
boundary.dependencies(snapshot=True)
