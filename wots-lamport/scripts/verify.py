"""WOTS supplies protected configuration to the shared verifier."""
import importlib.util
from pathlib import Path
import sys
import boundary
from limits import guarded
shared=Path(__file__).resolve().parents[2]/'secret-release/scripts'
sys.path.insert(0,str(shared))
spec=importlib.util.spec_from_file_location('secret_release_verifier',shared/'verify.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
def main():
    # Keep source diagnostics even when the unchanged outer guard kills the
    # author process. This file is evidence only, never an acceptance input.
    report = boundary.ROOT/'.yukon/author-sources.json'
    report.unlink(missing_ok=True)
    try:
        module.verify(boundary,guarded)
    finally:
        if '--authoring-preview' in sys.argv and report.is_file():
            with report.open() as stream:
                evidence = stream.read(1024*1024+1)
            if len(evidence) <= 1024*1024:
                print('AUTHOR_SOURCE_DIAGNOSTICS (not acceptance):', flush=True)
                print(evidence, flush=True)
            else:
                print('AUTHOR_SOURCE_DIAGNOSTICS: oversized diagnostic file omitted', flush=True)

if __name__=='__main__': main()
