"""WOTS supplies protected configuration to the shared verifier."""
import importlib.util
import json
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
    reports = [('AUTHOR_SOURCE_DIAGNOSTICS', boundary.ROOT/'.yukon/author-sources.json'),
               ('RUNTIME_PROGRESS', boundary.ROOT/'.yukon/runtime-progress.json')]
    (boundary.ROOT/'.yukon/runtime-probe.json').unlink(missing_ok=True)
    correspondence = boundary.ROOT/'.yukon/wots-lamport-correspondence-score.json'
    correspondence.unlink(missing_ok=True)
    for _, report in reports:
        report.unlink(missing_ok=True)
    try:
        module.verify(boundary,guarded)
        # The default author preview is this repository's reference entry.
        # Keep all shared admission checks and their order unchanged. Only
        # after they pass, compare the exact exported certified executable;
        # never impose this format-specific test on --submission candidates.
        if sys.argv[1:] == ['--authoring-preview']:
            from check_bundle_correspondence import check
            print('FINAL_CERTIFIED_REPORT:', flush=True)
            print(json.dumps(json.loads((boundary.ROOT/'.yukon/wots-lamport-score.json').read_text()), indent=2), flush=True)
            check(boundary.ROOT/'.yukon/bundle', correspondence)
    finally:
        if '--authoring-preview' in sys.argv:
            for title, report in reports:
                if not report.is_file():
                    continue
                with report.open() as stream:
                    evidence = stream.read(1024*1024+1)
                if len(evidence) <= 1024*1024:
                    print(title+' (not acceptance):', flush=True)
                    print(evidence, flush=True)
                else:
                    print(title+': oversized diagnostic file omitted', flush=True)

if __name__=='__main__': main()
