"""Author evidence for the exact exported reference bundle, after verification.

This is not a construction-neutral admission rule. It never rebuilds Lean or
replaces the certified entry, and uses the existing build/native guards.
"""
import hashlib
import json
import os
from pathlib import Path
import time
from limits import ROOT, REPO, guarded


def check(bundle, report, run=guarded):
    bundle, report = Path(bundle).resolve(), Path(report).resolve()
    report.unlink(missing_ok=True)
    metadata = json.loads((bundle/'bundle.json').read_text())
    assert metadata['acceptance'] == 'authoring-preview'
    assert metadata['status'] == 'certified' and metadata['certifiedBytes'] == 48752768
    def hashes():
        result = {}
        for name, expected in metadata['tools'].items():
            with (bundle/name).open('rb') as stream:
                result[name] = hashlib.file_digest(stream, 'sha256').hexdigest()
            assert result[name] == expected['sha256']
        return result
    before = hashes()
    workspace = REPO/'secret-release/rust'
    build = run(['cargo', 'test', '--no-run', '--locked', '--jobs', '1',
                 '--message-format=json', '-p', 'wots-lamport-tests', '--test', 'reference'], workspace)
    binaries = set()
    for line in build['stdout'].splitlines():
        item = json.loads(line)
        if item.get('reason') == 'compiler-artifact' and item.get('executable') and item.get('profile', {}).get('test'):
            binaries.add(item['executable'])
    assert len(binaries) == 1, 'expected exactly one reference test binary'
    metrics = report.with_suffix('.metrics.jsonl')
    metrics.write_text('')
    env = {'SECRET_RELEASE_BUNDLE': str(bundle), 'SECRET_RELEASE_METRICS_FILE': str(metrics)}
    previous = {key: os.environ.get(key) for key in env}
    try:
        os.environ.update(env)
        start = time.monotonic()
        native = run([next(iter(binaries)), '--ignored', '--exact',
                      'generated_reference_format_correspondence', '--test-threads=1', '--nocapture'],
                     workspace, native=True)
        seconds = time.monotonic()-start
    finally:
        for key, value in previous.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
    print(native['stdout'], end='', flush=True)
    print(native['stderr'], end='', flush=True)
    assert 'test result: ok. 1 passed; 0 failed;' in native['stdout'], 'correspondence test did not run'
    measured = [json.loads(line) for line in metrics.read_text().splitlines()]
    assert len(measured) == 1 and measured[0]['artifactBytes'] == 48752768
    assert hashes() == before, 'exported tools changed during correspondence check'
    evidence = dict(status='passed', scope='author-reference-correspondence',
                    certifiedBytes=metadata['certifiedBytes'], toolsSha256=before,
                    seconds=seconds, rustBuildPeakMemoryBytes=build['peakMemoryBytes'],
                    nativePeakMemoryBytes=native['peakMemoryBytes'], measurements=measured)
    report.write_text(json.dumps(evidence, indent=2)+'\n')
    print('FINAL_BUNDLE_REFERENCE_CORRESPONDENCE:', flush=True)
    print(json.dumps(evidence, indent=2), flush=True)
    return evidence


if __name__ == '__main__':
    check(ROOT/'.yukon/bundle', ROOT/'.yukon/wots-lamport-correspondence-score.json')
