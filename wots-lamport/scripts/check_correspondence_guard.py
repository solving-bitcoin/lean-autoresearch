"""Failure injection for retained final-bundle correspondence evidence."""
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
from check_bundle_correspondence import check


def main():
    for failure in (None, 'build', 'native', 'no-test', 'wrong-size', 'changed-tool'):
        with tempfile.TemporaryDirectory(prefix='wots-correspondence-') as directory:
            root = Path(directory)
            tool = root/'challenge'; tool.write_bytes(b'fixture executable')
            metadata = dict(acceptance='authoring-preview', status='certified', certifiedBytes=48752768,
                            tools={'challenge': {'sha256': hashlib.sha256(tool.read_bytes()).hexdigest()}})
            (root/'bundle.json').write_text(json.dumps(metadata))
            report = root/'report.json'; report.write_text('stale success')
            previous = {key: os.environ.get(key) for key in ('SECRET_RELEASE_BUNDLE', 'SECRET_RELEASE_METRICS_FILE')}
            calls = []
            def run(command, cwd, **options):
                calls.append(options)
                if len(calls) == 1:
                    assert not options.get('native', False)
                    if failure == 'build':
                        raise SystemExit('injected build failure')
                    stdout = json.dumps(dict(reason='compiler-artifact', executable='/test/reference', profile={'test': True}))
                else:
                    assert options == {'native': True}
                    assert '--exact' in command and 'generated_reference_format_correspondence' in command
                    assert os.environ['SECRET_RELEASE_BUNDLE'] == str(root)
                    if failure == 'native':
                        raise SystemExit('injected native failure')
                    Path(os.environ['SECRET_RELEASE_METRICS_FILE']).write_text(json.dumps({'artifactBytes': 1 if failure == 'wrong-size' else 48752768})+'\n')
                    if failure == 'changed-tool':
                        tool.write_bytes(b'changed')
                    stdout = 'test result: ok. 0 passed; 0 failed;' if failure == 'no-test' else 'test result: ok. 1 passed; 0 failed;'
                return dict(stdout=stdout, stderr='', peakMemoryBytes=1)
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    result = check(root, report, run)
            except (AssertionError, SystemExit):
                assert failure is not None
                assert not report.exists(), 'failed run retained a success report'
            else:
                assert failure is None and result['status'] == 'passed'
                assert json.loads(report.read_text())['measurements'][0]['artifactBytes'] == 48752768
            assert all(os.environ.get(key) == value for key, value in previous.items())
    print('PASS: final correspondence failures cannot retain success or bypass native guards')


if __name__ == '__main__':
    main()
