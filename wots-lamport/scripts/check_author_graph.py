"""Failure-injection checks for author preview scheduling; no Lean pass implied."""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import check_lean


def fixture(root, cycle=False, optimizations=False):
    directory = root/'WotsLamport/Submission'
    directory.mkdir(parents=True)
    (directory/'A.lean').write_text('import WotsLamport.Submission.B\n')
    (directory/'B.lean').write_text('import WotsLamport.Submission.A\n' if cycle else '')
    (directory/'C.lean').write_text('import WotsLamport.Submission.A\n')
    (directory/'D.lean').write_text('/- import WotsLamport.Submission.C -/\n')
    if optimizations:
        (directory/'MachineSharing.lean').write_text('import WotsLamport.Submission.D\n')
        (directory/'CachedSharing.lean').write_text('import WotsLamport.Submission.MachineSharing\n')


def exercise(failure=None, cycle=False, optimizations=False, rejected_optimization=None):
    with TemporaryDirectory() as directory:
        root = Path(directory)
        fixture(root, cycle, optimizations)
        calls = []

        def run(command):
            calls.append(tuple(map(str, command)))
            if command[:2] == ['lake', 'build'] and command[2].endswith('.B') and failure:
                raise SystemExit(failure)
            if command[:2] == ['lake', 'build'] and command[2].endswith('.'+str(rejected_optimization)):
                raise SystemExit('optimization proof failed')
            return dict(stdout='', stderr='', peakMemoryBytes=1)

        with patch.object(check_lean, 'ROOT', root), patch.object(check_lean, 'guarded', run), \
             patch.object(check_lean, 'check_protected'), patch.object(check_lean, 'check_source'), \
             redirect_stdout(StringIO()):
            try:
                check_lean.main()
            except SystemExit as error:
                return calls, str(error)
            return calls, None


def main():
    calls, error = exercise()
    assert error is None
    assert [call[-1] for call in calls] == [f'WotsLamport.Submission.{name}' for name in 'BACD']
    calls, error = exercise('ordinary elaboration failure')
    assert error.startswith('AUTHOR_PROOFS_REJECTED:')
    assert all(f'WotsLamport.Submission.{name}' in error for name in 'BAC')
    assert [call[-1] for call in calls[:2]] == ['WotsLamport.Submission.B', 'WotsLamport.Submission.D']
    assert len(calls) == 3 and calls[-1][-1].endswith('/scripts/check_runtime_probe.py')
    for failure in ['aggregate RSS exceeded', 'build timed out']:
        calls, error = exercise(failure)
        assert len(calls) == 1 and error == failure
    calls, error = exercise(cycle=True)
    assert not calls and error.startswith('AUTHOR_PROOFS_REJECTED: import cycle')
    for rejected, expected in [(None, 'cached'), ('CachedSharing', 'machine'), ('MachineSharing', None)]:
        calls, error = exercise('ordinary elaboration failure', optimizations=True,
                                rejected_optimization=rejected)
        assert error.startswith('AUTHOR_PROOFS_REJECTED:')
        probe = calls[-1]
        if expected is None:
            assert probe[-1].endswith('/scripts/check_runtime_probe.py')
            assert not any(call[-1] == 'WotsLamport.Submission.CachedSharing' for call in calls)
        else:
            assert probe[-2:] == ('--construction', expected)
            selected = 'CachedSharing' if expected == 'cached' else 'MachineSharing'
            assert any(call[-1] == 'WotsLamport.Submission.'+selected for call in calls[:-1])
    print('PASS: all modules on success; failures remain fatal; independent builds continue; resource/cycle failures stop; only compiled optimizations run')


if __name__ == '__main__':
    main()
