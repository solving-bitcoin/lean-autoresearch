"""No candidate-controlled rule, import side effect, or fake score is admitted."""
from pathlib import Path
import tempfile
from boundary import check_source, score_value, dependency_entries
import overlay


def rejected(action):
    try: action()
    except SystemExit: return
    raise AssertionError('invalid candidate accepted')


def main():
    dependency_entries()
    original = ('import G1Release.Protected.Target\nnamespace G1Release.Submission\n'
                'def fixture : Nat := 0\nend G1Release.Submission\n')
    with tempfile.TemporaryDirectory(prefix='g1-release-policy-') as directory:
        root = Path(directory)
        source = root/'Solution.lean'; source.write_text(original)
        score = root/'score.txt'; score.write_text('unranked\n')
        assert score_value(score) is None
        check_source(root)
        for text in (
            original.replace(':= 0', ':= by sorry'),
            original.replace(':= 0', ':= include_str "fixture.txt"'),
            original.replace(':= 0', ':= include_str /- comment -/ ("fixture.txt")'),
            original + '\n@[wf_preprocess] theorem f : True := True.intro\n',
            original + '\n@[csimp] theorem f : True := True.intro\n',
            original.replace('def fixture', '@[implemented_by f] def fixture'),
            original + '\nnamespace SecretRelease\ndef evil := 0\nend SecretRelease\n',
            original + '\nnamespace G1Release.Protected\ndef evil := 0\nend G1Release.Protected\n',
            'import G1Release.Protected.Runner\n' + original,
            'import GarblingPrize.Protected.SHA256\n' + original,
            'import GarblingPrize.Submission.Solution\n' + original,
            original + '\n#eval IO.println "untrusted"\n',
        ):
            source.write_text(text); rejected(lambda: check_source(root))
        source.write_text(original)
        for raw in (b'-1\n',b'01\n',b'1 2\n',b' 1\n',b'1\r\n',b'1\n\n',b'1e6\n'):
            score.write_bytes(raw); rejected(lambda: score_value(score))
        score.write_text('97\n'); assert score_value(score) == 97
        (root/'Link.lean').symlink_to(source); rejected(lambda: check_source(root))
    admission = overlay.common
    regular = ('100644','blob','a'*40)
    base = {admission.PREFIX+'Solution.lean': regular, admission.PREFIX+'score.txt': regular,
            'g1-release/protected.sha256': regular, 'secret-release/SecretRelease.lean': regular,
            'g1-release/scripts/boundary.py': regular, '.github/workflows/g1-release.yml': regular}
    changed = ('100644','blob','b'*40)
    assert admission.admitted_entries(base, {**base, admission.PREFIX+'Solution.lean':changed})
    for path in ('g1-release/protected.sha256','secret-release/SecretRelease.lean',
                 'g1-release/scripts/boundary.py','.github/workflows/g1-release.yml',
                 'GarblingPrize/Protected/G1.lean','g1-release/lakefile.lean'):
        rejected(lambda: admission.admitted_entries(base, {**base,path:changed}))
    # Recomputing the candidate digest along with replacement rules never helps.
    rejected(lambda: admission.admitted_entries(base, {**base,
        'g1-release/protected.sha256':changed, 'g1-release/scripts/boundary.py':changed}))
    rejected(lambda: admission.admitted_entries(base, {**base,
        admission.PREFIX+'Solution.lean':('120000','blob','a'*40)}))
    print('PASS: immutable rules, source/namespace/import restrictions, and canonical scores')

if __name__ == '__main__': main()
