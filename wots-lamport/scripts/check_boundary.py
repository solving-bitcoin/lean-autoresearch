"""No candidate-controlled rule, import side effect, or fake score is admitted."""
from pathlib import Path
import tempfile
from unittest.mock import patch
import boundary
from boundary import check_source, score_value, dependency_entries
import overlay


def rejected(action):
    try: action()
    except SystemExit: return
    raise AssertionError('invalid candidate accepted')


def main():
    dependency_entries()
    original = ('import WotsLamport.Protected.Target\nnamespace WotsLamport.Submission\n'
                'def fixture : Nat := 0\nend WotsLamport.Submission\n')
    with tempfile.TemporaryDirectory(prefix='wots-lamport-policy-') as directory:
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
            original + '\nnamespace WotsLamport.Protected\ndef evil := 0\nend WotsLamport.Protected\n',
            original + '\nnamespace WotsLamport.Tests\ndef evil := 0\nend WotsLamport.Tests\n',
            original + '\nnamespace WotsLamport.Math\ndef evil := 0\nend WotsLamport.Math\n',
            'import WotsLamport.Protected.Runner\n' + original,
            'import WotsLamport.Tests.RunnerFixture\n' + original,
            'import WotsLamport.Tests.Contract\n' + original,
            'import SecretRelease.NativeHash\n' + original,
            'import SecretRelease.CLI\n' + original,
            'import WotsLamport.Math.SHA256\n' + original,
            original + '\n#eval IO.println "untrusted"\n',
        ):
            source.write_text(text); rejected(lambda: check_source(root))
        source.write_text(original)
        source.write_text('import SecretRelease.Profiles\n' + original)
        check_source(root)
        for module in ('Encoding','Chains','Disclosure','ScriptRelation','Adaptive'):
            source.write_text(f'import WotsLamport.Protected.{module}\n' + original)
            check_source(root)
        source.write_text(original)
        for raw in (b'-1\n',b'01\n',b'1 2\n',b' 1\n',b'1\r\n',b'1\n\n',b'1e6\n'):
            score.write_bytes(raw); rejected(lambda: score_value(score))
        score.write_text('97\n'); assert score_value(score) == 97
        (root/'Link.lean').symlink_to(source); rejected(lambda: check_source(root))
    admission = overlay.common
    regular = ('100644','blob','a'*40)
    base = {admission.PREFIX+'Solution.lean': regular, admission.PREFIX+'score.txt': regular,
            'wots-lamport/protected.sha256': regular, 'secret-release/SecretRelease.lean': regular,
            'wots-lamport/scripts/boundary.py': regular, '.github/workflows/wots-lamport.yml': regular}
    changed = ('100644','blob','b'*40)
    assert admission.admitted_entries(base, {**base, admission.PREFIX+'Solution.lean':changed})
    for path in ('wots-lamport/protected.sha256','secret-release/SecretRelease.lean',
                 'wots-lamport/scripts/boundary.py','.github/workflows/wots-lamport.yml',
                 'wots-lamport/WotsLamport/Math/WOTS.lean','wots-lamport/lakefile.lean'):
        rejected(lambda: admission.admitted_entries(base, {**base,path:changed}))
    # Recomputing the candidate digest along with replacement rules never helps.
    rejected(lambda: admission.admitted_entries(base, {**base,
        'wots-lamport/protected.sha256':changed, 'wots-lamport/scripts/boundary.py':changed}))
    rejected(lambda: admission.admitted_entries(base, {**base,
        admission.PREFIX+'Solution.lean':('120000','blob','a'*40)}))
    with tempfile.TemporaryDirectory(prefix='wots-lamport-metadata-') as directory:
        root=Path(directory);shared=root/'shared';shared.mkdir()
        source=root/'Protected/Fixture.lean';source.parent.mkdir()
        source.write_text('-- protected fixture\n')
        with patch.object(boundary,'ROOT',root), patch.object(boundary,'REPO',root), \
                patch.object(boundary,'SHARED',shared):
            original=boundary.digest()
            for p in (root/'.DS_Store',source.parent/'.DS_Store',shared/'.DS_Store'):
                p.write_bytes(b'local desktop metadata')
            assert boundary.digest() == original
            source.write_text('-- changed protected fixture\n')
            assert boundary.digest() != original
    print('PASS: immutable rules, source/namespace/import restrictions, and canonical scores')

if __name__ == '__main__': main()
