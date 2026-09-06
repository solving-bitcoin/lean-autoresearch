"""Regression checks for the submission-only overlay and canonical score."""
from pathlib import Path
import tempfile

from policy import check_source,score_value,git_dependencies,dependency_entries,shared_source_files
from render_benchmark_challenge import parse_score


def rejected(action):
    try:
        action()
    except SystemExit:
        return
    raise AssertionError('invalid submission metadata was accepted')


def main():
    dependency_entries()
    original = ('import Blake3Prize.Protected.Target\n'
                'namespace Blake3Prize.Submission\n'
                'def policyExample : Nat := 0\n'
                'end Blake3Prize.Submission\n')
    with tempfile.TemporaryDirectory(prefix='blake3-policy-') as directory:
        submission = Path(directory)
        solution = submission/'Solution.lean'
        score = submission/'score.txt'
        solution.write_text(original)
        score.write_text('unranked\n')
        assert score_value(score) is None
        score.write_text('707680\n')
        check_source(submission)
        assert parse_score(score) == 707680

        for raw in (b'-1\n', b'01\n', b'1 2\n', b' 1\n', b'1\r\n',
                    b'1\n\n', b'1e6\n', b'9'*513):
            score.write_bytes(raw)
            rejected(lambda: parse_score(score))
        score.write_text('707680\n')

        for source in (
            original.replace(':= 0', ':= by sorry'),
            'import Blake3Prize.Protected.Runner\n' + original,
            'import Blake3Prize.Baselines.HalfGates.Runner\n' + original,
            original + '\nnamespace Blake3Prize.Protected\ndef extra := 0\nend Blake3Prize.Protected\n',
            original + '\nnamespace SecretRelease\ndef extra := 0\nend SecretRelease\n',
            # Policy-only input: never elaborate it or read any file.
            original.replace('def policyExample : Nat := 0',
                             'def policyExample := include_str "fixture.txt"'),
            original.replace(':= 0', ':= include_str\n  ("fixture.txt")'),
            original.replace(':= 0', ':= include_str /- comment -/ "fixture.txt"'),
            # Inert policy fixtures, never compiled or registered as attributes.
            original + '\n@[wf_preprocess] theorem fixture : True := True.intro\n',
            original + '\n@[csimp] theorem fixture : True := True.intro\n',
            original.replace('def policyExample', '@[implemented_by fixture] def policyExample'),
            original + '\ntheorem fixture : True := by native_decide\n',
        ):
            solution.write_text(source)
            rejected(lambda: check_source(submission))
        solution.write_text(original)
        solution.write_text('import SecretRelease\n' + original)
        check_source(submission)
        solution.write_text('import SecretRelease.Simulation\n' + original)
        check_source(submission)
        # Documentation can name the forbidden feature without executing it.
        solution.write_text(original + '\n-- include_str is forbidden\n'
                            'def documentation := "include_str"\n')
        check_source(submission)
        solution.write_text(original)
        extra = submission/'extra.json'
        extra.write_text('{}')
        rejected(lambda: check_source(submission))
        extra.unlink()
        (submission/'Alias.lean').symlink_to(solution)
        rejected(lambda: check_source(submission))
    # A path dependency is permitted only for the precise protected sibling.
    local={'type':'path','dir':'../secret-release','name':'secretRelease',
           'scope':'','manifestFile':'lake-manifest.json',
           'inherited':False,'configFile':'lakefile.lean'}
    external={'type':'git','name':'fixture','rev':'a'*40,'inherited':False}
    assert git_dependencies([local,external],[external]) == [external]
    for key, value in (('dir','../../elsewhere'),('dir','/tmp/elsewhere'),
                       ('name','replacement'),('configFile','other.lean'),
                       ('manifestFile','other.json'),('inherited',True)):
        rejected(lambda: git_dependencies([{**local,key:value},external],[external]))
    rejected(lambda: git_dependencies([local,local,external],[external]))
    rejected(lambda: git_dependencies([external],[external]))
    rejected(lambda: git_dependencies([local,external],[{**external,'rev':'b'*40}]))
    rejected(lambda: git_dependencies([local,external],[local]))
    with tempfile.TemporaryDirectory(prefix='secret-release-source-') as directory:
        root=Path(directory)
        (root/'SecretRelease.lean').write_text('-- protected fixture\n')
        (root/'.lake').mkdir(); (root/'.lake/cache').write_text('ignored')
        assert shared_source_files(root) == [root/'SecretRelease.lean']
        (root/'Alias').symlink_to(root/'.lake',target_is_directory=True)
        rejected(lambda: shared_source_files(root))
    print('PASS: canonical scores, proof-gap/import/namespace/file-inclusion policy, and submission file boundary')


if __name__ == '__main__':
    main()
