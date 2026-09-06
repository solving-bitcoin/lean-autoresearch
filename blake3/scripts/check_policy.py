"""Regression checks for the submission-only overlay and canonical score."""
from pathlib import Path
import tempfile

from policy import check_source,score_value
from render_benchmark_challenge import parse_score


def rejected(action):
    try:
        action()
    except SystemExit:
        return
    raise AssertionError('invalid submission metadata was accepted')


def main():
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
        ):
            solution.write_text(source)
            rejected(lambda: check_source(submission))
        solution.write_text(original)
        solution.write_text('import SecretRelease\n' + original)
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
    print('PASS: canonical scores, proof-gap/import/namespace/file-inclusion policy, and submission file boundary')


if __name__ == '__main__':
    main()
