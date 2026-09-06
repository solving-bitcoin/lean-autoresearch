"""Admission tests use inert Git blobs; candidate code is never executed."""
from pathlib import Path
import tempfile

from check_overlay import PREFIX, admitted_entries, extract, git


def rejected(action):
    try:
        action()
    except SystemExit as error:
        assert 'BLAKE3_OVERLAY_REJECTED' in str(error)
        return
    raise AssertionError('invalid overlay was admitted')


def main():
    regular = ('100644', 'blob', '1' * 40)
    different = ('100644', 'blob', '2' * 40)
    base = {PREFIX+'Solution.lean': regular, PREFIX+'score.txt': regular,
            'blake3/scripts/policy.py': regular, 'blake3/protected.sha256': regular,
            '.github/workflows/blake3-submission.yml': regular}
    admitted_entries(base, {**base, PREFIX+'Solution.lean': different})
    admitted_entries(base, {**base, PREFIX+'Helper.lean': regular})
    # A changed checker AND its replacement checksum are still protected.
    rejected(lambda: admitted_entries(base, {**base, 'blake3/scripts/policy.py': different,
                                           'blake3/protected.sha256': different}))
    for path in ('blake3/protected.sha256', 'blake3/scripts/policy.py',
                 '.github/workflows/blake3-submission.yml', 'scripts/run_with_rss.py',
                 'blake3/lakefile.lean', 'blake3/new-rule.txt',
                 PREFIX+'Nested/Helper.lean', PREFIX+'extra.json'):
        rejected(lambda: admitted_entries(base, {**base, path: different}))
    rejected(lambda: admitted_entries(base, {p: e for p, e in base.items()
                                            if p != 'blake3/scripts/policy.py'}))
    for mode, kind in (('120000', 'blob'), ('160000', 'commit'), ('100755', 'blob')):
        rejected(lambda: admitted_entries(base, {**base, PREFIX+'Solution.lean':
                                                (mode, kind, '2' * 40)}))
    # Exercise exact revisions and blob extraction in an isolated local repo.
    with tempfile.TemporaryDirectory(prefix='blake3-overlay-test-') as directory:
        root = Path(directory)
        repo = root/'repo'
        repo.mkdir()
        git(repo, 'init', '-q')
        (repo/PREFIX).mkdir(parents=True)
        (repo/PREFIX/'Solution.lean').write_text('-- harmless fixture\n')
        (repo/PREFIX/'score.txt').write_text('unranked\n')
        git(repo, 'add', '.')
        git(repo, '-c', 'user.name=Overlay Test', '-c', 'user.email=test@example.invalid',
            '-c', 'commit.gpgsign=false', 'commit', '-qm', 'Inert fixture')
        revision = git(repo, 'rev-parse', 'HEAD').decode().strip()
        # Working-tree files are not used as the source of admitted blobs.
        (repo/PREFIX/'Solution.lean').write_text('-- uncommitted fixture\n')
        destination = root/'submission'
        report = extract(repo, repo, revision, revision, destination)
        assert (destination/'Solution.lean').read_text() == '-- harmless fixture\n'
        assert report['trustedBaseSha'] == revision
        rejected(lambda: extract(repo, repo, '0' * 40, revision, root/'wrong'))
    print('PASS: base-owned tree equality, protected digests/workflows, file modes, and immutable extraction')


if __name__ == '__main__':
    main()
