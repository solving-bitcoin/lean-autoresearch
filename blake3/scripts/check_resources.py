"""The disk budget includes the shared sibling, without changing child cwd."""
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

import resources
from resources import guarded
from verify_submission import run_limited

# Capture configuration only: never start an 8 GiB process on the local host.
for marker in ('', 'false', '1', 'true'):
    for native in (False, True):
        with patch.dict(os.environ, {'GITHUB_ACTIONS': marker}), \
                patch.object(resources, 'run_limited', return_value={}) as run:
            guarded(['fixture'], native=native)
        expected = 1024**3 if native else (8 if marker == 'true' else 4) * 1024**3
        assert run.call_args.args[3] == expected
        assert run.call_args.args[2] == (300 if native else 1800)
        assert run.call_args.args[6] == (32 if native else 64)

for project_name in ('blake3','g1-release'):
    with tempfile.TemporaryDirectory(prefix='secret-release-quota-') as directory:
        root=Path(directory).resolve()
        project=root/project_name;project.mkdir()
        shared=root/'secret-release';shared.mkdir()
        calls=[]
        def capture(*args):
            calls.append(args)
            return {}
        with patch.object(resources,'run_limited',capture):
            guarded([sys.executable,'-c','import os; print(os.getcwd())'],project,native=True)
        args=list(calls.pop())
        assert args[1] == root
        result=run_limited(*args)
        assert result['stdout'].strip() == str(project)
        # A regular file outside the child's cwd must count toward the same quota.
        (shared/'fixture').write_bytes(b'x'*1024)
        args[7]=512  # Only the disk cap changes; existing RSS/process caps remain.
        try:
            run_limited(*args)
        except SystemExit as error:
            assert 'working-directory limit' in str(error), str(error)
        else:
            raise AssertionError('shared-package bytes escaped the disk quota')
print('PASS: original child cwd and combined shared-package disk accounting')
print('PASS: 8 GiB CI builds, 4 GiB local builds, and 1 GiB native checks')
