"""Shared fail-closed resource guards; every build/run uses these defaults."""
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
sys.path.insert(0,str(REPO/'scripts'))
from verify_submission import run_limited

os.environ['LEAN_NUM_THREADS']='1'
# Lean 4.33.1 uses mimalloc 2.2.3, which requests transparent huge pages by
# default on Linux. Prefer ordinary pages under the aggregate RSS budget:
# partially used large pages can keep extra physical memory resident.
# https://github.com/microsoft/mimalloc/blob/v2.2.3/src/options.c
os.environ['MIMALLOC_ALLOW_LARGE_OS_PAGES']='0'

LOCAL_BUILD_RSS = 4 * 1024**3
CI_BUILD_RSS = 8 * 1024**3
NATIVE_RSS = 1024**3


def guarded(command, cwd=ROOT, *, native=False, timeout=None):
    cwd=Path(cwd).resolve()
    # The local library now builds in a sibling directory. Monitor both packages
    # for disk usage while preserving the command's original working directory.
    scope=cwd.parent if (cwd.name in ('blake3','secret-release','g1-release') and
                         ((cwd.parent/'blake3').is_dir() or (cwd.parent/'g1-release').is_dir()) and
                         (cwd.parent/'secret-release').is_dir()) else cwd
    enter='import os,sys; os.chdir(sys.argv[1]); os.execvp(sys.argv[2],sys.argv[2:])'
    # The author approved a larger build budget on GitHub's CI runners only.
    # Local invocations retain the machine-protecting 4 GiB budget, while
    # executable checks use 1 GiB in both environments.
    build_rss = CI_BUILD_RSS if os.environ.get('GITHUB_ACTIONS') == 'true' else LOCAL_BUILD_RSS
    result=run_limited(
        ['nice','-n','10',sys.executable,'-c',enter,str(cwd),*map(str,command)],scope,
        timeout or (300 if native else 1800),
        NATIVE_RSS if native else build_rss,
        16*1024*1024,2*1024**3,32 if native else 64,64*1024**3,
        REPO/'scripts/run_with_rss.py','BLAKE3 native check' if native else 'BLAKE3 build')
    return result
