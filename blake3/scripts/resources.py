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


def guarded(command, cwd=ROOT, *, native=False, timeout=None):
    result=run_limited(
        ['nice','-n','10',*map(str,command)],Path(cwd),
        timeout or (300 if native else 1800),
        1073741824 if native else 4294967296,
        16*1024*1024,2*1024**3,32 if native else 64,64*1024**3,
        REPO/'scripts/run_with_rss.py','BLAKE3 native check' if native else 'BLAKE3 build')
    return result
