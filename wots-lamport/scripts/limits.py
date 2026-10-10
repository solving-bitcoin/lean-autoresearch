"""Use the shared capped process runner; never build outside these limits."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
sys.path.insert(0, str(REPO/'blake3/scripts'))
from resources import guarded as _guarded

def guarded(command, cwd=ROOT, **options):
    return _guarded(command, cwd, **options)
