"""Authenticate the full tree, then extract only regular G1 submission blobs."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'blake3/scripts'))
import check_overlay as common
common.PREFIX = 'g1-release/G1Release/Submission/'
if __name__ == '__main__': common.main()
