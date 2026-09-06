"""BLAKE3 supplies protected configuration to the shared verifier."""
import importlib.util
from pathlib import Path
import sys
import policy
from resources import guarded
shared=Path(__file__).resolve().parents[2]/'secret-release/scripts'
sys.path.insert(0,str(shared))
spec=importlib.util.spec_from_file_location('secret_release_verifier',shared/'verify.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
if __name__=='__main__': module.verify(policy,guarded)
