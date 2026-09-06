import importlib.util
from pathlib import Path
import sys
root=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('secret_release_summary',root.parent/'secret-release/scripts/summary.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
module.summarize(root,Path(sys.argv[1]))
