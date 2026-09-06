"""Install and build trusted dependencies before accepting submission code."""
from resources import ROOT,guarded
from policy import check_protected,dependencies,prepare_generated_cache_excludes

check_protected()
for command in (['lake','update'],['lake','build','blake3-trusted']):
    print(f"CHECK: {' '.join(command)}",flush=True)
    r=guarded(command)
    print(r['stdout'],end='');print(r['stderr'],end='')
    print(f"Peak RSS: {r['peakMemoryBytes']} bytes",flush=True)
prepare_generated_cache_excludes()
dependencies(snapshot=True)
print('PASS: pinned sources and trusted dependency build snapshot')
