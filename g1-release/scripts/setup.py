"""Build trusted sources and authenticate external caches before submission."""
from limits import guarded
from boundary import check_protected, dependencies, prepare_generated_cache_excludes

check_protected()
for command in (['lake','update'], ['lake','resolve-deps'], ['lake','build','g1-release-checks']):
    print(f"CHECK: {' '.join(command)}", flush=True)
    r = guarded(command)
    print(r['stdout'], end=''); print(r['stderr'], end='')
    print(f"Peak RSS: {r['peakMemoryBytes']} bytes", flush=True)
prepare_generated_cache_excludes()
dependencies(snapshot=True)
print('PASS: pinned G1/shared sources and authenticated external dependency builds')
