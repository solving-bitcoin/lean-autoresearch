"""Author preview: compile every research module before the isolated audit.

This catches independent proof errors in one build. It is never a substitute
for the fresh protected-tree build and exact candidate audits in verify.py.
"""
from limits import guarded, ROOT
from boundary import check_protected, check_source

check_protected()
check_source(ROOT/'WotsLamport/Submission')
modules = ['.'.join(p.relative_to(ROOT).with_suffix('').parts)
           for p in sorted((ROOT/'WotsLamport').rglob('*.lean'))]
peak = 0
for name in modules:
    # Independent proof modules can otherwise elaborate concurrently, each
    # retaining a large imported environment. Keep the aggregate cap intact.
    result = guarded(['lake', 'build', name])
    print(result['stdout'], end='', flush=True)
    print(result['stderr'], end='', flush=True)
    peak = max(peak, result['peakMemoryBytes'])
print(f"PASS: sequential author source build; peak {peak} bytes")
