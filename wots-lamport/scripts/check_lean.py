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
# Establish author-owned game checks before potentially expensive candidate proofs.
modules.sort(key=lambda name: (name.startswith('WotsLamport.Submission.'), name))
peak = 0
failed = []
for name in modules:
    # Independent proof modules can otherwise elaborate concurrently, each
    # retaining a large imported environment. Keep the aggregate cap intact.
    try:
        result = guarded(['lake', 'build', name])
    except SystemExit as error:
        # Keep ordinary elaboration diagnostics from independent modules in
        # one run. A resource rejection still stops immediately.
        if 'exceeded' in str(error) or 'timed out' in str(error):
            raise
        print(str(error), flush=True)
        failed.append(name)
        continue
    print(result['stdout'], end='', flush=True)
    print(result['stderr'], end='', flush=True)
    peak = max(peak, result['peakMemoryBytes'])
if failed:
    raise SystemExit('AUTHOR_PROOFS_REJECTED: ' + ', '.join(failed))
print(f"PASS: sequential author source build; peak {peak} bytes")
