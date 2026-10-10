"""Author preview: compile every research module before the isolated audit.

This catches independent proof errors in one build. It is never a substitute
for the fresh protected-tree build and exact candidate audits in verify.py.
"""
from limits import guarded, ROOT
from boundary import check_protected, check_source

check_protected()
check_source(ROOT/'WotsLamport/Submission')
result = guarded(['lake', 'build', 'WotsLamport'])
print(result['stdout'], end='', flush=True)
print(result['stderr'], end='', flush=True)
print(f"PASS: author source build; peak {result['peakMemoryBytes']} bytes")
