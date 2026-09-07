"""Optional historical transport evidence; not part of submission acceptance."""
from resources import ROOT, guarded
from policy import check_protected, dependencies

check_protected(); dependencies()
for command in (['lake','build','Blake3Prize.Migration.Transport'],
                ['lake','env','lean','-j1',ROOT/'scripts/MigrationAudit.lean']):
    result=guarded(command)
    print(result['stdout'],end='',flush=True)
dependencies(snapshot=True)
