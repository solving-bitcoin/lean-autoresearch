"""Regression checks for generated identifiers, registry and immutable admission."""
import json
import os
import tarfile
from pathlib import Path
import sys
import tempfile
from bundle import generate, archive, TOOLS
from projects import projects

REPO=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(REPO/'blake3/scripts'))
import check_overlay as overlay


def reject(action):
    try: action()
    except SystemExit: return
    raise AssertionError('unsafe framework configuration was accepted')


def main():
    with tempfile.TemporaryDirectory(prefix='secret-release-framework-') as directory:
        root=Path(directory); project=root/'demo'; project.mkdir()
        config={'wireModule':'Demo.Wire','wire':'Demo.wire','submissionModule':'Demo.Submission',
                'entry':'Demo.entry','fixtureModule':'Demo.Fixture','fixtureEntry':'Demo.fixture'}
        path=project/'challenge.json';path.write_text(json.dumps(config))
        generate(project)
        source=(project/'.lake/generated/SRTools.lean').read_text()
        assert 'SecretRelease.CLI.main Demo.wire Demo.entry args' in source
        for field in ('wireModule','wire','submissionModule','entry'):
            bad=config|{field:'Demo\nunsafe def main := 0'};path.write_text(json.dumps(bad))
            reject(lambda:generate(project))
        bundle=root/'bundle';bundle.mkdir()
        (bundle/'garble').write_bytes(b'inert archive fixture')
        (bundle/'garble').chmod(0o755)
        for tool in TOOLS[1:]:os.link(bundle/'garble',bundle/tool)
        (bundle/'bundle.json').write_text('{}')
        with tarfile.open(archive(bundle)) as stream:
            extracted=root/'extracted';stream.extractall(extracted,filter='data')
        for tool in TOOLS:
            restored=extracted/'bundle'/tool
            assert restored.read_bytes()==b'inert archive fixture'
            assert restored.stat().st_mode & 0o111
        (root/'secret-release').mkdir(); registry=root/'secret-release/challenges.json'
        registry.write_text('["demo"]');assert projects(root)==['demo']
        for bad in [['../demo'],['demo;echo bad'],['demo','demo'],[]]:
            registry.write_text(json.dumps(bad));reject(lambda:projects(root))
        # The shared overlay admits a union of regular submission paths, but
        # any protected SDK/codec/workflow/lock/digest mutation is still rejected.
        prefixes=['blake3/Blake3Prize/Submission/','g1-release/G1Release/Submission/']
        original_prefix,original_editable=overlay.PREFIX,overlay.editable
        try:
            overlay.PREFIX=prefixes[0]
            overlay.editable=lambda path:any(path.startswith(p) and
                (path[len(p):]=='score.txt' or overlay.MODULE.fullmatch(path[len(p):])) for p in prefixes)
            base={p+n:('100644','blob','old') for p in prefixes for n in ('Solution.lean','score.txt')}
            head={p:('100644','blob','new') for p in base}
            assert len(overlay.admitted_entries(base,head))==2
            for protected in ['secret-release/SecretRelease.lean','secret-release/rust/Cargo.lock',
                              'secret-release/rust/secret-release/src/lib.rs','blake3/protected.sha256',
                              '.github/workflows/secret-release-submission.yml']:
                reject(lambda:overlay.admitted_entries(base,head|{protected:('100644','blob','new')}))
            reject(lambda:overlay.admitted_entries(base,head|{prefixes[0]+'bad.lean':('120000','blob','new')}))
            reject(lambda:overlay.admitted_entries(base,head|{prefixes[0]+'nested/Bad.lean':('100644','blob','new')}))
        finally: overlay.PREFIX,overlay.editable=original_prefix,original_editable
    print('PASS: generated identifiers, executable archive modes, registry, protected Rust/codec/workflow admission')

if __name__=='__main__':main()
