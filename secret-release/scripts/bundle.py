"""Protected code generation and four-tool packaging. No author-written main."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tarfile

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO/'blake3/scripts'))
from resources import guarded
TOOLS = ('garble', 'encode', 'evaluate', 'challenge')


def generate(project, fixture=False):
    config = json.loads((project/'challenge.json').read_text())
    fields = ('wireModule', 'wire', 'fixtureModule' if fixture else 'submissionModule',
              'fixtureEntry' if fixture else 'entry')
    values = [config[k] for k in fields]
    if not all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*', v) for v in values):
        raise SystemExit('invalid protected Lean module/identifier')
    module, wire, candidate_module, entry = values
    directory = project/'.lake/generated'; directory.mkdir(parents=True, exist_ok=True)
    (directory/'SRTools.lean').write_text(
        f'import SecretRelease.CLI\nimport {module}\nimport {candidate_module}\n\n'
        f'def main (args : List String) : IO UInt32 :=\n'
        f'  SecretRelease.CLI.main {wire} {entry} args\n')
    return config


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        while part := stream.read(1024*1024): h.update(part)
    return h.hexdigest()


def package(project, destination, *, fixture=False):
    executable = project/'.lake/build/bin/secret-release-tools'
    destination.mkdir(parents=True, exist_ok=True)
    # Hard links avoid quadrupling disk use; archives may store four entries.
    for name in TOOLS:
        target = destination/name
        target.unlink(missing_ok=True)
        try: os.link(executable, target)
        except OSError: shutil.copy2(executable, target)
    result = guarded([destination/'challenge', 'describe'], project, native=True)
    if result['stderr']: raise SystemExit('unexpected description side output')
    metadata = json.loads(result['stdout'])
    metadata.update(bundleVersion=1, fixture=fixture,
                    # Packaging is not kernel acceptance. The verifier adds its audited result.
                    acceptance='not-audited', score=None,
                    sourceDescriptorSha256=sha(project/'challenge.json'),
                    dependencyManifestSha256=sha(project/'lake-manifest.json'),
                    tools={name: {'sha256': sha(destination/name),
                                  'bytes': (destination/name).stat().st_size} for name in TOOLS},
                    installedBytes=sum({(p.stat().st_dev,p.stat().st_ino):p.stat().st_size
                                        for p in (destination/name for name in TOOLS)}.values()),
                    unpackedToolBytes=4*executable.stat().st_size)
    (destination/'bundle.json').write_text(json.dumps(metadata, indent=2)+'\n')
    return metadata


def archive(destination):
    """Preserve executable modes and hard links through CI artifact downloads."""
    path=destination.parent/(destination.name+'.tar.gz')
    with tarfile.open(path,'w:gz') as stream:
        stream.add(destination,arcname=destination.name)
    return path


def build(project, *, fixture=False, destination=None):
    project = Path(project).resolve()
    generate(project, fixture)
    result = guarded(['lake', 'build', 'secret-release-tools'], project)
    print(result['stdout'], end='', flush=True)
    destination = destination or project/'.yukon'/('fixture' if fixture else 'bundle')
    metadata = package(project, destination, fixture=fixture)
    archive(destination)
    print(f"PASS: four tools ({metadata['status']}); build peak {result['peakMemoryBytes']} bytes", flush=True)
    return metadata


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('project', type=Path)
    parser.add_argument('--fixture', action='store_true')
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    if args.generate_only: generate(args.project.resolve(), args.fixture)
    else: build(args.project, fixture=args.fixture)
