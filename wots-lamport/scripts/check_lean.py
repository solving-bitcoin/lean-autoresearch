"""Author preview: compile every research module before the isolated audit.

Independent proof errors are collected in one sequential build. Failed
prerequisites block their dependents; every such block remains fatal. This is
never a substitute for the fresh protected-tree build and audits in verify.py.
"""
from limits import guarded, ROOT
import sys
import time
from boundary import check_protected, check_source, common


def module_graph(root):
    files = {'.'.join(p.relative_to(root).with_suffix('').parts): p
             for p in sorted((root/'WotsLamport').rglob('*.lean'))}
    lexer = common.source_policy
    dependencies = {
        name: [token.value for token in lexer.import_modules(
            lexer.code_without_comments_or_strings(path.read_text())) if token.value in files]
        for name, path in files.items()}
    ordered, visiting, visited = [], set(), set()

    def visit(name):
        if name in visiting:
            raise SystemExit('AUTHOR_PROOFS_REJECTED: import cycle at ' + name)
        if name in visited:
            return
        visiting.add(name)
        for dependency in dependencies[name]:
            visit(dependency)
        visiting.remove(name)
        visited.add(name)
        ordered.append(name)

    for name in sorted(files, key=lambda name: (name.startswith('WotsLamport.Submission.'), name)):
        visit(name)
    return ordered, dependencies


def main():
    check_protected()
    check_source(ROOT/'WotsLamport/Submission')
    modules, dependencies = module_graph(ROOT)
    peak, failed = 0, []
    rejected, compiled = set(), set()
    for name in modules:
        blockers = [dependency for dependency in dependencies[name] if dependency in rejected]
        if blockers:
            print(f"BLOCKED: {name}: failed prerequisites {', '.join(blockers)}", flush=True)
            rejected.add(name)
            failed.append(name)
            continue
        try:
            started = time.monotonic()
            print(f'CHECK: {name}', flush=True)
            result = guarded(['lake', 'build', name])
        except SystemExit as error:
            # Resource failures stop immediately; ordinary failures allow
            # independent source modules to be checked in this same run.
            if 'exceeded' in str(error) or 'timed out' in str(error):
                raise
            print(str(error), flush=True)
            rejected.add(name)
            failed.append(name)
            continue
        print(result['stdout'], end='', flush=True)
        print(result['stderr'], end='', flush=True)
        print(f'COMPILED: {name}; {time.monotonic()-started:.2f}s', flush=True)
        compiled.add(name)
        peak = max(peak, result['peakMemoryBytes'])
    # Diagnostic execution cannot suppress a source failure or create acceptance.
    # A complete source build proceeds directly to the normal isolated verifier.
    if failed:
        try:
            command = [sys.executable, ROOT/'scripts/check_runtime_probe.py']
            variant = 'original'
            for module, choice in [('CachedSharing', 'cached'), ('MachineSharing', 'machine')]:
                if f'WotsLamport.Submission.{module}' in compiled:
                    variant = choice
                    command += ['--construction', choice]
                    break
            print(f'CHECK: {variant} executable runtime diagnostic (source proofs compiled first)', flush=True)
            result = guarded(command)
            print(result['stdout'], end='', flush=True)
            print(result['stderr'], end='', flush=True)
            peak = max(peak, result['peakMemoryBytes'])
        except SystemExit as error:
            print(str(error), flush=True)
            if 'exceeded' in str(error) or 'timed out' in str(error):
                raise
            failed.append('runtime diagnostic')
    if failed:
        raise SystemExit('AUTHOR_PROOFS_REJECTED: ' + ', '.join(failed))
    print(f"PASS: sequential author source build; peak {peak} bytes")


if __name__ == '__main__':
    main()
