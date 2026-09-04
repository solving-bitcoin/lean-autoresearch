#!/usr/bin/env python3
"""Enforce the untrusted submission source and import policy."""

from __future__ import annotations

import argparse
from pathlib import Path
import re

from lean_source_policy import LexError, code_without_comments_or_strings, identifiers, import_modules


MAX_FILES = 1_000
MAX_TOTAL_BYTES = 10 * 1024 * 1024
MAX_SOURCE_BYTES = 4 * 1024 * 1024

FORBIDDEN_IDENTIFIERS = {
    "admit", "axiom", "axioms", "builtin_initialize", "command_elab",
    "dbgTrace", "debug.skipKernelTC", "elab", "elab_rules", "export", "extern",
    "implemented_by", "initialize", "macro", "macro_rules", "partial", "run_cmd",
    "run_elab", "run_tac", "sorry", "syntax", "trace", "traceVal", "unsafe",
}

FORBIDDEN_DIRECTIVES = (
    re.compile(r"(?m)#\s*(eval|exit)\b"),
    re.compile(r"@\s*\[\s*export\b"),
    re.compile(r"@\s*\[\s*implemented_by\b"),
    re.compile(r"\bset_option\s+(debug\.skipKernelTC|trustLevel)\b"),
)

VERIFIER_OWNED_NAMESPACES = (
    ("GarblingPrize", "Protected"),
    ("GarblingPrize", "Executable"),
)


def namespace_is_verifier_owned(parts: tuple[str, ...]) -> bool:
    return any(parts[:len(prefix)] == prefix for prefix in VERIFIER_OWNED_NAMESPACES)


def check_namespace_ownership(code: str, path: Path) -> None:
    """Reject declarations in namespaces owned by the protected runner.

    This is defense in depth: the runner is independently elaborated before a
    submission is imported. The lightweight command-stack handling covers both
    `namespace GarblingPrize.Executable` and nested namespace spelling.
    """
    current: tuple[str, ...] = ()
    command_stack: list[tuple[str, tuple[str, ...]]] = []
    declaration = re.compile(
        r"^(?:(?:private|protected|noncomputable)\s+)*"
        r"(?:def|abbrev|theorem|lemma|instance|structure|class|inductive|"
        r"opaque)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
    )
    for line_number, line in enumerate(code.splitlines(), start=1):
        stripped = line.strip()
        namespace = re.fullmatch(
            r"namespace\s+(_root_\.)?([A-Za-z_][A-Za-z0-9_'.]*)", stripped
        )
        if namespace:
            previous = current
            parts = tuple(namespace.group(2).split("."))
            current = parts if namespace.group(1) else current + parts
            command_stack.append(("namespace", previous))
            if namespace_is_verifier_owned(current):
                reject(f"{path.name}:{line_number} declares in verifier-owned namespace")
            continue
        if re.fullmatch(r"section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?", stripped):
            command_stack.append(("section", current))
            continue
        if re.fullmatch(r"end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?", stripped):
            if command_stack:
                _kind, current = command_stack.pop()
            continue
        declared = declaration.match(stripped)
        if declared:
            name = declared.group(1)
            absolute = name.startswith("_root_.")
            if absolute:
                name = name.removeprefix("_root_.")
            parts = tuple(name.split("."))
            qualified = parts if absolute else current + parts
            if namespace_is_verifier_owned(qualified):
                reject(f"{path.name}:{line_number} declares a verifier-owned name")


def reject(message: str) -> None:
    raise SystemExit(f"SOURCE_REJECTED: {message}")


def allowed_import(module: str) -> bool:
    return (
        module == "GarblingPrize.Protected.Target"
        or module.startswith("GarblingPrize.Submission.")
        or module == "Mathlib"
        or module.startswith("Mathlib.")
        or module == "CompPoly"
        or module.startswith("CompPoly.")
    )


def check_submission(submission: Path) -> None:
    if not submission.is_dir():
        reject(f"missing submission directory {submission}")
    for path in submission.rglob("*"):
        if path.is_symlink():
            reject(f"symlinks are not allowed: {path}")
        if path.is_dir() and path != submission:
            reject("the submission root must remain flat")

    files = sorted(path for path in submission.iterdir() if path.is_file())
    if len(files) > MAX_FILES:
        reject(f"submission has more than {MAX_FILES} files")
    if not {"Solution.lean", "score.txt"}.issubset({path.name for path in files}):
        reject("Solution.lean and score.txt are required")
    for path in files:
        if path.name != "score.txt" and path.suffix != ".lean":
            reject(f"unsupported file {path.name}")
        if path.suffix == ".lean" and not re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_']*\.lean", path.name
        ):
            reject(f"invalid flat Lean module name {path.name}")

    sizes = {path: path.stat().st_size for path in files}
    if sum(sizes.values()) > MAX_TOTAL_BYTES:
        reject("submission exceeds 10 MiB")

    for path in files:
        if path.suffix != ".lean":
            continue
        if sizes[path] > MAX_SOURCE_BYTES:
            reject(f"{path.name} exceeds 4 MiB")
        try:
            source = path.read_text(encoding="utf-8")
            code = code_without_comments_or_strings(source)
            imports = import_modules(code)
        except (LexError, UnicodeDecodeError, OSError) as error:
            reject(f"{path.name}: {error}")

        for imported in imports:
            if not allowed_import(imported.value):
                reject(f"{path.name}:{imported.line} imports forbidden module {imported.value}")
        for token in identifiers(code):
            if token.value in FORBIDDEN_IDENTIFIERS:
                reject(f"{path.name}:{token.line} uses forbidden token {token.value}")
        for pattern in FORBIDDEN_DIRECTIVES:
            match = pattern.search(code)
            if match:
                line = code.count("\n", 0, match.start()) + 1
                reject(f"{path.name}:{line} uses a forbidden directive")
        check_namespace_ownership(code, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("submission", type=Path)
    args = parser.parse_args()
    check_submission(args.submission.resolve())
    print("ok — submission source policy")


if __name__ == "__main__":
    main()
