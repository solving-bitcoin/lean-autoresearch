#!/usr/bin/env python3
"""Comment/string-aware gap scan for every local Lean source."""

from pathlib import Path

from lean_source_policy import LexError, code_without_comments_or_strings, identifiers


FORBIDDEN = {"sorry", "admit", "axiom", "axioms", "unsafe", "implemented_by"}


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    failures: list[str] = []
    for path in sorted((root / "GarblingPrize").rglob("*.lean")):
        try:
            code = code_without_comments_or_strings(path.read_text(encoding="utf-8"))
        except (LexError, UnicodeDecodeError, OSError) as error:
            failures.append(f"{path.relative_to(root)}: {error}")
            continue
        for token in identifiers(code):
            if token.value in FORBIDDEN:
                failures.append(f"{path.relative_to(root)}:{token.line}: forbidden {token.value}")
    if failures:
        raise SystemExit("\n".join(failures))
    print("ok — no Lean proof or code-generation gaps")


if __name__ == "__main__":
    main()
