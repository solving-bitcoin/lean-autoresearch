#!/usr/bin/env python3
"""Conservative lexer for release-policy checks on Lean source."""

from __future__ import annotations

from dataclasses import dataclass
import re


class LexError(ValueError):
    pass


@dataclass(frozen=True)
class Token:
    value: str
    line: int


IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def code_without_comments_or_strings(source: str) -> str:
    """Blank nested comments and strings while preserving newlines."""
    out = list(source)
    index = 0
    block_depth = 0
    mode = "code"
    escaped = False

    while index < len(source):
        char = source[index]
        next_char = source[index + 1] if index + 1 < len(source) else ""

        if mode == "line_comment":
            if char == "\n":
                mode = "code"
            else:
                out[index] = " "
            index += 1
            continue

        if mode == "block_comment":
            if char == "/" and next_char == "-":
                out[index] = out[index + 1] = " "
                block_depth += 1
                index += 2
            elif char == "-" and next_char == "/":
                out[index] = out[index + 1] = " "
                block_depth -= 1
                index += 2
                if block_depth == 0:
                    mode = "code"
            else:
                if char != "\n":
                    out[index] = " "
                index += 1
            continue

        if mode == "string":
            if char != "\n":
                out[index] = " "
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                mode = "code"
            index += 1
            continue

        if char == "-" and next_char == "-":
            out[index] = out[index + 1] = " "
            mode = "line_comment"
            index += 2
        elif char == "/" and next_char == "-":
            out[index] = out[index + 1] = " "
            mode = "block_comment"
            block_depth = 1
            index += 2
        elif char == '"':
            prefix = source[max(0, index - 2):index]
            if prefix.endswith("s!") or prefix.endswith("m!"):
                line = source.count("\n", 0, index) + 1
                raise LexError(f"interpolated strings are not allowed (line {line})")
            out[index] = " "
            mode = "string"
            escaped = False
            index += 1
        else:
            index += 1

    if mode == "block_comment":
        raise LexError("unterminated block comment")
    if mode == "string":
        raise LexError("unterminated string literal")
    return "".join(out)


def identifiers(code: str) -> list[Token]:
    return [
        Token(match.group(0), code.count("\n", 0, match.start()) + 1)
        for match in IDENTIFIER.finditer(code)
    ]


def import_modules(code: str) -> list[Token]:
    modules: list[Token] = []
    import_lines: set[int] = set()
    for match in re.finditer(r"(?m)^[ \t]*import[ \t]+([^\n]+)$", code):
        line = code.count("\n", 0, match.start()) + 1
        import_lines.add(line)
        tail = match.group(1).strip()
        if not tail:
            raise LexError(f"empty import command (line {line})")
        for module in tail.split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module):
                raise LexError(f"malformed import module {module!r} (line {line})")
            modules.append(Token(module, line))
    token_lines = {token.line for token in identifiers(code) if token.value == "import"}
    if token_lines != import_lines:
        raise LexError("every import must be a plain top-level import command")
    return modules
