#!/usr/bin/env python3
"""Build isolated submission targets sequentially under one resource guard."""

from __future__ import annotations

import argparse
import subprocess


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("lake")
    parser.add_argument("targets", nargs="+")
    args = parser.parse_args()

    for target in args.targets:
        result = subprocess.run([args.lake, "build", target], check=False)
        if result.returncode != 0:
            raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
