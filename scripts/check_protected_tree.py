#!/usr/bin/env python3

from pathlib import Path

from protected_tree import assert_protected_tree


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1]
    print(f"ok — protected tree {assert_protected_tree(root)}")
