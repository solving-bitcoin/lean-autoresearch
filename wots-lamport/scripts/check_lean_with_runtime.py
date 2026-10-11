"""Explicit author diagnostic, inside the existing single author build cap.

This never creates an acceptance result. Ordinary source failures remain fatal;
resource failures stop before diagnostics, and an optimized executable requires
its complete equality proof before compilation. Full source success proceeds
to the ordinary isolated verifier and mandatory native tests.
"""
from check_lean import main

if __name__ == '__main__':
    main(['--runtime-probe', '--runtime-construction', 'lane'])
