#!/usr/bin/env python3
"""Reject proof placeholders and compiler-trust shortcuts in project sources."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

def uncomment(text):
    # Lean has nested block comments. Keep newlines for useful diagnostics.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif not depth and text.startswith('--', i):
            stop = text.find('\n', i)
            i = len(text) if stop < 0 else stop
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise RuntimeError('Unterminated block comment')
    return ''.join(out)

files = list((ROOT / 'TalagrandIntegral').glob('*.lean'))
files += list((ROOT / 'TalagrandConjectures').glob('*.lean'))
files += [ROOT / 'TalagrandIntegral.lean', ROOT / 'Small-vs-Weakly-Small-and-Talagrand-Discrete-Convexty-Conjecture.lean']
for path in files:
    match = re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', uncomment(path.read_text()))
    if match:
        raise SystemExit(f'Forbidden proof token in {path.relative_to(ROOT)}: {match.group()}')
print(f'Source audit passed: {len(files)} Lean files.')
