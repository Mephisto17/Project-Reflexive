#!/usr/bin/env python3
"""Check every #print axioms result against the permitted standard axioms."""
from pathlib import Path
import re, sys
text = Path(sys.argv[1]).read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
if len(reports) < 12:
    raise SystemExit(f'Expected at least 12 complete axiom reports, found {len(reports)}')
for name, raw in reports:
    axioms = {a.strip() for a in raw.split(',') if a.strip()}
    if not axioms <= allowed:
        raise SystemExit(f'Unexpected axioms in {name}: {sorted(axioms - allowed)}')
if re.search(r'\berror:', text):
    raise SystemExit('Compiler error in audit log')
print(f'Axiom audit passed for {len(reports)} declarations; only the three standard Lean axioms occur.')
