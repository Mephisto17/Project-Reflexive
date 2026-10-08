#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
mkdir -p verification
python3 scripts/check_sources.py
lake build > verification/build.log 2>&1
lake env lean TalagrandIntegral/Audit.lean > verification/axioms.log 2>&1
python3 scripts/check_axioms.py verification/axioms.log
lake env lean Small-vs-Weakly-Small-and-Talagrand-Discrete-Convexty-Conjecture.lean > verification/standalone.log 2>&1
python3 scripts/check_axioms.py verification/standalone.log
printf '%s\n' 'Module build, standalone build, and axiom audit succeeded.'
