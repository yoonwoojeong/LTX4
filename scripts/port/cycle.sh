#!/usr/bin/env bash
# Full recompile -> auto-fix sweep -> full recompile -> status report.
set -e
cd "$(dirname "$0")/../.."
rm -rf .lake/build/lib/LiquidTensorExperiment .lake/compile-logs
python3 scripts/port/compile.py 3 > .lake/compile.log 2>&1
python3 scripts/port/census.py
python3 scripts/port/autofix_all.py 3 > .lake/autofix_all.log 2>&1 || true
grep SWEEP .lake/autofix_all.log || true
rm -rf .lake/build/lib/LiquidTensorExperiment .lake/compile-logs
python3 scripts/port/compile.py 3 > .lake/compile.log 2>&1
python3 scripts/port/census.py -v 30
python3 scripts/port/status_report.py
