#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
python3 verify_common_factor_graphs.py
python3 verify_period_words.py
python3 check_row_inner_action.py
python3 check_component_controls.py
python3 verify_component_reduction.py
python3 check_gcd_fold_sweep.py --controls
# The generated-pair sweep runs through inner area 7 by default; FULL=1 runs
# through inner area 9, which also reaches remainder four.
if [ "${FULL:-0}" = 1 ]; then SWEEP=9; else SWEEP=7; fi
python3 check_gcd_fold_sweep.py --sweep "$SWEEP"
python3 check_native_word_folds.py
python3 check_gcd_fold_words.py
python3 check_component_keys.py
# The window-locality probe runs on a default range; FULL=1 widens it.
if [ "${FULL:-0}" = 1 ]; then RANGE=--full; else RANGE=; fi
python3 check_mark_locality.py ${RANGE:+"$RANGE"}
# Reassociation through a coarse mark (lem:gluing-aligned) and the gauge identity.
python3 check_reassociation.py
# Verifies the chart drawn in the paper's figure: the mark against the legality
# predicate, and the composition by two independent routes.  --check-only
# imports no plotting library, so the suite needs none.
python3 make_figures.py --check-only
printf 'ALL PASS\n'
