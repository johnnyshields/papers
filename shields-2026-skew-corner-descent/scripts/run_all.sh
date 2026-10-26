#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 verify_corner.py
python3 check_corner_structure.py
python3 check_cofactor_primitivity.py
python3 check_shared_core.py
python3 verify_transport.py
python3 check_mark_structure.py
python3 check_without_v.py
python3 check_witness_determinant.py
python3 check_non_v_family.py
python3 check_mark_scope.py
python3 check_cell_model.py --transport
python3 verify_periods.py
python3 check_root_periods.py
python3 check_residual_pairs.py
python3 check_overlap_precision.py
python3 check_dual_scalar.py
python3 check_gap_cycles.py
python3 check_cyclic_inventory.py
python3 check_original_transfer.py
python3 check_original_defect_family.py
python3 check_profile_derivative.py
python3 check_full_window_boundary.py
echo "ALL PASS"
