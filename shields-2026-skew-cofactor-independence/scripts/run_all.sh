#!/bin/sh
# Run every verification script for this paper, in document order.
set -e
cd "$(dirname "$0")"

python3 check_nonnegative_rigidity.py 12 14
python3 check_exterior_gaps_nonnegative_class.py

for n in 2 3 4 5; do
  python3 check_cofactor_relations_exact.py "$n" 14 11
done
python3 check_cofactor_relations_all_spans.py 2 3
python3 check_dense_kernel_inputs.py 16 12 11 10
python3 check_cofactor_dilation.py
python3 check_ref_induction.py
python3 check_path_expansion_and_endpoint_units.py

python3 check_dense_kernel.py 14 11 10 9
python3 check_dense_kernel.py dilated 8 4
for n in 2 3 4 5; do
  python3 check_symmetric_kernel_exact.py "$n" 14 11
done
python3 check_symmetric_unit_kernel.py
python3 check_symmetric_lower_bound.py
python3 check_symmetric_child_derivative.py

python3 check_widen_containment.py
python3 check_dilation_all_t.py
python3 check_restoration_edges_and_rigidity.py
python3 check_paper_crossrefs.py

echo "ALL PASS"
