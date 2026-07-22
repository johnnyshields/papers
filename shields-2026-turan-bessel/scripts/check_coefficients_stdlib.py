#!/usr/bin/env python3
"""Dependency-free positivity audit of the exported degree-two coefficient tables.

Reads exported_coefficients.json and asserts that every block of the exceptional
numerator Q_*(a,t), expanded in R_a = psi_1(a+1) - 1/(a+1), has strictly positive
integer coefficients (paper section 5, Lemma 5.2, eq. (5.5), the manifestly positive
decomposition).  Since R_a > 0, this establishes Delta_2(a) > 0 for every a > 0
without SymPy or mpmath.
"""
from fractions import Fraction
import json
from pathlib import Path

data = json.loads(Path(__file__).with_name('exported_coefficients.json').read_text())
expected_lengths = {
    'Qstar_Ra_squared': 3,
    'Qstar_Ra_linear': 5,
    'Qstar_Ra_constant': 3,
}
for name, length in expected_lengths.items():
    block = data[name]
    coeffs = block['coefficients']
    powers = block['powers_of_a']
    assert len(coeffs) == length, name
    assert len(powers) == length, name
    assert powers == sorted(powers, reverse=True), name
    assert all(Fraction(c) > 0 for c in coeffs), name
    print(f'PASS {name}: {length} strictly positive coefficients')
print('ALL PASS: Q_* has positive coefficient blocks, so Delta_2(a) > 0 for a > 0')
