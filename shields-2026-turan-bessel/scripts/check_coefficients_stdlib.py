#!/usr/bin/env python3
"""Paper section 5 (Mixed determinants and coefficientwise positivity), Lemma 5.3
(lem:Delta2-positive), eq. (5.5): dependency-free positivity audit of the exported
degree-two coefficient tables.

Reads exported_coefficients.json and asserts that every block of the exceptional
numerator Q_*(a,t), expanded in R_a = psi_1(a+1) - 1/(a+1), has strictly positive
integer coefficients -- the manifestly positive decomposition of eq. (5.5).

Scope: given eqs. (5.4)-(5.5) as identities -- which verify_determinant.py re-derives
symbolically from the series definition of Z -- positivity of these blocks together
with R_a > 0 is what yields Delta_2(a) > 0 for every a > 0.  This script checks only
the positivity of the blocks, in exact integer arithmetic and without SymPy or mpmath;
it does not itself establish the identities.
"""
import json
from pathlib import Path


def polymul(p, q):
    """Multiply dense integer coefficient lists, lowest power first."""
    out = [0]*(len(p) + len(q) - 1)
    for i, pi in enumerate(p):
        for j, qj in enumerate(q):
            out[i + j] += pi*qj
    return out


def poly(*factors):
    r = [1]
    for fac in factors:
        r = polymul(r, fac)
    return r


# The three blocks of eq. (5.5), expanded here in exact integer arithmetic so the
# JSON is checked against the paper rather than merely checked for shape.
#   2 a^4 (a+1)^2,   2 a^2 (a+1)^2 (8a^2+3a+1),   2 a (a+1) (5a+3)
A1, AP1, Q8 = [0, 1], [1, 1], [1, 3, 8]          # a, a+1, 8a^2+3a+1
A5 = [3, 5]                                       # 5a+3
expected = {
    'Qstar_Ra_squared':  poly([2], A1, A1, A1, A1, AP1, AP1),
    'Qstar_Ra_linear':   poly([2], A1, A1, AP1, AP1, Q8),
    'Qstar_Ra_constant': poly([2], A1, AP1, A5),
}

data = json.loads(Path(__file__).with_name('exported_coefficients.json').read_text())
for name, dense in expected.items():
    block = data[name]
    coeffs = block['coefficients']
    powers = block['powers_of_a']
    # {power: coefficient} from eq. (5.5), dropping the zero terms
    want = {p: c for p, c in enumerate(dense) if c != 0}
    assert len(coeffs) == len(powers), name
    assert powers == sorted(powers, reverse=True), name
    # integrality, which Fraction(2.5) > 0 would silently accept
    assert all(isinstance(c, int) for c in coeffs), (name, 'non-integer coefficient')
    assert all(isinstance(p, int) for p in powers), (name, 'non-integer power')
    assert all(c > 0 for c in coeffs), name
    assert dict(zip(powers, coeffs)) == want, (name, dict(zip(powers, coeffs)), want)
    print(f'PASS {name}: {len(coeffs)} strictly positive integer coefficients,'
          f' matching eq. (5.5) at powers {powers}')
print('ALL PASS: the exported Q_* blocks are exactly eq. (5.5) and strictly positive,'
      ' so with eqs. (5.4)-(5.5) Delta_2(a) > 0 for a > 0')
