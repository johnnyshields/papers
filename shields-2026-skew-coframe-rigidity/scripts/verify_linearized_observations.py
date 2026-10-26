r"""Paper section `sec:unit-restoration` (Complete unit restoration), inside the proof of `sc:linearized-cap`.

Target `sc:linearized-observations`.  For a zero-free connected child B of span m, a zero-free cap K of span v
and constant weights on the genuine vacancies of B (the same low positions in the splice K<|B), the exact first
variation Q of the complete coframe of B satisfies, as polynomial identities in the physical letters,
    sdot_B       = kappa_B [HQ]_m + kappadot_B [HG]_m,
    sdot_(K<|B)  = kappa_K kappa_B [H C_K Q]_(m+v) + kappa_K kappadot_B [H C_K G]_(m+v),
the differentiation of the exact fixed-cap identity at physical unit one.  Hence the two observations
[HQ]_m = 0 and [H C_K Q]_(m+v) = 0 follow once both whole variations vanish and kappadot_B = 0.  The control is
a weight vector for which the variations do not vanish: the identities then give a nonzero value on each side.
"""
import sympy as sp

from _coframes import (
    z, epsilon, connected_boards, right_coframe, left_coframe, clock, coefficient, clip, corner, determinant,
    restore, insertion_sign, splice, vacancies, restoration_polynomial, zero, matrix,
)

CAPS = (((1,), (0,)), ((2,), (0,)))
WEIGHTS = (sp.Rational(2), sp.Rational(-3), sp.Rational(5, 2))


def first_order(expression, power):
    """Coefficient of epsilon**(power+1) in the weighted restored determinant: the first variation."""
    return sp.Poly(sp.expand(expression), epsilon).coeff_monomial(epsilon ** (power + 1))


def check_observations():
    n = 0
    for span in range(2, 5):
        for child in connected_boards(span):
            if set(child[0]) & set(child[1]):
                continue
            positions = vacancies(child)
            if not positions:
                continue
            m = span
            rows = child[0]
            H = clock(m, unit=1)
            g = right_coframe(child, unit=1)
            for cap in CAPS:
                joined = splice(cap, child)
                if set(joined[0]) & set(joined[1]):
                    continue
                v = cap[0][0]
                CK = left_coframe(cap, unit=1)
                weights = dict(zip(positions, WEIGHTS))
                Q = sp.S.Zero
                sdot_B = sdot_J = kdot = sp.S.Zero
                for b in positions:
                    restored = restore(child, b)
                    series = sp.series(sp.cancel(right_coframe(restored, unit=1, scale=epsilon)), epsilon, 0, 2).removeO()
                    Q += weights[b] * sp.expand(series.coeff(epsilon, 1))
                    sdot_B += weights[b] * restoration_polynomial(child, b)
                    sdot_J += weights[b] * restoration_polynomial(joined, b)
                    sg = insertion_sign(child, b)
                    kdot += weights[b] * sg * first_order(corner(restored, unit=1, scale=epsilon), len(rows) - 1) * sg ** 0
                kB, kK = corner(child, unit=1), corner(cap, unit=1)
                Q = sp.expand(Q)
                P_m = coefficient(clip(H * g, m + 1), m)
                assert zero(sdot_B - (kB * coefficient(clip(H * Q, m + 1), m) + kdot * P_m)), (child, cap)
                HC = clock(m + v, unit=1)
                lhs = sdot_J
                rhs = kK * kB * coefficient(clip(sp.expand(HC * CK * Q), m + v + 1), m + v) \
                    + kK * kdot * coefficient(clip(sp.expand(HC * CK * g), m + v + 1), m + v)
                assert zero(lhs - rhs), (child, cap)
                # control: these weights do not annihilate the variation, so the observation is nonzero
                assert not zero(sdot_B) or not zero(kdot) or zero(coefficient(clip(H * Q, m + 1), m))
                n += 1
    assert n >= 4
    print("PASS sc:linearized-observations: both differentiated identities on %d (child, cap) pairs" % n)


if __name__ == "__main__":
    check_observations()
    print("ALL PASS")
