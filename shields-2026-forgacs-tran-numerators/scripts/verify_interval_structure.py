#!/usr/bin/env python3
"""Structural facts about the Forgacs-Tran interval that the other scripts assume.

Four claims, none of which is checked elsewhere in this harness:

  (S1)  rQ(t) - tQ'(t) > 0 on (0, x_1).                     paper L569-570
        This is what makes t_a the SMALLEST positive critical point of g and
        forces t_a >= x_1.

  (S2)  a = g(t_a) >= 0, with a = 0 exactly when rho >= 2.  paper L569-571
        This is what puts I_{Q,r} inside (0, infty) at all, so it underpins
        the main theorem's "outside (0,infty)" formulation.

  (S3)  deg Q > r  =>  the leading t-coefficient of Q(t) + z t^r is the
        nonzero constant q_{deg Q}, independent of z.        paper L588-589
        Cited in thm:FT-geometry's proof; must not depend on tau, or the
        citation of lem:degree-drop there would be circular.

  (S4)  deg Q = r = d  =>  z_* = -q_d, and the case z_* in closure(I_{Q,r})
        is NON-VACUOUS.                                      paper L896-912
        lem:degree-drop splits on whether z_* meets the parameter interval.
        If that branch were empty the split would be dead weight; if it is
        reachable, the tau-normalisation branch is load-bearing.

Exact rational/symbolic arithmetic where possible; mpmath elsewhere.
"""

import sympy as sp
from mpmath import mp

mp.dps = 40

t, z = sp.symbols('t z', real=True)


def Q_from_zeros(zeros, Q0=1):
    """Q(t) = Q0 * prod (1 - t/x_j), the paper's eq:Q-hypotheses normalisation."""
    e = sp.Integer(Q0)
    for x in zeros:
        e *= (1 - t / sp.Rational(x))
    return sp.expand(e)


def critical_points(Qe, r):
    """Positive real zeros of rQ - tQ', i.e. the positive critical points of g."""
    phi = sp.expand(r * Qe - t * sp.diff(Qe, t))
    if phi.is_number:
        return [], phi
    roots = sp.real_roots(sp.Poly(phi, t))
    pos = sorted({sp.nsimplify(rt) for rt in roots if rt.is_real and rt > 0},
                 key=lambda e: float(e))
    return pos, phi


def g_at(Qe, r, tv):
    return -Qe.subs(t, tv) / tv**r


# (zeros of Q with multiplicity, r, label)
CONFIGS = [
    ([1, 2, 4],        1, 'rho=1, deg Q=3 > r=1  (the figure)'),
    ([1, 2],           1, 'rho=1, deg Q=2 = r+1'),
    ([1, 1, 3],        1, 'rho=2, deg Q=3 > r=1'),
    ([1, 1, 1, 5],     1, 'rho=3, deg Q=4 > r=1'),
    ([2, 3, 5],        2, 'rho=1, deg Q=3 > r=2'),
    ([1, 2, 4],        3, 'rho=1, deg Q=3 = r=3   <-- degree-drop, d ODD'),
    ([1, 1, 4],        3, 'rho=2, deg Q=3 = r=3   <-- degree-drop, d ODD'),
    ([2, 3],           3, 'rho=1, deg Q=2 < r=3'),
    ([1, 1, 1],        3, 'rho=3, deg Q=3 = r=3   <-- degree-drop, d ODD, a=0'),
    ([1, 2],           2, 'rho=1, deg Q=2 = r=2   <-- degree-drop, d EVEN'),
    ([1, 1],           2, 'rho=2, deg Q=2 = r=2   <-- degree-drop, d EVEN'),
    ([1, 2, 3, 7],     4, 'rho=1, deg Q=4 = r=4   <-- degree-drop, d EVEN'),
    ([2, 2, 5, 5, 9],  5, 'rho=2, deg Q=5 = r=5   <-- degree-drop, d ODD'),
    ([1, 1],           4, 'rho=2, deg Q=2 < r=4   <-- escaping at lower endpt'),
    ([3, 3, 7, 11],    2, 'rho=2, deg Q=4 > r=2'),
    ([1, 2, 2, 2, 9],  1, 'rho=1, repeated NON-smallest zero'),
]

print('=' * 78)
print('S1/S2: smallest positive critical point and the lower endpoint')
print('=' * 78)

drop_reachable = []

for zeros, r, label in CONFIGS:
    Qe = Q_from_zeros(zeros)
    x1 = sp.Rational(min(zeros))
    rho = sum(1 for x in zeros if sp.Rational(x) == x1)
    pos, phi = critical_points(Qe, r)
    assert pos, f'{label}: no positive critical point of g'
    ta = pos[0]
    a = sp.simplify(g_at(Qe, r, ta))

    # --- S1: rQ - tQ' > 0 strictly on (0, x_1) ---------------------------
    # sample densely, and also check the value at 0 is Q(0)*r > 0
    assert sp.simplify(phi.subs(t, 0)) == r * Qe.subs(t, 0), 'phi(0) != r Q(0)'
    for k in range(1, 400):
        tv = x1 * sp.Rational(k, 400)
        val = phi.subs(t, tv)
        assert val > 0, f'{label}: rQ - tQ\' = {val} <= 0 at t={float(tv):.4f} in (0,x_1)'
    # no critical point strictly inside (0, x_1)
    assert all(p >= x1 for p in pos), \
        f'{label}: critical point {float(min(pos))} < x_1 = {float(x1)}'

    # --- S2: a >= 0, and a == 0 iff rho >= 2 -----------------------------
    a_f = float(a)
    assert a_f >= -1e-30, f'{label}: a = {a_f} < 0, so I is not inside (0,inf)'
    if rho >= 2:
        assert sp.simplify(a) == 0, f'{label}: rho={rho} but a = {a} != 0'
        assert sp.simplify(ta - x1) == 0, f'{label}: rho>=2 but t_a != x_1'
    else:
        assert a_f > 1e-30, f'{label}: rho=1 but a = {a_f} is not positive'
        assert ta > x1, f'{label}: rho=1 but t_a = {float(ta)} <= x_1 = {float(x1)}'

    print(f'  {label}')
    print(f'      x_1={float(x1):<6.3f} rho={rho}  t_a={float(ta):<10.6f} '
          f'a={a_f:<12.8f} {"(a=0, t_a=x_1)" if rho >= 2 else "(a>0, t_a>x_1)"}')

    # --- S3 / S4: the leading t-coefficient of Q + z t^r ------------------
    D = sp.expand(Qe + z * t**r)
    dg = sp.degree(sp.Poly(D, t), t)
    lead = sp.Poly(D, t).LC()
    degQ = sp.degree(sp.Poly(Qe, t), t)
    if degQ > r:
        assert lead.free_symbols == set(), \
            f'{label}: deg Q > r but leading coeff {lead} depends on z'
        assert lead != 0
    elif degQ < r:
        assert sp.simplify(lead - z) == 0, f'{label}: deg Q < r but lead != z'
    else:
        qd = sp.Poly(Qe, t).LC()
        assert sp.simplify(lead - (qd + z)) == 0
        z_star = -qd
        # is z_* in the closed parameter interval?  b = +inf when r > 1.
        b_inf = (r > 1)
        assert b_inf, 'deg Q = r = d with max{deg Q,r} > 1 forces r >= 2, b = +inf'
        inside = (z_star >= a)
        drop_reachable.append((label, float(z_star), a_f, bool(inside), degQ % 2))

print()
print('=' * 78)
print('S3: deg Q > r => leading coefficient is a nonzero CONSTANT (no tau used)')
print('=' * 78)
print('  verified above for every deg Q > r config; the fact cited inside')
print('  thm:FT-geometry\'s proof is pure algebra, so citing lem:degree-drop')
print('  there is not circular even though lem:degree-drop\'s proof uses tau.')

print()
print('=' * 78)
print('S4: is the degree-drop branch z_* in closure(I) ever REACHED?')
print('=' * 78)
assert drop_reachable, 'no deg Q = r configuration was tested'
for label, zs, a_f, inside, d_par in drop_reachable:
    print(f'  {label}')
    print(f'      z_* = -q_d = {zs:<14.8f} a = {a_f:<12.8f} '
          f'-> z_* {"IS" if inside else "is NOT"} in closure(I)')
    # the sign of z_* = -q_d is forced by the parity of d, since
    # q_d = Q(0) (-1)^d / prod x_j with Q(0) > 0 and every x_j > 0
    assert (zs > 0) == (d_par == 1), \
        f'{label}: sign of z_* does not match the parity of d'
    if d_par == 0:
        assert not inside, \
            f'{label}: d even forces z_* < 0 <= a, so z_* cannot meet closure(I)'
assert any(ins for *_, ins, _ in drop_reachable), \
    'the z_* in closure(I) branch of lem:degree-drop is never reached: ' \
    'the case split would be vacuous'
assert any(not ins for *_, ins, _ in drop_reachable), \
    'the z_* outside closure(I) branch is never reached'
print()
print('  BOTH branches of lem:degree-drop\'s case split are reachable, so the')
print('  split is load-bearing rather than defensive.')

print()
print('PASS: (S1) rQ - tQ\' > 0 on (0,x_1), so t_a >= x_1 with equality iff rho>=2')
print('PASS: (S2) a >= 0 always, a = 0 exactly when rho >= 2; hence I inside (0,inf)')
print('PASS: (S3) deg Q > r gives a constant nonzero leading coeff; no circularity')
print('PASS: (S4) both branches of the lem:degree-drop case split are reachable')
print('ALL PASS: verify_interval_structure')
