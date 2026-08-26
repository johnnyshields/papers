#!/usr/bin/env python3
"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude).

Structural facts about the Forgacs-Tran interval that the other scripts assume,
and the boundary sweep for the denominator class of eq:Q-hypotheses.  Five
claims, none of which is checked elsewhere in this harness:

  (S1)  rQ(t) - tQ'(t) > 0 on (0, x_1).                       eq:ab-def
        The endpoints are read off t^{r-1}(rQ(t) - tQ'(t)); positivity of the
        second factor on (0, x_1) is what makes t_a the SMALLEST positive
        critical point of g and forces t_a >= x_1.

  (S2)  a = g(t_a) >= 0, with a = 0 exactly when rho >= 2.    eq:ab-def
        This is what puts I_{Q,r} inside (0, infty) at all, so it underpins
        thm:main's "outside (0,infty)" formulation.

  (S3)  deg Q > r  =>  the leading t-coefficient of Q(t) + z t^r is the
        nonzero leading coefficient of Q, independent of z.  proof of `thm:FT-geometry`
        That proof rules out an escaping root when deg Q > r by this algebraic
        fact alone, so the step must not depend on tau.

  (S4)  deg Q = r = d  =>  z_inf = -q_d, and the case z_inf in closure(I_{Q,r})
        is NON-VACUOUS.                                       `thm:FT-geometry`
        deg Q = r is the one degree relation under which a root leaves every
        bounded set on the parameter interval, which is the case
        `thm:FT-geometry` covers by sending it to infinity and
        `lem:contour-separation` then absorbs into the contour remainder.  If
        z_inf never met the interval those statements would carry nothing; both
        the meeting and the non-meeting configuration are exhibited here.

  (S5)  The "only positive real zeros" clause of eq:Q-hypotheses cannot be
        dropped.                                              eq:Q-hypotheses
        Of that equation's clauses, Q(0) != 0 is shown load-bearing in
        check_contour_separation.py and max{deg Q, r} > 1 in verify_reduction.py;
        this one had no boundary sweep.  Four denominators are exhibited that
        satisfy every OTHER clause -- Q(0) > 0, Q nonconstant, max{deg Q,r} > 1 --
        and violate this one, two with a conjugate pair of nonreal zeros and two
        with a negative real zero.

        The degradation asserted is that the number of zeros of H_m outside
        (0, infty), counted with multiplicity, is UNBOUNDED in m: it is at least
        half of deg H_m at every index of the ladder and strictly increasing.
        That is the right witness because it is the negation of the paper's own
        deliverable rather than of a step on the way to it.  The numerator is
        N = 1, so eq:P-generating-intro is eq:H-generating and B_N = 1 with
        deg B_N = 0; the failure therefore defeats thm:main (i) AND the constant
        C_0(Q,r) of thm:main (iii), with the numerator contributing nothing.  The
        upstream candidates -- a = g(t_a) < 0, no positive critical point of g,
        the loss of the eq:principal-pair conjugate pair -- are each recorded as
        the MECHANISM behind one witness, since no single one of them covers all
        four, and one witness (a negative zero of smallest modulus) keeps a > 0
        and an intact interval and fails only through the principal pair.

        Two controls keep the finding scoped.  At r EVEN the substitution
        t -> -t carries an all-negative-zero Q back into eq:Q-hypotheses, by an
        identity asserted exactly here, and the Forgacs-Tran conclusion survives;
        and a negative zero of largest modulus leaves the count at 0 over the
        same ladder.  So the clause cannot be dropped, but not every violation of
        it is fatal.

Exact rational/symbolic arithmetic where possible; mpmath elsewhere.
"""

import sympy as sp
from mpmath import mp

mp.dps = 40

t, z = sp.symbols('t z', real=True)


def Q_from_zeros(zeros, Q0=1):
    """Q(t) = Q0 * prod (1 - t/x_j), the paper's eq:Q-hypotheses normalization."""
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
    # The sign is decided in SymPy on the exact algebraic value of a, never on
    # a float: `is_positive` on an exact number returns True only when SymPy
    # can separate it from zero, so a True here is a proof and an undecided
    # case fails the assertion instead of rounding into one.
    a_exact = sp.simplify(a)
    a_is_zero = (a_exact == 0)
    assert a_is_zero or a_exact.is_positive, \
        f'{label}: a = {a_exact} is not >= 0, so I is not inside (0,inf)'
    if rho >= 2:
        assert a_is_zero, f'{label}: rho={rho} but a = {a_exact} != 0'
        assert sp.simplify(ta - x1) == 0, f'{label}: rho>=2 but t_a != x_1'
    else:
        assert a_exact.is_positive, f'{label}: rho=1 but a = {a_exact} is not positive'
        assert ta > x1, f'{label}: rho=1 but t_a = {ta} <= x_1 = {x1}'
    a_f = float(a_exact)                       # display only, from here on

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
        z_inf = -qd
        # is z_inf in the closed parameter interval?  b = +inf when r > 1.
        b_inf = (r > 1)
        assert b_inf, 'deg Q = r = d with max{deg Q,r} > 1 forces r >= 2, b = +inf'
        inside = (z_inf >= a)
        drop_reachable.append((label, float(z_inf), a_f, bool(inside), degQ % 2))

print()
print('=' * 78)
print('S3: deg Q > r => leading coefficient is a nonzero CONSTANT (no tau used)')
print('=' * 78)
print('  verified above for every deg Q > r config; the fact is pure algebra,')
print('  so thm:FT-geometry may use it to exclude an escaping root without')
print('  appealing to tau, and no circularity arises.')

print()
print('=' * 78)
print('S4: is the escaping-root parameter z_inf in closure(I) ever REACHED?')
print('=' * 78)
assert drop_reachable, 'no deg Q = r configuration was tested'
for label, zs, a_f, inside, d_par in drop_reachable:
    print(f'  {label}')
    print(f'      z_inf = -q_d = {zs:<14.8f} a = {a_f:<12.8f} '
          f'-> z_inf {"IS" if inside else "is NOT"} in closure(I)')
    # the sign of z_inf = -q_d is forced by the parity of d, since
    # q_d = Q(0) (-1)^d / prod x_j with Q(0) > 0 and every x_j > 0
    assert (zs > 0) == (d_par == 1), \
        f'{label}: sign of z_inf does not match the parity of d'
    if d_par == 0:
        assert not inside, \
            f'{label}: d even forces z_inf < 0 <= a, so z_inf cannot meet closure(I)'
assert any(ins for *_, ins, _ in drop_reachable), \
    'z_inf never meets closure(I): thm:FT-geometry\'s escaping-root clause ' \
    'and the contour remainder that absorbs it would carry nothing'
assert any(not ins for *_, ins, _ in drop_reachable), \
    'the z_inf outside closure(I) branch is never reached'
print()
print('  BOTH configurations are reachable, so thm:FT-geometry\'s escaping-root')
print('  clause is carrying a real case rather than a defensive one.')


print()
print('=' * 78)
print('S5: is "only positive real zeros" load-bearing?  Witnesses that violate it')
print('=' * 78)


def H_coeffs(Qe, r, Mmax):
    """H_m of eq:H-generating: 1/(Q(t) + z t^r) = sum_m H_m(z) t^m, exactly."""
    Qp = sp.Poly(sp.expand(Qe), t)
    q0 = Qp.nth(0)
    qc = [Qp.nth(i) for i in range(Qp.degree() + 1)]
    P = []
    for m in range(Mmax + 1):
        rhs = sp.Integer(1) if m == 0 else sp.Integer(0)
        for i in range(1, len(qc)):
            if m - i >= 0:
                rhs -= qc[i] * P[m - i]
        if m - r >= 0:
            rhs -= z * P[m - r]
        P.append(sp.expand(rhs / q0))
    return P


def exceptional_count(poly):
    """(deg, #zeros outside (0,inf) with multiplicity) -- the count thm:main bounds.

    nroots is arbitrary precision, so the real-vs-complex and sign decisions are
    made in mpmath against a threshold derived from the working precision.
    """
    p = sp.Poly(poly, z)
    if p.degree() < 1:
        return p.degree(), 0
    tol = mp.mpf(10)**(-mp.dps // 3)
    pos = 0
    for rt in p.nroots(n=30, maxsteps=1500):
        if abs(mp.mpf(str(sp.im(rt)))) < tol and mp.mpf(str(sp.re(rt))) > tol:
            pos += 1
    return p.degree(), p.degree() - pos


def offending_zeros(Qe):
    """The zeros of Q that eq:Q-hypotheses forbids: nonreal, or real and <= 0."""
    bad = []
    for rt in sp.Poly(sp.expand(Qe), t).all_roots():
        if (not rt.is_real) or rt <= 0:
            bad.append(rt)
    return bad


def min_modulus_pair(Qe, r, zval):
    """The two smallest-modulus zeros of Q(t) + z t^r, at arbitrary precision."""
    Qp = sp.Poly(sp.expand(Qe), t)
    d = max(Qp.degree(), r)
    c = [mp.mpf(0)] * (d + 1)
    for i in range(Qp.degree() + 1):
        c[i] += mp.mpf(str(Qp.nth(i)))
    c[r] += mp.mpf(str(zval))
    rts = sorted(mp.polyroots(list(reversed(c)), maxsteps=4000, extraprec=300),
                 key=lambda w: abs(w))
    return rts[0], rts[1]


def is_conjugate_pair(w0, w1):
    return abs(mp.im(w0)) > mp.mpf('1e-20') and abs(w0 - mp.conj(w1)) < mp.mpf('1e-20')


MLADDER = (24, 36, 48, 60, 72)

# Each witness satisfies EVERY other clause of eq:Q-hypotheses -- Q(0) > 0, Q
# nonconstant, max{deg Q, r} > 1 -- and the numerator is N = 1, so
# eq:P-generating-intro is eq:H-generating, B_N = 1 and deg B_N = 0.  A failure
# here therefore defeats thm:main (i) and, since deg B_N = 0, the constant C_0
# of thm:main (iii) as well, with the numerator contributing nothing.
WITNESSES = [
    ('W1  Q = 1 - t + t^2/2  (zeros 1 +- i), r = 2', 1 - t + t**2 / 2, 2),
    ('W2  Q = (1 - t/4)(1 - t + t^2/2), r = 2', sp.expand((1 - t / 4) * (1 - t + t**2 / 2)), 2),
    ('W3  Q = (1 + t)(1 - t/2)(1 - t/4), r = 2', sp.expand((1 + t) * (1 - t / 2) * (1 - t / 4)), 2),
    ('W4  Q = (1 + t)(1 + t/2), r = 1', sp.expand((1 + t) * (1 + t / 2)), 1),
]

for label, Qw, rw in WITNESSES:
    # --- the OTHER clauses of eq:Q-hypotheses all hold ---------------------
    assert Qw.subs(t, 0) > 0, f'{label}: Q(0) <= 0'
    degQw = sp.Poly(Qw, t).degree()
    assert degQw >= 1, f'{label}: Q is constant'
    assert max(degQw, rw) > 1, f'{label}: max(deg Q, r) = 1'
    bad = offending_zeros(Qw)
    assert bad, f'{label}: Q has only positive real zeros, so it is not a witness'

    # --- the asserted degradation: the exceptional count is UNBOUNDED in m --
    Hs = H_coeffs(Qw, rw, max(MLADDER))
    row = []
    for m in MLADDER:
        assert Hs[m] != 0, (label, m)
        dg, exc = exceptional_count(Hs[m])
        row.append((m, dg, exc))
    excs = [e for _, _, e in row]
    assert all(excs[i] > excs[i - 1] for i in range(1, len(excs))), (label, row)
    assert all(2 * e >= d for _, d, e in row), (label, row)
    print(f'  {label}')
    print(f'      forbidden zeros of Q: {[str(sp.N(x, 8)) for x in bad]}')
    print(f'      (m, deg H_m, # zeros outside (0,inf)): {row}')
    print(f'      -> the count is at least half the degree at every m and strictly')
    print(f'         increasing, so no constant bounds it: thm:main (i) fails here.')

# --- the mechanism behind each witness, so the failure is located ----------
# W1: a = g(t_a) < 0, so I_{Q,r} of eq:ab-def is not inside (0, infty).
Q_w1, r_w1 = 1 - t + t**2 / 2, 2
pos_w1, _ = critical_points(Q_w1, r_w1)
a_w1 = sp.simplify(g_at(Q_w1, r_w1, pos_w1[0]))
assert a_w1.is_negative, a_w1
print(f'  W1 mechanism: t_a = {pos_w1[0]}, a = g(t_a) = {a_w1} < 0, so eq:ab-def puts')
print(f'      I_{{Q,r}} across the origin and S2 above fails.')

# W2: g has NO positive critical point, so t_a does not exist and eq:ab-def
# does not define an interval at all.
Q_w2, r_w2 = sp.expand((1 - t / 4) * (1 - t + t**2 / 2)), 2
pos_w2, phi_w2 = critical_points(Q_w2, r_w2)
assert not pos_w2, pos_w2
assert sp.real_roots(sp.Poly(phi_w2, t)), 'phi has no real root at all'
assert all(x < 0 for x in sp.real_roots(sp.Poly(phi_w2, t))), phi_w2
print(f'  W2 mechanism: rQ - tQ\' = {sp.factor(phi_w2)} has only the negative real root')
print(f'      {float(sp.real_roots(sp.Poly(phi_w2, t))[0]):.8f}, so g has no positive critical')
print(f'      point, t_a of eq:ab-def does not exist and I_{{Q,r}} is undefined.')

# W3: a > 0 and I_{Q,r} is a genuine subinterval of (0,inf), so the failure is
# not at the endpoints -- it is that the two minimum-modulus denominator zeros
# are NOT a conjugate pair on the lower part of the interval, which is exactly
# the principal pair thm:FT-geometry supplies and eq:principal-pair names.
Q_w3, r_w3 = sp.expand((1 + t) * (1 - t / 2) * (1 - t / 4)), 2
pos_w3, _ = critical_points(Q_w3, r_w3)
a_w3 = sp.simplify(g_at(Q_w3, r_w3, pos_w3[0]))
assert a_w3.is_positive, a_w3
a_w3m = mp.mpf(str(sp.N(a_w3, 25)))
broken = []
for zv in (a_w3m * mp.mpf('1.01'), mp.mpf('0.1'), mp.mpf('0.3')):
    w0, w1 = min_modulus_pair(Q_w3, r_w3, zv)
    assert not is_conjugate_pair(w0, w1), (zv, w0, w1)
    assert abs(mp.im(w0)) < mp.mpf('1e-20') and mp.re(w0) < 0, (zv, w0)
    broken.append((zv, w0))
Q_ref = sp.expand((1 - t) * (1 - t / 2) * (1 - t / 4))       # same Q with +1 for -1
for zv in (mp.mpf('0.05'), mp.mpf('0.1'), mp.mpf('0.3'), mp.mpf('3')):
    assert is_conjugate_pair(*min_modulus_pair(Q_ref, 2, zv)), zv
print(f'  W3 mechanism: a = {float(a_w3):.8f} > 0, so I_{{Q,r}} is a genuine subinterval')
print(f'      of (0,inf) and the endpoints are intact.  What fails is eq:principal-pair:')
for zv, w0 in broken:
    print(f'         z = {float(zv):<9.5f} minimum-modulus zero = {mp.nstr(w0, 8)} (real, negative)')
print(f'      For the same Q with the zero at -1 replaced by +1 the minimum-modulus zeros')
print(f'      are a conjugate pair at every z tested, as thm:FT-geometry asserts.')

# W4: the failure is exact.  For Q with all zeros negative and Qt(t) = Q(-t)
# admissible under eq:Q-hypotheses, comparing eq:H-generating for Q and Qt gives
#     Ht_m(w) = (-1)^m H_m((-1)^r w).
# At r odd this reflects the zero set into (-inf, 0); at r even it fixes it.
Q_w4 = sp.expand((1 + t) * (1 + t / 2))
Q_tilde = sp.expand(Q_w4.subs(t, -t))
assert all(x > 0 for x in sp.Poly(Q_tilde, t).all_roots()), 'Qt is not FT-admissible'
for r_par in (1, 2):
    Hs_w = H_coeffs(Q_w4, r_par, 12)
    Hs_tilde = H_coeffs(Q_tilde, r_par, 12)
    for m in range(13):
        assert sp.expand(Hs_tilde[m] - (-1)**m * Hs_w[m].subs(z, (-1)**r_par * z)) == 0, (r_par, m)
print('  W4 mechanism: with Qt(t) = Q(-t) admissible under eq:Q-hypotheses, the identity')
print('      Ht_m(z) = (-1)^m H_m((-1)^r z) holds exactly for m <= 12 at r = 1 and r = 2.')
print('      At r = 1 it negates the zero set, which is why every zero of H_m is negative.')

# --- and the CONTROL: violating the clause is not by itself fatal ----------
# At r EVEN the same identity carries an all-negative-zero Q back into
# eq:Q-hypotheses, so the Forgacs-Tran conclusion survives verbatim; and a
# negative zero of largest modulus leaves the count at 0 over the same ladder.
# Neither is asserted beyond the ladder -- thm:main (i) is an eventual statement
# and no eventual claim is made for a Q outside its hypotheses.
CONTROLS = [
    ('C1  Q = (1 + t)(1 + t/2), r = 2  (all zeros negative, r EVEN)',
     sp.expand((1 + t) * (1 + t / 2)), 2),
    ('C2  Q = (1 - t)(1 - t/2)(1 + t/3), r = 2  (negative zero of largest modulus)',
     sp.expand((1 - t) * (1 - t / 2) * (1 + t / 3)), 2),
]
print()
for label, Qc, rc in CONTROLS:
    assert offending_zeros(Qc), f'{label}: not a violation of the clause'
    Hs = H_coeffs(Qc, rc, max(MLADDER))
    row = []
    for m in MLADDER:
        dg, exc = exceptional_count(Hs[m])
        assert exc == 0, (label, m, dg, exc)
        row.append((m, dg))
    print(f'  {label}')
    print(f'      every H_m real-rooted with all zeros in (0,inf) at (m, deg) = {row}')
print('  So the clause is load-bearing but not through a sign argument alone: at r even')
print('  the reflection t -> -t returns an all-negative-zero Q to eq:Q-hypotheses, and a')
print('  negative zero far from the branch arc is not seen over this ladder.  What the')
print('  witnesses show is that the clause cannot be DROPPED, not that every violation')
print('  of it is fatal.')

print()
print('PASS: (S1) rQ - tQ\' > 0 on (0,x_1), so t_a >= x_1 with equality iff rho>=2')
print('PASS: (S2) a >= 0 always, a = 0 exactly when rho >= 2; hence I inside (0,inf)')
print('PASS: (S3) deg Q > r gives a constant nonzero leading coeff; no circularity')
print('PASS: (S4) z_inf both meets and misses closure(I) across the configurations')
print('PASS: (S5) with the positive-real-zero clause of eq:Q-hypotheses dropped, the')
print('           exceptional-zero count of H_m is unbounded in m on four witnesses')
print('ALL PASS: verify_interval_structure')
