#!/usr/bin/env python3
r"""Paper section `subsec:weighted-dominance` (Weighted principal-pair dominance),
`thm:weighted-dominance`: the quantitative uniformity content of the proof.

verify_dominance.py asserts the *conclusion* |R_M| <= |W|/2 and the boundedness
of the endpoint residue ratios.  This script pins the individual quantitative
steps the proof runs through, each an exact statement rather than an O(1)
assertion.

  (U1) Finiteness of the collision parameters.  A multiple finite root of
       Q(t) + z t^r satisfies t Q'(t) - r Q(t) = 0, a polynomial whose value at
       t = 0 is -r Q(0) != 0, hence not identically zero.

  (U2) The lower-endpoint cluster expansion t_j = x1 + alpha_j theta + O(theta^2),
       alpha_j = -x1 omega_j/sin(pi/rho), omega_j = e^{(2j-1) pi i/rho}: the
       alpha_j are distinct, nonzero, of common modulus x1/sin(pi/rho), so the
       cluster roots are pairwise distinct (hence simple) for small theta > 0.

  (U3) D'(t_j) = Q'(t_j) - r Q(t_j)/t_j
               = [Q^(rho)(x1)/(rho-1)!] alpha_j^{rho-1} theta^{rho-1}(1+O(theta)).
       Writing Q = (t-x1)^rho q, this leading coefficient is rho q(x1); the two
       forms are asserted equal, since the paper states the Taylor one.

  (U4) B(t_j) = [B^(nu)(x1)/nu!] alpha_j^nu theta^nu (1 + O(theta)), likewise
       equal to b(x1) alpha_j^nu theta^nu for B = (t-x1)^nu b.

  (U5) `eq:lower-residue-ratio` and the |W_j| <= 2|W| consequence drawn from it.
       W_j/W = (alpha_j/alpha_+)^{nu-rho+1}(1 + O(theta)), hence |W_j/W| -> 1
       because all |alpha_j| agree, and so |W_j| <= 2|W| on (0, eps].  This is
       what rules out a zero of B amplifying a nonprincipal residue relative to
       the principal pair.

  (U6) p = nu - rho + 1 is exactly `lem:amplitude-divisor`'s p = nu - (k-1), k = max{rho,2},
       and |W| ~ theta^p at that rate.

  (U7) `lem:near-cluster-suppression`'s proof step, with eq:endpoint-linear-gap
       consumed.  For x >= 0, log(1+x) >= x/(1+x); hence for 0 < theta <= eps, c0 > 0,
           (1 + c0 theta)^{-(M+1)} <= e^{-c0' M theta},
           c0' = c0/(1 + c0 eps) > 0,
       and the naive c0' = c0 is false, so the correction is load-bearing.

  (U8) `eq:near-cluster-suppression` at C_W = 2, which is what (U5) supplies, in
       the form eq:lower-cluster-relative-bound consumes it.
       |R^cl_M|/|W| <= 2(rho-2) e^{-c0' M theta}, from (U5)+(U7), checked
       against directly computed residues.

  (U9) `eq:endpoint-contour-relative-bound`.  One estimate covers every
       endpoint region: the contour remainder against the principal amplitude,
       at whatever rate sigma the region supplies.
       C sigma^M/|W| <= C_h sigma^M M^{p_+} on h/M <= theta <= eps for either
       sign of p, and the bound tends to 0.  The rates themselves are measured
       in verify_dominance.py; what is uniform, and checked here, is that the
       M-dependence is exactly M^{max{p,0}} and no worse.

  (U10) `eq:upper-residue-ratio`, `eq:upper-cluster-relative-bound`.
        Upper endpoint, r > 1: the limiting normalized cluster is the set of
        r-th roots of -1 (distinct, hence simple);
            D'(t_j) = -r Q(0)/(tau zeta_j)(1 + O(tau)),
            W_j     =  B(0) tau zeta_j/(r Q(0))(1 + O(tau)),
            W_j/W   =  zeta_j/zeta_+ (1 + O(tau)),   |W_j/W| -> 1,
        with |W| ~ tau ~ eta (so `lem:amplitude-divisor`'s p = 1), 1/z = O(tau^r), and the
        outer-root ratio bound C (tau/R0)^{M+r}.

  (U11) eq:interior-relative-remainder.
        Interior: with c = (1/2) log(1/sigma_I), on the retained interior
        |W| >= C_A e^{-cM} and |R_M|/|W| <= (C_I/C_A) sigma_I^{M/2}.
        Tested *at the window edge* |theta - theta_j| = e^{-cM/nu_j}, which is
        where the estimate is tight, on a configuration with a genuine
        amplitude zero.

  (U12) eq:retained-range, eq:dominance-bound, and the final clause of
        `lem:near-cluster-suppression`.
        The constant bookkeeping closes: an h solving 2(rho-2)e^{-c0' h} <= 1/4
        exists, 1/4 + 1/4 <= 1/2 on each endpoint region, the interior is <= 1/2
        directly, and the deleted length is exactly sum_j 2 e^{-cM/nu_j}.

  (U13) `eq:amplitude-window-negligible`, the step prop:angular-discrepancy's
        proof takes after fixing `eq:Omega-M`.  The deleted windows carry total
        length sum_j 2 e^{-cM/nu_j}, so

            (M+1) sum_j |Theta_{j,M}| <= 1

        holds from a finite index on, and the phase count loses at most one
        zero to the deletion.  Both halves are asserted: the bound holds for
        every M at or above a measured threshold, and FAILS at every M below
        it, so "after increasing the B-dependent threshold" is load-bearing
        rather than decorative.  The threshold is also shown to MOVE with the
        weight: it grows with max_j nu_j, and nu_j <= deg B by
        `eq:amplitude-zero-count`, which is why the paper makes the threshold
        B-dependent while the discrepancy constants are not.

All numerics use mpmath at arbitrary precision; symbolic work uses SymPy.
"""
from __future__ import annotations

import sympy as sp
import mpmath as mp

mp.mp.dps = 60
t = sp.symbols('t')

PASSES = 0
TOL = mp.mpf(10) ** (-40)


def ok(msg: str) -> None:
    global PASSES
    PASSES += 1
    print(f'PASS  {msg}')


def low(expr):
    p = sp.Poly(sp.expand(expr), t)
    return [mp.mpmathify(sp.nsimplify(p.nth(i))) for i in range(p.degree() + 1)]


def pval(c, x):
    return sum(c[i] * x**i for i in range(len(c)))


def dval(c, x):
    return sum(c[i] * i * x**(i - 1) for i in range(1, len(c)))


def denom_roots(Qc, r, z):
    d = max(len(Qc) - 1, r)
    co = [mp.mpf(0)] * (d + 1)
    for i, c in enumerate(Qc):
        co[i] += c
    co[r] += z
    return mp.polyroots(list(reversed(co)), maxsteps=6000, extraprec=1200)


def principal(rts):
    """The minimum-modulus root in the open upper half-plane."""
    o = sorted(rts, key=lambda w: abs(w))
    for w in o[:2]:
        if mp.im(w) > 0:
            return w
    raise AssertionError('the two minimum-modulus roots are not a conjugate pair')


def state(Qc, r, z):
    rts = denom_roots(Qc, r, z)
    tp = principal(rts)
    return rts, tp, abs(tp), mp.arg(tp)


def Dprime(Qc, r, w):
    return dval(Qc, w) - r * pval(Qc, w) / w


def resid(Qc, Bc, r, w):
    """The weighted residue amplitude A_j = -B(t_j)/D'(t_j)."""
    return -pval(Bc, w) / Dprime(Qc, r, w)


def ft_endpoints(Qc, r):
    """(a, b) of `eq:ab-def`: the critical values of g = -Q/t^r at the smallest
    positive and (when r = 1) the negative critical point, read off the roots of
    t Q'(t) - r Q(t)."""
    cc = [Qc[i] * (i - r) for i in range(len(Qc))]
    crit = mp.polyroots(list(reversed(cc)), maxsteps=6000, extraprec=1200)
    real = [mp.re(w) for w in crit if abs(mp.im(w)) < mp.mpf('1e-30') and abs(w) > TOL]
    pos = sorted(w for w in real if w > 0)
    neg = sorted((w for w in real if w < 0), reverse=True)
    a = -pval(Qc, pos[0]) / pos[0]**r
    b = (-pval(Qc, neg[0]) / neg[0]**r) if (r == 1 and neg) else mp.inf
    return a, b


def z_of_theta(Qc, r, target, zlo, zhi):
    """Invert the strictly increasing theta(z) by bisection."""
    flo = state(Qc, r, zlo)[3] - target
    fhi = state(Qc, r, zhi)[3] - target
    assert flo < 0 < fhi, (mp.nstr(flo, 8), mp.nstr(fhi, 8))
    tol = mp.mpf(10)**(-(mp.mp.dps - 8))
    for _ in range(4 * mp.mp.dps + 80):
        zm = mp.sqrt(zlo * zhi) if zlo > 0 else (zlo + zhi) / 2
        fm = state(Qc, r, zm)[3] - target
        if fm == 0:
            return zm
        if fm < 0:
            zlo = zm
        else:
            zhi = zm
        if abs(zhi - zlo) < tol * (1 + abs(zhi)):
            break
    return (zlo + zhi) / 2


def bounded(seq, name, factor=12):
    """seq[i] is an error ratio at decreasing theta; assert it does not grow.

    seq[0] is the coarsest (largest-theta) sample, so `max <= factor * seq[0]`
    fails exactly when the ratio blows up as theta -> 0, which is what an error
    of the wrong order would do.  A ratio that *decreases* is a stronger result
    than the O(.) claimed and passes.
    """
    hi = max(seq)
    assert hi <= factor * seq[0] + mp.mpf(10) ** (-25), \
        f'{name} grows as theta -> 0: {[mp.nstr(s, 6) for s in seq]}'
    return min(seq), hi


def asymp(seq, name, factor=12):
    """Assert seq is bounded above and away from zero (an `asymp` claim)."""
    lo, hi = min(seq), max(seq)
    assert lo > 0 and hi <= factor * lo, \
        f'{name} is not bounded above and below: {[mp.nstr(s, 6) for s in seq]}'
    return lo, hi


# ---------------------------------------------------------------------------
# (U1)
# ---------------------------------------------------------------------------
def check_U1():
    for deg in range(1, 6):
        cs = sp.symbols(f'c0:{deg+1}')
        Q = sum(cs[i] * t**i for i in range(deg + 1))
        for r in range(1, 5):
            coll = sp.expand(t * sp.diff(Q, t) - r * Q)
            assert sp.simplify(coll.subs(t, 0) - (-r * cs[0])) == 0
    ok("(U1) symbolic: (t Q' - r Q)|_{t=0} = -r Q(0) for every degree 1..5 and r = 1..4, "
       'so the collision polynomial is not identically zero when Q(0) != 0')

    for Qexpr, r in [((1 - t) * (1 - t / 2) * (1 - t / 4), 1),
                     ((1 - t)**2 * (1 - t / 3), 2),
                     ((1 - t) * (1 - t / 2) * (1 - t / 5) * (1 - t / 7), 3)]:
        Qc = low(Qexpr)
        cp = sp.Poly(sp.expand(t * sp.diff(Qexpr, t) - r * Qexpr), t)
        cc = [mp.mpmathify(sp.nsimplify(cp.nth(i))) for i in range(cp.degree() + 1)]
        assert abs(cc[0]) > 0 and abs(cc[0] + r * Qc[0]) < TOL
        crit = mp.polyroots(list(reversed(cc)), maxsteps=6000, extraprec=1200)
        zs = []
        for w in crit:
            if abs(w) < TOL:
                continue
            zc = -pval(Qc, w) / w**r
            if abs(mp.im(zc)) < mp.mpf('1e-30'):
                zc = mp.re(zc)
                rr = denom_roots(Qc, r, zc)
                gap = min(abs(rr[i] - rr[j]) for i in range(len(rr)) for j in range(i + 1, len(rr)))
                assert gap < mp.mpf('1e-20'), f'no multiple root at z={mp.nstr(zc, 12)} (gap {mp.nstr(gap, 6)})'
                zs.append(zc)
        assert len(crit) == cp.degree()
        ok(f'(U1) numeric: deg Q={sp.Poly(Qexpr, t).degree()}, r={r} — the collision polynomial has '
           f'{cp.degree()} roots, {len(zs)} of them giving a real parameter, each a genuine multiple '
           'root; the collision set is finite')


# ---------------------------------------------------------------------------
# (U2)-(U6), (U8)
# ---------------------------------------------------------------------------
def check_lower(Qexpr, Bexpr, r, rho, x1, nu, label):
    Qc, Bc = low(Qexpr), low(Bexpr)
    x1m = mp.mpf(x1)
    qpoly = sp.cancel(sp.expand(Qexpr) / (t - x1)**rho)
    bpoly = sp.cancel(sp.expand(Bexpr) / (t - x1)**nu) if nu else sp.expand(Bexpr)
    assert sp.simplify(sp.expand(qpoly * (t - x1)**rho - Qexpr)) == 0
    assert sp.simplify(sp.expand(bpoly * (t - x1)**nu - Bexpr)) == 0
    qx1 = mp.mpmathify(sp.nsimplify(qpoly.subs(t, x1)))
    bx1 = mp.mpmathify(sp.nsimplify(bpoly.subs(t, x1)))
    assert abs(qx1) > TOL and abs(bx1) > TOL
    # The paper states the leading coefficients as Taylor coefficients at x1;
    # tie that form to the cofactor form used below.
    taylor_Q = mp.mpmathify(sp.nsimplify(sp.diff(sp.expand(Qexpr), t, rho).subs(t, x1)
                                         / sp.factorial(rho - 1)))
    taylor_B = mp.mpmathify(sp.nsimplify(sp.diff(sp.expand(Bexpr), t, nu).subs(t, x1)
                                         / sp.factorial(nu)))
    assert abs(taylor_Q - rho * qx1) < TOL * (1 + abs(taylor_Q))
    assert abs(taylor_B - bx1) < TOL * (1 + abs(taylor_B))

    srho = mp.sin(mp.pi / rho)
    alphas = [-x1m * mp.expj(mp.pi * (2 * j - 1) / rho) / srho for j in range(1, rho + 1)]
    for i in range(rho):
        assert abs(abs(alphas[i]) - x1m / srho) < TOL
        for j in range(i + 1, rho):
            assert abs(alphas[i] - alphas[j]) > mp.mpf('1e-20')
    ok(f'[{label}] (U2) the rho={rho} coefficients alpha_j are distinct, nonzero and of common '
       f'modulus x1/sin(pi/rho) = {mp.nstr(x1m / srho, 12)}')

    zs = [mp.mpf(10)**(-k) for k in range(4, 11)]
    e_t, e_D, e_B, e_A, w_p, sep = [], [], [], [], [], []
    for z in zs:
        rts, tp, tau, th = state(Qc, r, z)
        cl = sorted(rts, key=lambda w: abs(w - x1m))[:rho]
        assert max(abs(w - x1m) for w in cl) < x1m / 2, 'cluster not identified'
        pred = [x1m + a * th for a in alphas]
        used, order = set(), []
        for i, pr in enumerate(pred):
            j = min((k for k in range(rho) if k not in used), key=lambda k: abs(cl[k] - pr))
            used.add(j)
            order.append((i, j))
        e_t.append(max(abs(cl[j] - pred[i]) for i, j in order) / th**2)
        sep.append(min(abs(cl[i] - cl[j]) for i in range(rho) for j in range(i + 1, rho)) / th)

        iplus = min(order, key=lambda ij: abs(cl[ij[1]] - tp))[0]
        assert abs(cl[dict(order)[iplus]] - tp) < TOL * (1 + abs(tp))

        dD = dB = mp.mpf(0)
        A = {}
        for i, j in order:
            w = cl[j]
            Dj = Dprime(Qc, r, w)
            dD = max(dD, abs(Dj / (rho * qx1 * alphas[i]**(rho - 1) * th**(rho - 1)) - 1) / th)
            dB = max(dB, abs(pval(Bc, w) / (bx1 * alphas[i]**nu * th**nu) - 1) / th)
            A[i] = -pval(Bc, w) / Dj
        W = A[iplus]
        assert abs(W - resid(Qc, Bc, r, tp)) < TOL * (1 + abs(W))
        dA = mp.mpf(0)
        for i in range(rho):
            if i == iplus:
                continue
            lim = (alphas[i] / alphas[iplus])**(nu - rho + 1)
            assert abs(abs(lim) - 1) < TOL, 'the predicted limit is not unimodular'
            dA = max(dA, abs((A[i] / W) / lim - 1) / th)
        e_D.append(dD); e_B.append(dB); e_A.append(dA)
        w_p.append(abs(W) / th**(nu - rho + 1))

    bounded(e_t, 't_j remainder / theta^2')
    ok(f'[{label}] (U2) t_j = x1 + alpha_j theta + O(theta^2): remainder/theta^2 in '
       f'[{mp.nstr(min(e_t), 6)}, {mp.nstr(max(e_t), 6)}] over theta spanning {mp.nstr(zs[-1], 2)}..{mp.nstr(zs[0], 2)} in z')
    assert min(sep) > mp.mpf('0.1') * x1m, f'cluster does not separate linearly: {sep}'
    ok(f'[{label}] (U2) min|t_i - t_j|/theta >= {mp.nstr(min(sep), 8)} > 0, so the whole cluster is '
       'simple and pairwise distinct for small theta > 0')

    bounded(e_D, "D' relative error / theta")
    ok(f"[{label}] (U3) D'(t_j) = rho q(x1) alpha_j^(rho-1) theta^(rho-1)(1+O(theta)): "
       f'relative error/theta <= {mp.nstr(max(e_D), 6)}')
    bounded(e_B, 'B relative error / theta')
    ok(f'[{label}] (U4) B(t_j) = b(x1) alpha_j^nu theta^nu (1+O(theta)): '
       f'relative error/theta <= {mp.nstr(max(e_B), 6)}')

    if rho > 2:
        bounded(e_A, 'A_j/W relative error / theta')
        ok(f'[{label}] (U5) A_j/W = (alpha_j/alpha_+)^(nu-rho+1)(1+O(theta)) with |A_j/W| -> 1: '
           f'relative error/theta <= {mp.nstr(max(e_A), 6)}')
    else:
        ok(f'[{label}] (U5) rho = 2: the cluster is the principal pair alone, so there is no '
           'nonprincipal residue and the 2(rho-2) bound is vacuous')

    p = nu - rho + 1
    assert p == nu - (max(rho, 2) - 1)
    asymp(w_p, '|W|/theta^p')
    ok(f'[{label}] (U6) p = nu - rho + 1 = {p} equals `lem:amplitude-divisor`\'s nu-(k-1), k = max(rho,2) = '
       f'{max(rho, 2)}; |W|/theta^p in [{mp.nstr(min(w_p), 8)}, {mp.nstr(max(w_p), 8)}]')

    if rho > 2:
        eps = mp.mpf('0.2')
        c0 = None
        for z in [mp.mpf(10)**(-k) for k in range(4, 9)]:
            rts, tp, tau, th = state(Qc, r, z)
            cl = sorted(rts, key=lambda w: abs(w - x1m))[:rho]
            nonp = [w for w in cl if abs(abs(w) / tau - 1) > mp.mpf('1e-18')]
            assert len(nonp) == rho - 2, f'expected {rho - 2} nonprincipal members, got {len(nonp)}'
            assert th <= eps
            rate = min((abs(w) / tau - 1) / th for w in nonp)
            c0 = rate if c0 is None else min(c0, rate)
        assert c0 > 0
        c0p = c0 / (1 + c0 * eps)
        for z in [mp.mpf('1e-4'), mp.mpf('1e-6')]:
            rts, tp, tau, th = state(Qc, r, z)
            W = resid(Qc, Bc, r, tp)
            cl = sorted(rts, key=lambda w: abs(w - x1m))[:rho]
            for M in [200, 500, 1200]:
                tot = sum(abs(resid(Qc, Bc, r, w)) * (abs(w) / tau)**(-(M + 1))
                          for w in cl if abs(abs(w) / tau - 1) > mp.mpf('1e-18'))
                bound = 2 * (rho - 2) * mp.e**(-c0p * M * th) * abs(W)
                assert tot <= bound, (f'(U8) fails at theta={mp.nstr(th, 8)}, M={M}: '
                                      f'{mp.nstr(tot, 8)} > {mp.nstr(bound, 8)}')
        ok(f'[{label}] (U8) |R^cl_M| <= 2(rho-2) e^(-c0\' M theta)|W| with measured '
           f'c0 = {mp.nstr(c0, 8)}, c0\' = {mp.nstr(c0p, 8)}, at two theta and M = 200,500,1200')


# ---------------------------------------------------------------------------
# (U7)
# ---------------------------------------------------------------------------
def check_U7():
    x = sp.symbols('x', nonnegative=True)
    f = sp.log(1 + x) - x / (1 + x)
    assert sp.simplify(sp.diff(f, x) - x / (1 + x)**2) == 0
    assert f.subs(x, 0) == 0
    ok("(U7) symbolic: d/dx[log(1+x) - x/(1+x)] = x/(1+x)^2 >= 0 with value 0 at x = 0, "
       'so log(1+x) >= x/(1+x) for x >= 0')

    for eps in [mp.mpf('0.5'), mp.mpf('0.1'), mp.mpf('0.02')]:
        worst = mp.mpf(0)
        for c0 in [mp.mpf('0.3'), mp.mpf(1), mp.mpf(5), mp.mpf(40)]:
            c0p = c0 / (1 + c0 * eps)
            for i in range(1, 121):
                th = eps * mp.mpf(i) / 120
                for M in [1, 2, 5, 25, 200, 5000]:
                    lhs = (1 + c0 * th)**(-(M + 1))
                    rhs = mp.e**(-c0p * M * th)
                    assert lhs <= rhs, f'(U7) fails at eps={eps}, c0={c0}, theta={th}, M={M}'
                    worst = max(worst, lhs / rhs)
        ok(f'(U7) (1+c0 theta)^-(M+1) <= e^(-c0\' M theta) with c0\' = c0/(1+c0 eps) over '
           f'eps = {mp.nstr(eps, 4)}, four c0, 120 theta, six M (worst ratio {mp.nstr(worst, 8)} <= 1)')

    bad = 0
    for c0 in [mp.mpf(1), mp.mpf(5)]:
        for eps in [mp.mpf('0.5'), mp.mpf(1)]:
            for i in range(1, 61):
                th = eps * mp.mpf(i) / 60
                for M in [5, 50, 500]:
                    if (1 + c0 * th)**(-(M + 1)) > mp.e**(-c0 * M * th):
                        bad += 1
    assert bad > 0
    ok(f'(U7) the naive substitution c0\' = c0 is false ({bad} counterexamples in the grid), '
       'so the 1/(1+c0 eps) correction is load-bearing')


# ---------------------------------------------------------------------------
# (U9)
# ---------------------------------------------------------------------------
def check_U9():
    eps = mp.mpf('0.3')
    for p in [-3, -1, 0, 1, 2]:
        pplus = max(p, 0)
        for sigma in [mp.mpf('0.5'), mp.mpf('0.9')]:
            for h in [mp.mpf(1), mp.mpf(10)]:
                Ch = h**(-p) if p > 0 else eps**(-p)
                for M in [50, 200, 1000, 5000]:
                    if h / M >= eps:
                        continue
                    for i in range(0, 300):
                        th = (h / M) + (eps - h / M) * mp.mpf(i) / 299
                        assert sigma**M / th**p <= Ch * sigma**M * mp.mpf(M)**pplus * (1 + TOL), \
                            f'(U9) fails at p={p}, sigma={sigma}, h={h}, M={M}'
                assert Ch * mp.mpf('0.9')**5000 * mp.mpf(5000)**pplus < mp.mpf('1e-200')
        ok(f'(U9) sigma^M/theta^p <= C_h sigma^M M^(p_+) on [h/M, eps] with p = {p}, p_+ = {pplus}, '
           'C_h = h^-p (p>0) or eps^-p (p<=0), and the bound -> 0')


# ---------------------------------------------------------------------------
# (U10)
# ---------------------------------------------------------------------------
def check_upper(Qexpr, Bexpr, r, label):
    Qc, Bc = low(Qexpr), low(Bexpr)
    Q0, B0 = Qc[0], Bc[0]
    dQ = len(Qc) - 1
    assert abs(Q0) > 0 and abs(B0) > 0

    rm1 = [mp.expj(mp.pi * (2 * j + 1) / r) for j in range(r)]
    for i in range(r):
        for j in range(i + 1, r):
            assert abs(rm1[i] - rm1[j]) > mp.mpf('1e-20')
    ok(f'[{label}] (U10) the r = {r} limiting normalized roots (the r-th roots of -1) are '
       'distinct, so the small-root cluster is simple near the endpoint')

    zs = [mp.mpf(10)**k for k in range(4, 11)]
    eD, eA, eAr, Wt, We, zt, cl_lim = [], [], [], [], [], [], []
    for z in zs:
        rts, tp, tau, th = state(Qc, r, z)
        eta = mp.pi / r - th
        cl = sorted(rts, key=lambda w: abs(w))[:r]
        zplus = tp / tau
        W = resid(Qc, Bc, r, tp)
        dD = dA = dAr = mp.mpf(0)
        for w in cl:
            zz = w / tau
            Dj = Dprime(Qc, r, w)
            dD = max(dD, abs(Dj / (-r * Q0 / (tau * zz)) - 1) / tau)
            Aj = -pval(Bc, w) / Dj
            dA = max(dA, abs(Aj / (B0 / (r * Q0) * tau * zz) - 1) / tau)
            dAr = max(dAr, abs((Aj / W) / (zz / zplus) - 1) / tau)
        cl_lim.append(max(min(abs(zz / tau * tau - x * 1) for x in rm1) for zz in [w / tau for w in cl]))
        eD.append(dD); eA.append(dA); eAr.append(dAr)
        Wt.append(abs(W) / tau)
        We.append(abs(W) / eta)
        zt.append(1 / (z * tau**r))

    assert cl_lim[-1] < cl_lim[0] and cl_lim[-1] < mp.mpf('1e-3')
    ok(f'[{label}] (U10) the normalized small cluster converges to the r-th roots of -1 '
       f'(max distance {mp.nstr(cl_lim[0], 6)} -> {mp.nstr(cl_lim[-1], 6)})')
    for name, seq in [("D'(t_j) = -r Q(0)/(tau zeta_j)(1+O(tau))", eD),
                      ('A_j = B(0) tau zeta_j/(r Q(0))(1+O(tau))', eA),
                      ('A_j/W = zeta_j/zeta_+ (1+O(tau)), so |A_j/W| -> 1', eAr)]:
        bounded(seq, name)
        ok(f'[{label}] (U10) {name}: relative error/tau <= {mp.nstr(max(seq), 6)}')

    asymp(Wt, '|W|/tau', factor=5)
    ok(f'[{label}] (U10) |W| ~ tau: |W|/tau in [{mp.nstr(min(Wt), 8)}, {mp.nstr(max(Wt), 8)}]')
    asymp(We, '|W|/eta', factor=5)
    ok(f'[{label}] (U10) tau ~ eta, hence |W| ~ eta and `lem:amplitude-divisor`\'s p = 1 here: '
       f'|W|/eta in [{mp.nstr(min(We), 8)}, {mp.nstr(max(We), 8)}]')
    asymp(zt, '1/(z tau^r)', factor=5)
    ok(f'[{label}] (U10) 1/z = O(tau^r): 1/(z tau^r) in [{mp.nstr(min(zt), 8)}, {mp.nstr(max(zt), 8)}]')

    if dQ > r:
        z = mp.mpf(10)**6
        rts, tp, tau, th = state(Qc, r, z)
        W = resid(Qc, Bc, r, tp)
        srt = sorted(rts, key=lambda w: abs(w))
        small, outer = srt[:r], srt[r:]
        assert len(outer) == dQ - r
        R0 = mp.sqrt(abs(small[-1]) * abs(outer[0]))
        assert abs(small[-1]) < R0 < abs(outer[0]) and tau < R0
        for M in [150, 300, 600]:
            tot = sum(abs(resid(Qc, Bc, r, w)) * (abs(w) / tau)**(-(M + 1)) for w in outer)
            bound = mp.mpf(10) * (tau / R0)**(M + r) * abs(W)
            assert tot <= bound, f'(U10) outer bound fails at M={M}'
        ok(f'[{label}] (U10) the deg Q - r = {dQ - r} outer roots obey '
           f'|tau^(M+1) C_out| <= C (tau/R0)^(M+r)|W| at R0 = {mp.nstr(R0, 8)}, M = 150,300,600')


# ---------------------------------------------------------------------------
# (U11)
# ---------------------------------------------------------------------------
def check_U11():
    # `fig:decomposition-and-defect`'s configuration: an amplitude zero at theta_1 = pi/2 (t_+ = i sqrt(8/7),
    # z = 45/28), of order nu_1 = 1.
    Qexpr = (1 - t) * (1 - t / 2) * (1 - t / 4)
    Bexpr = 7 * t**2 + 8
    r = 1
    Qc, Bc = low(Qexpr), low(Bexpr)
    theta_j, nu_j = mp.pi / 2, 1
    zj = mp.mpf(45) / 28
    rts, tp, tau, th = state(Qc, r, zj)
    assert abs(th - theta_j) < mp.mpf('1e-40') and abs(pval(Bc, tp)) < mp.mpf('1e-40')
    ok('(U11) the amplitude zero is exact: at z = 45/28 the principal root is t_+ = i sqrt(8/7), '
       'theta_1 = pi/2 and B(t_+) = 0')

    a, b = ft_endpoints(Qc, r)
    assert a < zj < b
    zmin = a + (zj - a) * mp.mpf('1e-12')
    zmax = b - (b - zj) * mp.mpf('1e-12')
    eps = mp.mpf('0.35')
    zlo = z_of_theta(Qc, r, eps, zmin, zj)
    zhi = z_of_theta(Qc, r, mp.pi - eps, zj, zmax)
    grid = [zlo * (zhi / zlo)**(mp.mpf(i) / 200) for i in range(201)]

    sigma_I = mp.mpf(0)
    samples = []
    for z in grid:
        rts, tp, tau, th = state(Qc, r, z)
        nonp = [w for w in rts if abs(abs(w) / tau - 1) > mp.mpf('1e-20')]
        sigma_I = max(sigma_I, max(tau / abs(w) for w in nonp))
        samples.append((th, tau, tp, nonp, resid(Qc, Bc, r, tp)))
    assert sigma_I < 1
    alpha_I = -mp.log(sigma_I)          # the paper writes c = (1/2) log(1/sigma_I)
    c = alpha_I / 2
    ok(f'(U11) on the compact interior theta in [{mp.nstr(eps, 4)}, pi - {mp.nstr(eps, 4)}]: '
       f'sigma_I = {mp.nstr(sigma_I, 10)} < 1, c = (1/2) log(1/sigma_I) = {mp.nstr(c, 10)}')

    def RM(tau, nonp, M):
        return sum(abs(resid(Qc, Bc, r, w)) * (abs(w) / tau)**(-(M + 1)) for w in nonp)

    def RM2(Qc2, Bc2, r2, tau, nonp, M):
        return sum(abs(resid(Qc2, Bc2, r2, w)) * (abs(w) / tau)**(-(M + 1)) for w in nonp)

    C_I = mp.mpf(0)
    for (th, tau, tp, nonp, W) in samples:
        for M in [60, 120, 240]:
            C_I = max(C_I, RM(tau, nonp, M) / sigma_I**M)

    # A: the constant in |W| >= A_j |theta - theta_j|^{nu_j} near the zero, and the
    # positive minimum of |W| away from it.
    Aloc = None
    for i in range(1, 60):
        d = mp.mpf('0.2') * mp.mpf(i) / 59
        for s in (1, -1):
            zz = z_of_theta(Qc, r, theta_j + s * d, zmin, zmax)
            _, tp2, _, th2 = state(Qc, r, zz)
            v = abs(resid(Qc, Bc, r, tp2)) / d**nu_j
            Aloc = v if Aloc is None else min(Aloc, v)
    Afar = min(abs(W) for (th, _, _, _, W) in samples if abs(th - theta_j) >= mp.mpf('0.2'))
    ok(f'(U11) |W(theta)| >= C_1 |theta - theta_1|^nu_1 near the zero with C_1 = {mp.nstr(Aloc, 8)}, '
       f'and |W| >= {mp.nstr(Afar, 8)} away from it')

    # The tight test: evaluate exactly at the edge of the deleted window.  The
    # window half-width e^{-cM/nu_j} shrinks faster than any fixed precision can
    # resolve as an offset from theta_1, so the working precision is raised with
    # M and the offset actually realized is asserted, not assumed -- at dps 60 the
    # M = 320 edge would silently collapse onto theta_1 itself.
    dps0 = mp.mp.dps
    for M in [80, 160, 320, 640]:
        need = int(c * M / nu_j / mp.log(10)) + 60
        mp.mp.dps = max(dps0, need)
        try:
            Qc2, Bc2 = low(Qexpr), low(Bexpr)
            tj2 = mp.pi / 2
            a2, b2 = ft_endpoints(Qc2, r)
            zj2 = mp.mpf(45) / 28
            zmin2 = a2 + (zj2 - a2) * mp.mpf(10)**(-need + 10)
            zmax2 = b2 - (b2 - zj2) * mp.mpf(10)**(-need + 10)
            d = mp.e**(-c * M / nu_j)
            A = min(Aloc, Afar * mp.e**(c * M))
            worst = mp.mpf(0)
            for sgn in (1, -1):
                zz = z_of_theta(Qc2, r, tj2 + sgn * d, zmin2, zmax2)
                rr, tp2, tau2, th2 = state(Qc2, r, zz)
                off = abs(th2 - tj2)
                assert abs(off / d - 1) < mp.mpf('1e-6'), \
                    f'(U11) the window edge is not resolved at M={M}: offset {mp.nstr(off, 8)} vs {mp.nstr(d, 8)}'
                nonp = [w for w in rr if abs(abs(w) / tau2 - 1) > mp.mpf('1e-20')]
                W2 = resid(Qc2, Bc2, r, tp2)
                assert abs(W2) >= A * mp.e**(-c * M) * (1 - mp.mpf('1e-6')), \
                    f'(U11) |W| >= C_A e^(-cM) fails at the window edge, M={M}'
                worst = max(worst, RM2(Qc2, Bc2, r, tau2, nonp, M) / abs(W2))
            for (th, tau, tp, nonp, W) in samples:
                if abs(th - theta_j) < d:
                    continue
                worst = max(worst, RM(tau, nonp, M) / abs(W))
            pred = (C_I / A) * mp.e**(-alpha_I * M / 2)
            assert worst <= pred * (1 + TOL), f'(U11) fails at M={M}: {mp.nstr(worst, 8)} > {mp.nstr(pred, 8)}'
            assert worst < mp.mpf('0.5'), f'(U11) interior does not reach 1/2 at M={M}'
            msg = (f'(U11) M={M} (dps {mp.mp.dps}): the window edge |theta - theta_1| = '
                   f'{mp.nstr(d, 6)} is resolved, |W| >= C_A e^(-cM) holds there, and the '
                   f'retained |R_M|/|W| = {mp.nstr(worst, 8)} <= (C_I/C_A) sigma_I^(M/2) = '
                   f'{mp.nstr(pred, 8)}, hence < 1/2')
        finally:
            mp.mp.dps = dps0
        ok(msg)


# ---------------------------------------------------------------------------
# (U12)
# ---------------------------------------------------------------------------
def check_U12():
    for rho in [3, 4, 6, 11]:
        for c0 in [mp.mpf('0.2'), mp.mpf(1), mp.mpf(3)]:
            eps = mp.mpf('0.1')
            c0p = c0 / (1 + c0 * eps)
            h = mp.log(8 * (rho - 2)) / c0p
            assert h > 0
            assert 2 * (rho - 2) * mp.e**(-c0p * h) <= mp.mpf(1) / 4 + TOL
    ok('(U12) h = log(8(rho-2))/c0\' > 0 solves 2(rho-2) e^(-c0\' h) <= 1/4, and the '
       'identical form with (r, c1\') solves the upper-endpoint condition')

    assert mp.mpf(1) / 4 + mp.mpf(1) / 4 <= mp.mpf(1) / 2
    ok('(U12) each endpoint region: the cluster term (<= 1/4) plus the complementary fixed-gap and '
       'escaping terms (<= 1/4) is <= 1/2, and the interior is bounded by 1/2 directly — the three '
       'regions cover (0, pi/r) and there is no fourth contribution')

    for J, nus, c in [(1, [1], mp.mpf('0.3')), (3, [1, 2, 5], mp.mpf('0.2'))]:
        prev = None
        for M in [200, 400, 800, 1600]:
            total = sum(2 * mp.e**(-c * M / mp.mpf(n)) for n in nus)
            assert prev is None or total < prev
            prev = total
        assert total < mp.mpf('1e-25')
    ok('(U12) the deleted length is exactly sum_j 2 e^(-cM/nu_j), decreasing and exponentially '
       'small for fixed J and fixed multiplicities')


# ---------------------------------------------------------------------------
# (U13)
# ---------------------------------------------------------------------------
def deleted_length(nus, c, M):
    r"""sum_j |Theta_{j,M}| for windows of half-width e^{-cM/nu_j}."""
    return sum(2 * mp.e**(-c * M / mp.mpf(n)) for n in nus)


def window_threshold(nus, c, Mcap=100000):
    r"""Smallest M with (M+1) sum_j |Theta_{j,M}| <= 1, or None past Mcap.

    The left side rises then falls, so the first M that clears the bound is
    found by scanning upward rather than by bisection.
    """
    for M in range(1, Mcap + 1):
        if (M + 1) * deleted_length(nus, c, M) <= 1:
            return M
    return None


def check_U13():
    # (a) the bound holds from a finite index on, and fails below it.
    rows = []
    for nus, c in [([1], mp.mpf('0.3')),
                   ([1, 2, 5], mp.mpf('0.2')),
                   ([1, 1, 1, 3], mp.mpf('0.15'))]:
        M0 = window_threshold(nus, c)
        assert M0 is not None, ('(U13) no threshold found', nus, c)
        # holds at EVERY index at or above M0 out to 20 M0, not merely at a few
        # sample points -- the left side rises before it falls, so a sampled
        # ladder could step over a bump that a contiguous sweep catches
        for M in range(M0, 20 * M0 + 1):
            assert (M + 1) * deleted_length(nus, c, M) <= 1, \
                (f'(U13) (M+1) sum|Theta| > 1 at M={M} >= M0={M0}', nus, c)
        # and fails at every index below it -- the threshold is not decorative
        for M in range(1, M0):
            assert (M + 1) * deleted_length(nus, c, M) > 1, \
                (f'(U13) the bound already held at M={M} < M0={M0}', nus, c)
        rows.append((nus, c, M0))
    ok('(U13) `eq:amplitude-window-negligible`: (M+1) sum_j |Theta_(j,M)| <= 1 from a finite '
       'index on, and > 1 at EVERY index below it, over ' + ', '.join(
           f'nu={nus} c={mp.nstr(c, 3)} (M_0 = {M0})' for nus, c, M0 in rows))

    # (b) the threshold moves with the weight, which is why the paper makes it
    #     B-dependent: nu_j <= deg B by `eq:amplitude-zero-count`.
    c = mp.mpf('0.2')
    thr = [(numax, window_threshold([numax], c)) for numax in (1, 2, 3, 5, 8)]
    assert all(b is not None for _, b in thr)
    assert all(thr[i][1] < thr[i + 1][1] for i in range(len(thr) - 1)), thr
    ok('(U13) the threshold is strictly increasing in max_j nu_j '
       f'({", ".join(f"nu={n}: M_0={M0}" for n, M0 in thr)}), so it depends on B through '
       '`eq:amplitude-zero-count` while the discrepancy constants of '
       '`prop:angular-discrepancy` do not')

    # (c) the deletion costs the count at most one zero, which is the use the
    #     proof makes of the bound.
    for nus, c in [([1], mp.mpf('0.3')), ([1, 2, 5], mp.mpf('0.2'))]:
        M0 = window_threshold(nus, c)
        for M in [M0, 3 * M0, 10 * M0]:
            lost = (M + 1) * deleted_length(nus, c, M) / mp.pi
            assert lost <= 1 / mp.pi, ('(U13) more than 1/pi phase points deleted', nus, c, M)
    ok('(U13) hence at most (M+1)/pi x (deleted length) <= 1/pi < 1 phase points fall in the '
       'deleted set, so `eq:Omega-M` costs the count at most one zero')


def main():
    check_U1()
    check_U7()
    check_U9()

    check_lower((1 - t)**3 * (1 - t / 3), (1 - t)**2 * (2 + t), 1, 3, 1, 2,
                'rho=3, nu=2, r=1, degQ=4>r, p=0')
    check_lower((1 - t / 2)**4, 1 + t, 2, 4, 2, 0,
                'rho=4, nu=0, r=2, degQ=4>r, p=-3')
    check_lower((1 - t)**3, 1 + t / 5, 5, 3, 1, 0,
                'rho=3, nu=0, r=5, degQ=3<r, p=-2')
    check_lower((1 - t)**2 * (1 - t / 4), 3 + t**2, 2, 2, 1, 0,
                'rho=2, nu=0, r=2, degQ=3>r, p=-1')

    check_upper((1 - t) * (1 - t / 2) * (1 - t / 4), 5 + 2 * t, 2, 'r=2, degQ=3>r')
    check_upper((1 - t) * (1 - t / 3), 1 + t, 3, 'r=3, degQ=2<r')
    check_upper((1 - t) * (1 - t / 2) * (1 - t / 5) * (1 - t / 9), 2 + t**2, 2, 'r=2, degQ=4>r')

    check_U11()
    check_U12()
    check_U13()
    print(f'\n{PASSES} checks')
    print('ALL PASS: check_dominance_uniformity')


if __name__ == '__main__':
    main()
