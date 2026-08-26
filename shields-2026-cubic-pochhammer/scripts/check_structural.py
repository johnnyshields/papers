#!/usr/bin/env python3
r"""Paper sections `sec:reduction`, `sec:kernel` and `sec:consequences`: the
three structural results.

Each is checked against the objects that define it rather than transcribed.
`sec:threshold`'s headline identities -- `eq:r-central-slope` and
`eq:r-degree-three`, the closed form of G^{(r)}_3, the quartic flatness and
the two minimality clauses -- live in
`verify_multiplicity.py`, which is the sweep named for that section.

  * `eq:abel-weight`, the Abel/tail-sum identity behind `lem:weighting`, and the dual cone it
    exhibits, enumerated exhaustively for `L <= 5`: the weighted sum is
    nonnegative against every nondecreasing nonnegative weight exactly when every
    tail sum is nonnegative, with the central-window indicator as the witness
    when one is not.  The lemma as stated -- the identity in general, both cone
    directions, the strict clause and its hypothesis controls -- is in
    `verify_monotonicity_lemmas.py`.
  * `prop:kernel-exact`, the exactness of the kernel reduction, in BOTH directions.
    The equivalence (i) <=> (ii) between monotonicity of `G_{m,w}` on `[0,1/2]`
    and Schur-concavity of `C_{m,w}`, at arbitrary symmetric nonnegative weights
    including ones that violate `eq:w-monotone`; and the concentration step of the
    converse as a symbolic limit `s -> infinity` on the exact beta-moment sum,
    which returns `G(p)` identically rather than as a decreasing error.
  * `cor:differential`'s exact support, including at `mu = 0`, where the differential
    Turanian degenerates to `(sum f_n x^n)^2`; the identity
    `[x^m](...) = -Phi''(0)/2`; and `Phi''(0) = kappa_{m,2mu} Cov(Ghat_{m,w}(Q_0),
    ell(Q_0)^2) < 0` at several `m` and at genuine log-concave `f`-weights.

Exact `sympy` and integer arithmetic throughout, and the beta concentration is
computed from exact beta moments rather than by quadrature, since a Beta law at
large `s` is too concentrated for it.  The one place quadrature appears is the
covariance of `cor:differential`, in `mpmath` at 30 digits with the estimated error
asserted below the margin the strict inequality needs.
"""

import sympy as sp
import mpmath as mp

mp.mp.dps = 30
mu, p, q, x, d = sp.symbols('mu p q x d')
R = sp.Rational


def poch(a, j):
    out = sp.Integer(1)
    for i in range(j):
        out *= a + i
    return out


def check_abel_duality():
    """`eq:abel-weight`, and the dual cone with its central-window witnesses."""
    import itertools
    for L in range(1, 6):
        for A in itertools.product(range(-3, 4), repeat=L):
            A = [sp.Integer(a) for a in A]
            T = [sum(A[k - 1] for k in range(r, L + 1)) for r in range(1, L + 1)]
            # the identity, against every 0/1-increment weight
            for cut in range(1, L + 1):
                w = [sp.Integer(0)] * cut + [sp.Integer(1)] * (L - cut + 1)
                lhs = sum(w[k] * A[k - 1] for k in range(1, L + 1))
                rhs = sum((w[r] - w[r - 1]) * T[r - 1] for r in range(1, L + 1))
                assert sp.expand(lhs - rhs) == 0, (A, cut)
            if all(t >= 0 for t in T):
                for cut in range(1, L + 1):     # every central window is then nonneg
                    w = [sp.Integer(0)] * cut + [sp.Integer(1)] * (L - cut + 1)
                    assert sum(w[k] * A[k - 1] for k in range(1, L + 1)) >= 0, (A, cut)
            else:
                bad = [r for r in range(1, L + 1) if T[r - 1] < 0][0]
                w = [sp.Integer(0)] * bad + [sp.Integer(1)] * (L - bad + 1)
                assert sum(w[k] * A[k - 1] for k in range(1, L + 1)) < 0, (A, bad)
    print("PASS  `eq:abel-weight` holds identically, and tails all >= 0 <=> nonnegative against "
          "every monotone weight, the failing central window witnessing otherwise "
          "(exhaustive, L <= 5)")
    # one sign change, - to +, with a nonnegative total, forces every tail nonnegative
    for L in range(1, 9):
        for cut in range(L + 1):
            for neg in itertools.product(range(0, 3), repeat=cut):
                A = [-sp.Integer(v) for v in neg] + [sp.Integer(1)] * (L - cut)
                if sum(A) < 0:
                    continue
                T = [sum(A[k - 1] for k in range(r, L + 1)) for r in range(1, L + 1)]
                assert all(t >= 0 for t in T), (A, T)
    print("PASS  one sign change (- to +) with a nonnegative total gives every tail >= 0")


def EG_moments(G, sv, pv):
    """E G(P) for P ~ Beta(s p, s(1-p)), from the exact beta moments of a polynomial."""
    P = sp.Poly(sp.expand(G), p)
    return sum(c * poch(sv * pv, k) / poch(sv, k) for (k,), c in P.terms())


KERNELS = {
    'r=3,m=3': 21 * (p * (1 - p)) ** 3 * (1 - 3 * p * (1 - p)),
    'r=3,m=4': sum(sp.binomial(10, 3 * k - 1) * p ** (3 * k) * (1 - p) ** (3 * (4 - k))
                   for k in (1, 2, 3)),
    'r=4,m=3': sum(sp.binomial(10, 4 * k - 1) * p ** (4 * k) * (1 - p) ** (4 * (3 - k))
                   for k in (1, 2)),
}


def check_kernel_reduction_exact():
    """`prop:kernel-exact`'s converse: the concentration step, as a limit.

    The proof lets s -> infinity and uses P_{s,p} -> p in probability to pass
    E G(P_{s,p}) -> G(p).  A list of four decreasing errors is consistent with
    that but does not establish it, so the limit is taken symbolically instead:
    over a symbolic s, the exact beta-moment sum for a polynomial G has limit
    G(p) identically in p.  The decreasing errors are kept beside it as a
    numeric cross-check, and the contrapositive is exhibited on a kernel that is
    NOT centrally monotone.
    """
    sv = sp.Symbol('s', positive=True)
    for name, G in KERNELS.items():
        EG = sp.simplify(EG_moments(G, sv, p))
        lim = sp.limit(EG, sv, sp.oo)
        assert sp.simplify(sp.expand(lim - G)) == 0, (name, lim)
        # A second, independent route to the same limit, so the step does not
        # rest on one sympy call: E G(P_{s,p}) is a rational function of s whose
        # numerator and denominator have equal degree, and the limit is then the
        # ratio of their leading coefficients.  That is elementary and instant,
        # and it agrees with sp.limit on every kernel here.
        num, den = sp.fraction(sp.cancel(sp.together(EG)))
        pn, pd = sp.Poly(num, sv), sp.Poly(den, sv)
        assert pn.degree() == pd.degree(), (name, pn.degree(), pd.degree())
        by_leading = sp.expand(pn.LC() / pd.LC())
        assert sp.simplify(sp.expand(by_leading - G)) == 0, (name, by_leading)
        assert sp.simplify(sp.expand(by_leading - lim)) == 0, name
        for pv in [R(1, 2), R(3, 5), R(7, 10), R(9, 10)]:
            errs = [abs(sp.nsimplify(EG_moments(G, sp.Integer(s), pv), rational=True)
                        - sp.nsimplify(G.subs(p, pv), rational=True))
                    for s in (10, 100, 1000, 10000)]
            assert all(errs[i + 1] < errs[i] for i in range(3)), (name, pv, errs)
    print(f"PASS  `prop:kernel-exact`: lim_{{s->oo}} E G(P_{{s,p}}) = G(p) IDENTICALLY in p, "
          f"symbolically in s by two independent routes ({len(KERNELS)} kernels), with "
          f"the errors decreasing at four scales x four p as a cross-check")
    # the converse has teeth: a kernel that is NOT central breaks the all-scale property
    G4 = KERNELS['r=4,m=3']
    assert sp.nsimplify(G4.subs(p, R(1, 2)) - G4.subs(p, R(11, 20)), rational=True) < 0
    gap = (EG_moments(G4, sp.Integer(10000), R(1, 2))
           - EG_moments(G4, sp.Integer(10000), R(11, 20)))
    assert sp.nsimplify(gap, rational=True) < 0, gap
    print("PASS  and it has teeth: for the r=4, m=3 kernel the all-scale gap is NEGATIVE, "
          "matching G(1/2) < G(11/20)")


def Ghat(m, w):
    """Ghat_{m,w}(q), the folding of `eq:G-weighted` through q = p(1-p).

    Reduced modulo p^2 - p + q rather than substituted: for symmetric weights
    G_{m,w} is a polynomial in q, so the remainder is constant in p, and that
    the remainder IS constant in p is asserted -- it is the well-definedness of
    Ghat, that the two roots of p(1-p) = q give the same value.
    """
    G = sum(w[k] * sp.binomial(3 * m - 2, 3 * k - 1) * p ** (3 * k) * (1 - p) ** (3 * (m - k))
            for k in range(1, m))
    rem = sp.expand(sp.rem(sp.expand(G), p ** 2 - p + q, p))
    assert sp.Poly(rem, p).degree() <= 0, (m, rem)
    return sp.expand(rem)


def check_kernel_exact_equivalence():
    r"""`prop:kernel-exact`'s equivalence (i) <=> (ii), at arbitrary symmetric weights.

    (i) G_{m,w} nondecreasing on [0,1/2]; (ii) C_{m,w} Schur-concave, i.e. at
    each fixed s the map d -> C_{m,w}(s/2+d, s/2-d) is nonincreasing on [0,s/2].

    (i) is decided EXACTLY: by `eq:J-weighted` the derivative of G_{m,w}(t/(1+t)) is
    a positive multiple of J_{m,w}(t) on 0 < t < 1, and t -> t/(1+t) maps (0,1)
    onto (0,1/2), so (i) holds exactly when J_{m,w} >= 0 there -- settled by an
    exact interior root count plus one sign evaluation.  (ii) is then tested on
    a grid of (s,d): where (i) holds no increase may appear, and where it fails
    an explicit increasing pair is REQUIRED, which is the direction a sampled
    check can carry.  The weight families include vectors violating `eq:w-monotone`,
    among them `rem:internal-zeros`' w = (1,0,0,1).
    """
    t = sp.Symbol('t')

    def Jw(m, w):
        return sp.expand(sum(w[k] * sp.binomial(3 * m - 2, 3 * k - 1)
                             * t ** (3 * k - 1) * (k - (m - k) * t)
                             for k in range(1, m)))

    def Cmw(w, m, u, v):
        return sum(w[k] * poch(u, 3 * k) * poch(v, 3 * (m - k))
                   / (sp.factorial(3 * k - 1) * sp.factorial(3 * (m - k) - 1))
                   for k in range(1, m))

    families = [
        (3, [1, 1]), (4, [1, 1, 1]), (4, [0, 1, 0]),
        (5, [1, 2, 2, 1]), (5, [2, 1, 1, 2]), (5, [1, 0, 0, 1]),
        (6, [1, 1, 5, 1, 1]), (6, [5, 1, 1, 1, 5]), (6, [0, 0, 1, 0, 0]),
        (7, [1, 3, 4, 4, 3, 1]), (7, [4, 3, 1, 1, 3, 4]),
    ]
    monotone = broken = 0
    for m, ws in families:
        w = {k: sp.Integer(ws[k - 1]) for k in range(1, m)}
        assert all(w[k] == w[m - k] for k in range(1, m)), (m, ws)   # symmetric
        assert all(w[k] >= 0 for k in w)
        J = sp.Poly(Jw(m, w), t)
        # strip the endpoint roots with their multiplicities, so what is left
        # counts the INTERIOR roots; t^a and (t-1)^b have constant sign on (0,1),
        # so J does too whenever that count is zero
        core = J
        while core.eval(0) == 0:
            core = core.quo(sp.Poly(t, t))
        while core.eval(1) == 0:
            core = core.quo(sp.Poly(t - 1, t))
        interior = core.count_roots(0, 1)
        grid = [R(i, 24) for i in range(1, 24)]
        negative = [tv for tv in grid if J.eval(tv) < 0]
        if negative:
            nondecreasing_G = False
        else:
            # no negative sample: the root count must confirm constant sign
            assert interior == 0, (m, ws, interior)
            nondecreasing_G = J.eval(R(1, 2)) > 0
            assert nondecreasing_G, (m, ws)
        rises = []
        for sv in [R(3), R(15, 2), R(11)]:
            ds = [sv / 2 * R(i, 6) for i in range(7)]
            vals = [sp.nsimplify(Cmw(w, m, sv / 2 + dv, sv / 2 - dv), rational=True)
                    for dv in ds]
            rises += [(sv, a, b) for a, b in zip(vals, vals[1:]) if b > a]
        if nondecreasing_G:
            assert not rises, (m, ws, rises[:1])          # (i) => (ii) on every pair
            monotone += 1
        else:
            assert rises, (m, ws)                          # not (i) => not (ii)
            broken += 1
    assert monotone > 0 and broken > 0, (monotone, broken)
    print(f"PASS  `prop:kernel-exact` (i) <=> (ii) on {len(families)} symmetric weight "
          f"vectors: {monotone} with J_{{m,w}} >= 0 on (0,1) by exact root count show no "
          f"increase of d -> C_{{m,w}}(s/2+d,s/2-d) anywhere, and {broken} without it "
          f"exhibit one -- `eq:w-monotone` violators included")


def check_differential_exact_support():
    """`cor:differential`: strict positivity exactly on I+I, mu = 0 included."""
    def Fser(f, m, N):
        return sum(f.get(n, 0) * poch(m, 3 * n) / sp.factorial(3 * n - 1) * x ** n
                   for n in range(1, N + 1))
    cases = [({1: sp.Integer(1), 2: sp.Integer(1)}, 'I={1,2}'),
             ({2: sp.Integer(1), 3: sp.Integer(1)}, 'I={2,3}'),
             ({n: sp.Integer(1) for n in range(1, 6)}, 'I={1..5}'),
             ({3: sp.Integer(1)}, 'I={3}'),
             ({1: sp.Integer(1), 2: sp.Integer(2), 3: sp.Integer(1)}, 'I={1,2,3}')]
    for f, _ in cases:
        N = 8
        I = sorted(n for n in f if f[n] > 0)
        IpI = {i + j for i in I for j in I}
        F = Fser(f, mu, N)
        D = sp.expand(sp.diff(F, mu) ** 2 - F * sp.diff(F, mu, 2))
        for m in range(2, N + 1):
            c = sp.expand(D.coeff(x, m))
            for v in [sp.Integer(0), R(1, 2), sp.Integer(1), sp.Integer(7), sp.Integer(50)]:
                val = sp.nsimplify(c.subs(mu, v), rational=True)
                assert (val > 0) if m in IpI else (val == 0), (m, v, val)
        # at mu = 0 the Turanian degenerates to (sum f_n x^n)^2
        assert sp.expand(F.subs(mu, 0)) == 0
        assert sp.expand(sp.diff(F, mu).subs(mu, 0)
                         - sum(f.get(n, 0) * x ** n for n in range(1, N + 1))) == 0
    for n in range(1, 7):
        assert sp.diff(poch(mu, 3 * n) / sp.factorial(3 * n - 1), mu).subs(mu, 0) == 1
    print("PASS  `cor:differential`: strictly positive exactly on I+I at mu = 0, 1/2, 1, 7, 50 "
          "(5 supports), and at mu=0 the Turanian is (sum f_n x^n)^2")
    # the second-derivative identity and the sign of the covariance behind it
    def Cmw(w, m, u, v):
        return sum(w[k] * poch(u, 3 * k) * poch(v, 3 * (m - k))
                   / (sp.factorial(3 * k - 1) * sp.factorial(3 * (m - k) - 1))
                   for k in range(1, m))
    for f, m in [({1: sp.Integer(1), 2: sp.Integer(1)}, 3),
                 ({n: sp.Integer(1) for n in range(1, 5)}, 4)]:
        F = Fser(f, mu, 7)
        D = sp.expand(sp.diff(F, mu) ** 2 - F * sp.diff(F, mu, 2))
        w = {k: f.get(k, 0) * f.get(m - k, 0) for k in range(1, m)}
        for v in [R(1, 2), sp.Integer(1), sp.Integer(4)]:
            Phi = sp.expand(Cmw(w, m, v + d, v - d))
            assert sp.simplify(sp.nsimplify(sp.expand(D.coeff(x, m)).subs(mu, v), rational=True)
                               + sp.diff(Phi, d, 2).subs(d, 0) / 2) == 0, (m, v)
            assert sp.diff(Phi, d, 2).subs(d, 0) < 0, (m, v)
    print("PASS  [x^m]((d_mu F)^2 - F d^2_mu F) = -Phi''(0)/2, with Phi''(0) < 0")
    check_differential_covariance_identity()


def kappa(m, s):
    """kappa_{m,s} = (s)_{3m}/(3m)! * 3m(3m-1), the prefactor of `eq:fixed-sum`."""
    return poch(s, 3 * m) / sp.factorial(3 * m) * 3 * m * (3 * m - 1)


def check_differential_covariance_identity():
    r"""`cor:differential`: Phi''(0) = kappa_{m,2mu} Cov(Ghat_{m,w}(Q_0), ell(Q_0)^2) < 0.

    The corollary states this for every m >= 2 at the weights w_k = f_k f_{m-k}
    of `eq:w-from-f`, so it is run at several m and at genuine log-concave f, not
    only at constant weights and m = 3.  Phi''(0) is computed symbolically from
    `eq:C-def`; the covariance is a quadrature against the folded-beta density
    g_0(q) proportional to q^{s/2-1}(1-4q)^{-1/2}, which is singular at BOTH
    endpoints and feeds a strict inequality, so every integral is taken with its
    error estimate and the estimate is asserted small against the value it
    bounds -- otherwise the sign claim rests on an unmeasured quadrature.
    """
    def Cmw(w, m, u, v):
        return sum(w[k] * poch(u, 3 * k) * poch(v, 3 * (m - k))
                   / (sp.factorial(3 * k - 1) * sp.factorial(3 * (m - k) - 1))
                   for k in range(1, m))

    def to_mp(r):
        r = sp.Rational(r)
        return mp.mpf(int(r.p)) / mp.mpf(int(r.q))

    cases = [(3, {1: sp.Integer(1), 2: sp.Integer(1)}, 'constant, m=3'),
             (4, {k: sp.Integer(1) for k in (1, 2, 3)}, 'constant, m=4')]
    # a genuinely log-concave f with interval support, checked to be one
    f = {1: sp.Integer(1), 2: sp.Integer(3), 3: sp.Integer(4), 4: sp.Integer(2)}
    assert sorted(f) == list(range(1, 5))
    for n in (2, 3):
        assert f[n] ** 2 >= f[n - 1] * f[n + 1], n
    for m in (4, 5, 6):
        w = {k: f.get(k, sp.Integer(0)) * f.get(m - k, sp.Integer(0)) for k in range(1, m)}
        assert any(v != 0 for v in w.values()), m
        cases.append((m, w, f'w_k = f_k f_(m-k), m={m}'))

    worst_rel = mp.mpf(0)
    for m, w, name in cases:
        Gh = sp.lambdify(q, Ghat(m, w), 'mpmath')
        for muv in (R(3, 4), R(3, 2), R(4)):
            sv = 2 * muv
            Phi2 = sp.diff(sp.expand(Cmw(w, m, muv + d, muv - d)), d, 2).subs(d, 0)
            assert Phi2 < 0, (name, muv, Phi2)
            half = to_mp(sv) / 2
            rho = lambda z: z ** (half - 1) * (1 - 4 * z) ** mp.mpf("-0.5")
            ell = lambda z: mp.log((1 + mp.sqrt(1 - 4 * z)) / (1 - mp.sqrt(1 - 4 * z)))
            end = [0, mp.mpf(1) / 4]
            Z, eZ = mp.quad(rho, end, error=True)
            A, eA = mp.quad(lambda z: Gh(z) * rho(z), end, error=True)
            B, eB = mp.quad(lambda z: ell(z) ** 2 * rho(z), end, error=True)
            C, eC = mp.quad(lambda z: Gh(z) * ell(z) ** 2 * rho(z), end, error=True)
            # each integral's estimated error, relative to the integral itself
            for val, err in ((Z, eZ), (A, eA), (B, eB), (C, eC)):
                assert err < mp.mpf("1e-15") * abs(val), (name, muv, val, err)
            cov = C / Z - (A / Z) * (B / Z)
            assert cov < 0, (name, muv, cov)
            # and the margin: the quadrature error cannot reach zero from here
            margin = (eC / Z + abs(A / Z) * eB / Z + abs(B / Z) * eA / Z
                      + 3 * abs(cov) * eZ / Z)
            assert margin < abs(cov) / 10 ** 6, (name, muv, cov, margin)
            pred = to_mp(kappa(m, sv)) * cov
            got = to_mp(Phi2)
            rel = abs(got - pred) / abs(got)
            assert rel < mp.mpf("1e-12"), (name, muv, got, pred, rel)
            worst_rel = max(worst_rel, rel)
    print(f"PASS  `cor:differential`: Phi''(0) = kappa_{{m,2mu}} Cov(Ghat_{{m,w}}(Q_0), "
          f"l(Q_0)^2) < 0 over {len(cases)} weight sets (m = 3..6, constant and "
          f"f-derived) x 3 values of mu, worst relative gap {mp.nstr(worst_rel, 3)}, "
          f"every quadrature error asserted below 1e-6 of the covariance it bounds")


def main():
    check_abel_duality()
    check_kernel_reduction_exact()
    check_kernel_exact_equivalence()
    check_differential_exact_support()
    print("ALL PASS")


if __name__ == "__main__":
    main()
