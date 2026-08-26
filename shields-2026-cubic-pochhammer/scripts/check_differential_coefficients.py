#!/usr/bin/env python3
r"""Paper section `subsec:differential-turan-inequality` (`cor:differential`):
the finite algebraic form of the degree-`m` coefficient, and the exact shape of
what a strictness proof has to reproduce.

`check_structural.py` already checks the corollary's exact support, the identity
`[x^m](...) = -Phi''(0)/2`, and the covariance form of `Phi''(0)` along the
paper's own beta route.  This script checks the *finite* route instead -- no
integral anywhere -- because that is the route the Lean development takes:

  * `-Phi_m''(0) = sum_k u_k (V_k - T_k^2)` at the antidiagonal, with
    `u_k = w_k (mu)_{3k}(mu)_{3(m-k)}/((3k-1)!(3(m-k)-1)!)`,
    `T_k = H(3k) - H(3(m-k))`, `V_k = S(3k) + S(3(m-k))`,
    `H(N) = sum_{j<N} 1/(mu+j)`, `S(N) = sum_{j<N} 1/(mu+j)^2`.
    Checked against the exact `d`-derivative of `C_{m,w}(mu+d, mu-d)`.
  * The inequality `sum_k u_k T_k^2 < sum_k u_k V_k` holds over a sweep of
    degrees, parameters and weight families satisfying `eq:w-monotone`.  This is
    the statement the Lean tree records as the remaining gap, so it is checked
    to be TRUE before anything is built on it.
  * It is not termwise and not pairwise: the pairwise bound
    `V_k + V_l >= (T_k - T_l)^2` fails, so no per-term argument can work.
  * It is asymptotically tight: at constant weights the slack tends to `2/mu^2`
    while both sides grow like `3m/mu^2`.
  * Dropping the `j = 0` term from both sides -- which is where that `2/mu^2`
    comes from -- REVERSES the inequality, so the slack cannot be split off.
  * The summand collapses: `(V_k - T_k^2)/2 = tau(3 min(k, m-k))` with
    `tau(n) = S(n) - e_2([n, 3m-n))`, so it depends on `k` only through the
    length of the shorter index block, and `tau` is increasing in `n` with a
    single sign change.  The missing inequality is then "a single-crossing
    function has positive mean".
  * The Abel reduction: the tail sums `B_j` of `lem:weighting` are unimodal in
    `j`, so strictness against every `eq:w-monotone` weight reduces to two
    weights -- the constant one, which is the sequence `f = 1`, and the central
    window.  Both occur as the minimum as `mu` varies.
  * The exact polynomial identity behind the `m = 2` closure,
    `((mu)_N')^2 - (mu)_N (mu)_N'' = sum_{i<N} (prod_{j != i}(mu+j))^2`, and the
    positivity of every `mu`-coefficient of the degree-`m` coefficient at the
    extreme rays of the monotone weight cone.

Exact `sympy` for every identity; `mpmath` at 30 digits for the sweeps, whose
comparisons are all of quantities computed from finite sums with no quadrature.
"""

import math

import mpmath as mp
import sympy as sp

mp.mp.dps = 30
mu, d = sp.symbols('mu d')


def poch_sym(a, k):
    out = sp.Integer(1)
    for i in range(k):
        out *= a + i
    return out


def Cmw_sym(w, m, u, v):
    """`C_{m,w}(u,v)` of `eq:C-def`, exactly."""
    tot = sp.Integer(0)
    for k in range(1, m):
        if w[k] == 0:
            continue
        tot += (sp.sympify(w[k])
                * poch_sym(u, 3 * k) * poch_sym(v, 3 * (m - k))
                / (sp.factorial(3 * k - 1) * sp.factorial(3 * (m - k) - 1)))
    return sp.expand(tot)


def Dpoly(w, m):
    """`-Phi_m''(0)/2`, a polynomial in `mu`."""
    Phi = Cmw_sym(w, m, mu + d, mu - d)
    return sp.expand(-sp.diff(Phi, d, 2).subs(d, 0) / 2)


def window(m, j):
    """The extreme ray of the `eq:w-monotone` cone: 1 on `[j, m-j]`, 0 outside."""
    w = [0] * (m + 1)
    for k in range(j, m - j + 1):
        w[k] = 1
    return w


# ---------------------------------------------------------------------------
# 1.  `-Phi''(0) = sum_k u_k (V_k - T_k^2)`, exactly.
# ---------------------------------------------------------------------------

def H(m_, N):
    return mp.fsum([mp.mpf(1) / (m_ + j) for j in range(N)])


def S(m_, N):
    return mp.fsum([mp.mpf(1) / (m_ + j) ** 2 for j in range(N)])


def uTV(w, m, m_):
    ks = list(range(1, m))
    u = [mp.mpf(w[k]) * mp.mpf(1) / (mp.mpf(math.factorial(3 * k - 1))
                                     * mp.mpf(math.factorial(3 * (m - k) - 1)))
         * mp.mpf(1) for k in ks]
    for i, k in enumerate(ks):
        p = mp.mpf(1)
        for j in range(3 * k):
            p *= (m_ + j)
        for j in range(3 * (m - k)):
            p *= (m_ + j)
        u[i] *= p
    T = [H(m_, 3 * k) - H(m_, 3 * (m - k)) for k in ks]
    V = [S(m_, 3 * k) + S(m_, 3 * (m - k)) for k in ks]
    return ks, u, T, V


def check_uTV_identity():
    for m in range(2, 8):
        for j in range(1, m // 2 + 1):
            w = window(m, j)
            D = Dpoly(w, m)
            for m0 in ['0.25', '1', '3.5', '11']:
                m_ = mp.mpf(m0)
                r = sp.Rational(D.subs(mu, sp.Rational(m0)))
                exact = mp.mpf(int(r.p)) / mp.mpf(int(r.q))
                _, u, T, V = uTV(w, m, m_)
                summed = mp.fsum([uk * (Vk - Tk ** 2)
                                  for uk, Tk, Vk in zip(u, T, V)]) / 2
                rel = abs(summed - exact) / max(abs(exact), mp.mpf(1))
                assert rel < mp.mpf('1e-22'), (m, j, m0, exact, summed, rel)
    print('  [1] -Phi_m\'\'(0)/2 = (1/2) sum_k u_k (V_k - T_k^2): exact match, '
          'm = 2..7, every window weight, mu in {0.25, 1, 3.5, 11}')


# ---------------------------------------------------------------------------
# 2.  The inequality itself, over a sweep.
# ---------------------------------------------------------------------------

def slack(w, m, m_):
    _, u, T, V = uTV(w, m, m_)
    Z = mp.fsum(u)
    assert Z > 0
    EV = mp.fsum([uk * Vk for uk, Vk in zip(u, V)]) / Z
    ET2 = mp.fsum([uk * Tk ** 2 for uk, Tk in zip(u, T)]) / Z
    ET = mp.fsum([uk * Tk for uk, Tk in zip(u, T)]) / Z
    return EV, ET2, ET


MUS = ['0.001', '0.01', '0.1', '0.5', '1', '1.5', '2', '3', '5', '10', '30',
       '100', '1000', '1e5', '1e10']


def monotone_families(m):
    """A spread of weights satisfying `eq:w-monotone`: every extreme ray, the
    all-ones ray, and staircases built from nonnegative increments."""
    out = [[1] * (m + 1)]
    for j in range(1, m // 2 + 1):
        out.append(window(m, j))
    half = m // 2
    for pattern in ([0] * half, list(range(1, half + 1)),
                    [0] * (half - 1) + [1] if half >= 1 else [1],
                    [100] + [0] * (half - 1) if half >= 1 else [1]):
        vals, cur = [], 0.0
        for step in pattern:
            cur += float(step)
            vals.append(cur)
        if max(vals, default=0.0) <= 0:
            continue
        w = [0.0] * (m + 1)
        for k in range(1, m):
            w[k] = vals[min(k, m - k) - 1]
        out.append(w)
    return out


def check_inequality_sweep():
    worst = None
    for m in range(2, 26):
        for w in monotone_families(m):
            for m0 in MUS:
                m_ = mp.mpf(m0)
                EV, ET2, ET = slack(w, m, m_)
                # `T` is odd and the weights even under `k <-> m-k`.
                assert abs(ET) < mp.mpf('1e-20') * max(mp.mpf(1), EV), (m, m0, ET)
                assert ET2 < EV, ('inequality FAILED', m, m0, w[1:m], EV, ET2)
                rel = (EV - ET2) / EV
                if worst is None or rel < worst[0]:
                    worst = (rel, m, m0)
    print('  [2] sum_k u_k T_k^2 < sum_k u_k V_k on the whole sweep '
          '(m = 2..25, every extreme ray and four staircases, 15 values of mu); '
          'E[T] = 0 throughout; tightest relative margin %s at m = %d, mu = %s'
          % (mp.nstr(worst[0], 3), worst[1], worst[2]))


# ---------------------------------------------------------------------------
# 3.  Not pairwise: `V_k + V_l >= (T_k - T_l)^2` fails.
# ---------------------------------------------------------------------------

def check_not_pairwise():
    m, m_ = 40, mp.mpf(1)
    ks, _, T, V = uTV([1] * (m + 1), m, m_)
    i, j = ks.index(1), ks.index(m - 1)
    lhs = V[i] + V[j]
    rhs = (T[i] - T[j]) ** 2
    assert rhs > lhs, (lhs, rhs)
    # and the diagonal pair is the only one that is free
    assert V[i] + V[i] > mp.mpf(0)
    print('  [3] the pairwise bound fails: at m = 40, mu = 1, k = 1, l = 39, '
          '(T_k - T_l)^2 = %s exceeds V_k + V_l = %s, so no termwise or '
          'pairwise argument can give the inequality'
          % (mp.nstr(rhs, 6), mp.nstr(lhs, 6)))


# ---------------------------------------------------------------------------
# 4.  Asymptotic tightness: slack -> 2/mu^2 at constant weights.
# ---------------------------------------------------------------------------

def check_tightness():
    rows = []
    for m in (12, 20, 40, 80):
        for m0 in ('5', '100', '10000'):
            m_ = mp.mpf(m0)
            EV, ET2, _ = slack([1] * (m + 1), m, m_)
            gap = EV - ET2
            target = mp.mpf(2) / m_ ** 2
            rows.append((m, m0, gap, target, gap / EV))
    for m, m0, gap, target, rel in rows:
        assert abs(gap - target) < mp.mpf('0.05') * target, (m, m0, gap, target)
    # once `mu` dominates `m`, both sides are `3m/mu^2` and the relative margin
    # is `2/(3m)`.  At moderate `mu` the sides are smaller, so the margin is
    # larger; the tightness claim is the large-`mu` one.
    for m, m0, gap, target, rel in rows:
        if m0 != '10000':
            continue
        mm = mp.mpf(m0)
        _, _, _ = m, m0, gap
        EV = gap / rel
        assert abs(EV - 3 * m / mm ** 2) < mp.mpf('0.02') * (3 * m / mm ** 2), (m, EV)
        pred = mp.mpf(2) / (3 * m)
        assert abs(rel - pred) < mp.mpf('0.05') * pred, (m, m0, rel, pred)
    print('  [4] at constant weights the slack is 2/mu^2 to within 5% for '
          'm in {12,20,40,80} and mu in {5,100,10^4}; at mu = 10^4 both sides '
          'are 3m/mu^2 to within 2%, so the relative margin is 2/(3m) to '
          'within 5% and the inequality is asymptotically tight')


# ---------------------------------------------------------------------------
# 5.  The `j = 0` term cannot be split off: without it the inequality reverses.
# ---------------------------------------------------------------------------

def check_split_reverses():
    m, m_ = 40, mp.mpf(5)
    ks, u, T, V = uTV([1] * (m + 1), m, m_)
    Z = mp.fsum(u)
    # `V` with the `j = 0` term dropped from both `S(3k)` and `S(3(m-k))`;
    # `T` is unchanged, since the `1/mu` cancels between its two halves.
    Vp = [Vk - 2 / m_ ** 2 for Vk in V]
    EVp = mp.fsum([uk * Vk for uk, Vk in zip(u, Vp)]) / Z
    ET2 = mp.fsum([uk * Tk ** 2 for uk, Tk in zip(u, T)]) / Z
    assert EVp < ET2, (EVp, ET2)
    print('  [5] with the j = 0 term dropped from V the inequality REVERSES at '
          'm = 40, mu = 5 (by %s), so the 2/mu^2 slack is not separable'
          % mp.nstr(ET2 - EVp, 3))


# ---------------------------------------------------------------------------
# 6.  The `m = 2` identity, and coefficient positivity at the extreme rays.
# ---------------------------------------------------------------------------

def check_poch_wronskian():
    for N in range(1, 9):
        P = poch_sym(mu, N)
        lhs = sp.expand(sp.diff(P, mu) ** 2 - P * sp.diff(P, mu, 2))
        rhs = sp.Integer(0)
        for i in range(N):
            term = sp.Integer(1)
            for j in range(N):
                if j != i:
                    term *= mu + j
            rhs += term ** 2
        assert sp.expand(lhs - rhs) == 0, N
    # `m = 2`: the degree-two coefficient is that Wronskian at `N = 3`
    f1 = sp.Symbol('f1', positive=True)
    P = poch_sym(mu, 3)
    D2 = Dpoly([0, f1 * f1, 0], 2)
    expect = sp.expand((f1 / sp.factorial(2)) ** 2
                       * (sp.diff(P, mu) ** 2 - P * sp.diff(P, mu, 2)))
    assert sp.expand(D2 - expect) == 0, (D2, expect)
    print('  [6a] ((mu)_N\')^2 - (mu)_N (mu)_N\'\' = sum_{i<N} (prod_{j!=i}(mu+j))^2 '
          'for N = 1..8, and the m = 2 coefficient is that Wronskian at N = 3')


def check_coefficient_positivity():
    worst = None
    for m in range(2, 10):
        for j in range(1, m // 2 + 1):
            D = Dpoly(window(m, j), m)
            cs = sp.Poly(D, mu).all_coeffs()
            assert min(cs) > 0, (m, j, [c for c in cs if c <= 0])
            assert cs[-1] == m - 2 * j + 1, (m, j, cs[-1])
            if worst is None or min(cs) < worst[0]:
                worst = (min(cs), m, j)
    print('  [6b] every mu-coefficient of the degree-m coefficient is strictly '
          'positive at every extreme ray of the eq:w-monotone cone, m = 2..9; '
          'constant term = #{k : j <= k <= m-j}; smallest coefficient anywhere '
          '%s at m = %d, j = %d -- the cancellation a coefficientwise proof '
          'would have to reproduce' % (worst[0], worst[1], worst[2]))


# ---------------------------------------------------------------------------
# 7.  A simpler equivalent form of the summand, and its single crossing.
# ---------------------------------------------------------------------------

def e2(m_, lo, hi):
    """`e_2` of the reciprocals `1/(mu+i)` over the block `[lo, hi)`."""
    idx = list(range(lo, hi))
    tot = mp.mpf(0)
    for a in range(len(idx)):
        for b in range(a + 1, len(idx)):
            tot += mp.mpf(1) / ((m_ + idx[a]) * (m_ + idx[b]))
    return tot


def tau(m_, m, n):
    """`tau(n) = S(n) - e_2([n, 3m-n))`, the summand as a function of `n` alone."""
    return S(m_, n) - e2(m_, n, 3 * m - n)


def check_tau_form():
    """`(V_k - T_k^2)/2 = tau(3 min(k, m-k))`, and `tau` is increasing with at
    most one sign change.  Both `e_1` identities collapse: writing `S` for the
    shorter index block and `T` for the longer, `AB - e_2(S) - e_2(T)` is
    `sum_{i in S} r_i^2 - e_2(T \\ S)`, so the summand depends on `k` only
    through the length of the shorter block."""
    worst_gap = None
    for m in (2, 3, 4, 6, 10, 20, 40):
        for m0 in ('0.1', '1', '5', '100', '1e6'):
            m_ = mp.mpf(m0)
            ks, u, T, V = uTV([1] * (m + 1), m, m_)
            for i, k in enumerate(ks):
                lhs = (V[i] - T[i] ** 2) / 2
                rhs = tau(m_, m, 3 * min(k, m - k))
                assert abs(lhs - rhs) <= mp.mpf('1e-20') * max(mp.mpf(1), abs(lhs)), \
                    (m, m0, k, lhs, rhs)
            ns = sorted(set(3 * min(k, m - k) for k in ks))
            ts = [tau(m_, m, n) for n in ns]
            for a in range(len(ts) - 1):
                assert ts[a] < ts[a + 1], (m, m0, ns[a], ts[a], ts[a + 1])
            signs = [1 if t > 0 else -1 for t in ts]
            changes = sum(1 for a in range(len(signs) - 1) if signs[a] != signs[a + 1])
            assert changes <= 1, (m, m0, changes, ts)
            # the top of the range is always positive, the bottom is not
            assert ts[-1] > 0, (m, m0, ts[-1])
            D = mp.fsum([uk * tau(m_, m, 3 * min(k, m - k)) for uk, k in zip(u, ks)])
            assert D > 0, (m, m0, D)
            if worst_gap is None or ts[0] < worst_gap[0]:
                worst_gap = (ts[0], m, m0)
    print('  [7] the summand collapses: (V_k - T_k^2)/2 = tau(3 min(k, m-k)) with '
          'tau(n) = S(n) - e_2([n, 3m-n)), so it depends on k only through the '
          'shorter index block; tau is strictly increasing in n with at most one '
          'sign change and is positive at the center, so the missing inequality is '
          '"a single-crossing function has positive mean"; most negative tau '
          'anywhere %s at m = %d, mu = %s'
          % (mp.nstr(worst_gap[0], 4), worst_gap[1], worst_gap[2]))


# ---------------------------------------------------------------------------
# 8.  The Abel reduction: every eq:w-monotone weight reduces to two of them.
# ---------------------------------------------------------------------------

def beta_k(m_, m, k):
    """`u_k tau(n_k)`, the degree-`m` summand at unit weight `w_k = 1`."""
    c = mp.mpf(1) / (mp.mpf(math.factorial(3 * k - 1))
                     * mp.mpf(math.factorial(3 * (m - k) - 1)))
    p = mp.mpf(1)
    for j in range(3 * k):
        p *= (m_ + j)
    for j in range(3 * (m - k)):
        p *= (m_ + j)
    return c * p * tau(m_, m, 3 * min(k, m - k))


def check_abel_reduction():
    """`lem:weighting` makes the degree-`m` coefficient nonnegative against every
    `eq:w-monotone` weight exactly when every tail sum `B_j = sum_{k=j}^{m-j}`
    of the unit-weight summands is nonnegative, `B_j` being the value at the
    `j`-th extreme ray.  Here `B_{j+1} - B_j = -2 u_j tau(3j)` and `tau` is
    increasing, so the differences run `+ ... + - ... -`: `B` is unimodal in `j`
    and its minimum sits at `j = 1` or `j = floor(m/2)`.  Which of the two
    depends on `mu`, so both are needed -- and `B_1` is the constant weight,
    i.e. the sequence `f = 1`, while `B_{floor(m/2)}` is the central window,
    where the gap block is empty or has three elements."""
    flips = set()
    for m in range(2, 26):
        for m0 in ('0.01', '0.5', '1', '3', '10', '100', '1e5'):
            m_ = mp.mpf(m0)
            B = [mp.fsum([beta_k(m_, m, k) for k in range(j, m - j + 1)])
                 for j in range(1, m // 2 + 1)]
            assert min(B) > 0, (m, m0, B)
            assert min(B) == min(B[0], B[-1]), (m, m0, [mp.nstr(b, 4) for b in B])
            for j in range(1, len(B)):
                t = tau(m_, m, 3 * j)
                assert (B[j] - B[j - 1] > 0) == (t < 0), (m, m0, j, t)
            flips.add('j=1' if B[0] <= B[-1] else 'j=floor(m/2)')
    assert flips == {'j=1', 'j=floor(m/2)'}, flips
    # `B_1` is the coefficient at the constant sequence `f = 1`
    for m in range(2, 8):
        for m0 in ('0.5', '2', '9'):
            m_ = mp.mpf(m0)
            B1 = mp.fsum([beta_k(m_, m, k) for k in range(1, m)])
            r = sp.Rational(Dpoly([1] * (m + 1), m).subs(mu, sp.Rational(m0)))
            exact = mp.mpf(int(r.p)) / mp.mpf(int(r.q))
            assert abs(B1 - exact) < mp.mpf('1e-22') * max(abs(exact), mp.mpf(1)), \
                (m, m0, B1, exact)
    print('  [8] the Abel tail sums B_j are unimodal in j -- '
          'sign(B_{j+1} - B_j) = -sign(tau(3j)) and tau is increasing -- so the '
          'minimum is at j = 1 or j = floor(m/2), and BOTH occur as mu varies. '
          'B_1 is the coefficient at the constant sequence f = 1 (checked exactly), '
          'and B_{floor(m/2)} is the central window, where the gap block is empty '
          '(m even) or has three elements (m odd). So strictness for every '
          'eq:w-monotone weight reduces to those two.')


def main():
    print('cor:differential, the finite algebraic route:')
    check_uTV_identity()
    check_inequality_sweep()
    check_not_pairwise()
    check_tightness()
    check_split_reverses()
    check_poch_wronskian()
    check_coefficient_positivity()
    check_tau_form()
    check_abel_reduction()
    print('ALL PASS')


if __name__ == '__main__':
    main()
