#!/usr/bin/env python3
r"""The tail half of lem:central-moments in the critical-scaling section sec:scaling:
eq. (tilt-comparison), eq. (tilted-tail), and the fourth- and sixth-moment claims of
eq. (X4-asymptotic).

The second-moment law eq. (X2-asymptotic) and the averaging that consumes these tail
estimates are verify_critical_scaling.py's.  What is settled here is the estimate that
licenses the termwise averaging in the first place: that the law of K_n is a bounded
tilt of the symmetric hypergeometric law, so its tails are hypergeometric tails.

With S_m as in thm:coefficients, h_m = (m!)^2 4^{-m} S_m, u_m = h_m/(m+1)^b,
b = 3/2 - 2a, C_a = 2^{2a-2}/sqrt(pi), pi_{n,k} = binom(n,k)^2/binom(2n,n) and
X_n = (K_n - n/2)/sqrt n, this verifies, exactly or at arbitrary precision (mpmath):

  * the rewriting the proof opens with: P(K_n = k) = pi_{n,k} h_k h_{n-k}/E_{pi_n}[h_K h_{n-K}]
    is the same law as eq. (Tn-Kn-law)'s S_k S_{n-k}/T_n;
  * u_m -> C_a with 0 < inf_m u_m <= sup_m u_m < infinity, the two constants the proof
    calls m_a and M_a;
  * the two bracketing steps behind eq. (tilt-comparison): on |K - n/2| <= sqrt n the
    product h_K h_{n-K} is a positive multiple of n^{2b} -- converging to the predicted
    C_a^2 2^{-2b} -- while globally it is bounded by a multiple of n^{2b+(-b)_+}; and the
    pi_n-probability of that window is bounded away from zero, which is what the exact
    hypergeometric variance and Chebyshev give;
  * eq. (tilt-comparison) itself in its sharpest form: max_k P(K_n = k)/pi_{n,k}, which
    is the least admissible C_tilt(a) n^{(-b)_+}, divided by n^{(-b)_+} stays bounded
    along an n-ladder.  The exponent is load-bearing: for a > 3/4 the raw ratio grows
    like n^{-b}, so the comparison fails outright without it;
  * Hoeffding's sampling-without-replacement bound pi_n{|K-n/2| > t} <= 2 e^{-2t^2/n},
    against the exact hypergeometric tail;
  * eq. (tilted-tail): |X_n| <= sqrt n/2 exactly, the exact tilted tail moment
    E[(1+|X_n|^q) 1_{|K_n-n/2|>n^{3/5}}] against the bound the proof assembles, and that
    the bound decays super-polynomially -- its effective exponent -d log B/d log n grows
    without bound along a ladder and passes M = 10, which a genuine O(n^-M) rate cannot
    be read off any fixed n;
  * eq. (X4-asymptotic): E X_n^4 = 3/64 + O(n^-1) and E|X_n|^6 = O(1) under the tilted
    law, with the n-weighted fourth-moment remainder bounded along the ladder.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 60

NMAX = 1600
LADDER = [100, 200, 400, 800, 1600]
AVALS = ['0.3', '1', '2.5']

def S_num(a, k):
    return mp.rf(2*a + k - 1, k)/(mp.factorial(k)*mp.gamma(a + k)**2)

for text in AVALS:
    a = mp.mpf(text)
    b = mp.mpf(3)/2 - 2*a
    bplus = max(mp.mpf(0), -b)                       # (-b)_+
    C_a = 2**(2*a - 2)/mp.sqrt(mp.pi)
    S = [S_num(a, k) for k in range(NMAX + 1)]
    h = [mp.factorial(k)**2/mp.mpf(4)**k*S[k] for k in range(NMAX + 1)]
    u = [h[m]/mp.mpf(m + 1)**b for m in range(NMAX + 1)]

    # ---- u_m -> C_a, with m_a = inf u > 0 and M_a = sup u < infinity. ----
    m_a, M_a = min(u), max(u)
    assert m_a > 0 and M_a < mp.inf, (a, m_a, M_a)
    # u_m -> C_a > 0 at rate 1/m, which is what makes the inf and sup over the whole
    # index set -- not just the tested range -- positive and finite.
    assert C_a > 0
    assert abs(u[NMAX]/C_a - 1) < 20/mp.mpf(NMAX), (a, u[NMAX], C_a)
    assert abs(u[NMAX//4]/C_a - 1) > abs(u[NMAX]/C_a - 1), (a,)
    assert m_a <= C_a*(1 + 20/mp.mpf(NMAX)) and M_a >= C_a*(1 - 20/mp.mpf(NMAX)), (a,)

    lo_prev = None
    scaled_ratio = []
    for n in LADDER:
        binom2n = mp.binomial(2*n, n)
        pi = [mp.binomial(n, k)**2/binom2n for k in range(n + 1)]
        assert abs(mp.fsum(pi) - 1) < mp.mpf('1e-40'), n
        w = [S[k]*S[n-k] for k in range(n + 1)]
        T = mp.fsum(w)
        law = [wk/T for wk in w]

        # ---- the tilt rewriting of eq. (Tn-Kn-law). ----
        mean_tilt = mp.fsum(pi[k]*h[k]*h[n-k] for k in range(n + 1))
        for k in [0, 1, n//3, n//2, n - 1, n]:
            assert abs(law[k] - pi[k]*h[k]*h[n-k]/mean_tilt) < mp.mpf('1e-45')*law[k], (a, n, k)

        # ---- the two bracketing steps. ----
        window = [k for k in range(n + 1) if abs(k - mp.mpf(n)/2) <= mp.sqrt(n)]
        lo = min(h[k]*h[n-k] for k in window)/mp.mpf(n)**(2*b)
        hi = max(h[k]*h[n-k] for k in range(n + 1))/mp.mpf(n)**(2*b + bplus)
        predicted = C_a**2*mp.mpf(2)**(-2*b)
        assert mp.mpf('0.7') < lo/predicted < mp.mpf('1.05'), (a, n, lo/predicted)
        if lo_prev is not None:
            assert lo/predicted > lo_prev                 # improving toward C_a^2 2^{-2b}
        lo_prev = lo/predicted
        assert 0 < hi < 100, (a, n, hi)

        # Chebyshev on the window, from the exact hypergeometric variance
        # Var_{pi_n} K = n^2/(4(2n-1)), which is n times eq. (hypergeom-moments).
        var_pi = mp.fsum(pi[k]*(k - mp.mpf(n)/2)**2 for k in range(n + 1))
        assert abs(var_pi - mp.mpf(n)**2/(4*(2*n - 1))) < mp.mpf('1e-40')*var_pi, (a, n)
        p_window = mp.fsum(pi[k] for k in window)
        assert p_window >= 1 - var_pi/n, (a, n)           # Chebyshev
        assert p_window > mp.mpf(7)/8, (a, n, p_window)   # bounded away from zero

        # ---- eq. (tilt-comparison), in its sharpest form. ----
        ratio = max(law[k]/pi[k] for k in range(n + 1))
        assert ratio/mp.mpf(n)**bplus < 2, (a, n, ratio)
        scaled_ratio.append(ratio/mp.mpf(n)**bplus)

        # ---- Hoeffding, against the exact hypergeometric tail. ----
        for t in [mp.sqrt(n), mp.mpf(n)**mp.mpf('0.6'), mp.mpf(n)/4]:
            exact = mp.fsum(pi[k] for k in range(n + 1) if abs(k - mp.mpf(n)/2) > t)
            assert exact <= 2*mp.e**(-2*t**2/n), (a, n, t, exact)

        # ---- eq. (tilted-tail): the exact moment against the assembled bound. ----
        t = mp.mpf(n)**mp.mpf('0.6')
        tail_idx = [k for k in range(n + 1) if abs(k - mp.mpf(n)/2) > t]
        assert max(abs(k - mp.mpf(n)/2)/mp.sqrt(n) for k in range(n + 1)) <= mp.sqrt(n)/2
        for q in [0, 2, 6]:
            exact_moment = mp.fsum(
                law[k]*(1 + abs((k - mp.mpf(n)/2)/mp.sqrt(n))**q) for k in tail_idx)
            tail_prob = mp.fsum(law[k] for k in tail_idx)
            # |X_n| <= sqrt(n)/2, then eq. (tilt-comparison), then Hoeffding
            bound = (1 + (mp.sqrt(n)/2)**q)*2*(ratio/mp.mpf(n)**bplus)*mp.mpf(n)**bplus \
                * mp.e**(-2*t**2/n)
            assert exact_moment <= (1 + (mp.sqrt(n)/2)**q)*tail_prob, (a, n, q)
            assert exact_moment <= bound, (a, n, q, exact_moment, bound)

        # ---- eq. (X4-asymptotic) under the tilted law. ----
        X4 = mp.fsum(law[k]*((k - mp.mpf(n)/2)/mp.sqrt(n))**4 for k in range(n + 1))
        X6 = mp.fsum(law[k]*abs((k - mp.mpf(n)/2)/mp.sqrt(n))**6 for k in range(n + 1))
        assert abs(X4 - mp.mpf(3)/64)*n < 2, (a, n, X4)
        assert X6 < 1, (a, n, X6)

    # The exponent (-b)_+ in eq. (tilt-comparison) is exactly right, not merely
    # sufficient: the scaled ratio is bounded above and below along the ladder, so for
    # a > 3/4, where (-b)_+ > 0, the raw ratio genuinely grows like n^{(-b)_+} and no
    # comparison with a smaller exponent can hold.
    assert max(scaled_ratio) < mp.mpf('1.5')*min(scaled_ratio), (a, scaled_ratio)
    if a > mp.mpf(3)/4:
        span = mp.mpf(LADDER[-1])/LADDER[0]
        raw_growth = ((scaled_ratio[-1]*mp.mpf(LADDER[-1])**bplus)
                      / (scaled_ratio[0]*mp.mpf(LADDER[0])**bplus))
        assert raw_growth > span**bplus/mp.mpf('1.5'), (a, raw_growth)

print('PASS: P(K_n=k) = pi_{n,k} h_k h_{n-k}/E_{pi_n}[h_K h_{n-K}] is eq. (Tn-Kn-law)\'s law')
print('PASS: u_m -> C_a with 0 < m_a = inf u_m <= C_a <= M_a = sup u_m < infinity')
print('PASS: h_K h_{n-K} is a positive multiple of n^{2b} on |K-n/2| <= sqrt n, converging')
print('      to C_a^2 2^{-2b}, and a bounded multiple of n^{2b+(-b)_+} globally; the window')
print('      has pi_n-probability > 7/8 by the exact variance n^2/(4(2n-1)) and Chebyshev')
print('PASS: eq. (tilt-comparison) max_k P(K_n=k)/pi_{n,k} stays a bounded multiple of')
print('      n^{(-b)_+}, and for a > 3/4 grows like it, so the exponent is load-bearing')
print('PASS: Hoeffding pi_n{|K-n/2|>t} <= 2 e^{-2t^2/n} against the exact hypergeometric tail')
print('PASS: eq. (tilted-tail) |X_n| <= sqrt n/2 and the exact tail moment sits under the')
print('      bound the proof assembles, for q = 0, 2, 6')
print('PASS: eq. (X4-asymptotic) E X_n^4 = 3/64 + O(n^-1) and E|X_n|^6 = O(1), tilted law')

# ===========================================================================
# Super-polynomial decay of the assembled bound.  O_{a,q,M}(n^-M) holds for every M,
# with an M-dependent constant, so it cannot be read off any single n: what is testable
# is that the effective exponent of the bound grows without bound.  The bound is closed
# form, so the ladder can run far past anything summable.
# ===========================================================================
for text in AVALS:
    a = mp.mpf(text)
    bplus = max(mp.mpf(0), 2*a - mp.mpf(3)/2)
    for q in [0, 6]:
        def logB(nv):
            n_ = mp.mpf(nv)
            return (mp.log(1 + (mp.sqrt(n_)/2)**q) + bplus*mp.log(n_)
                    + mp.log(2) - 2*n_**mp.mpf('0.2'))
        rung = [mp.mpf(10)**j for j in range(3, 13)]
        exps = [-(logB(rung[i+1]) - logB(rung[i]))/(mp.log(rung[i+1]) - mp.log(rung[i]))
                for i in range(len(rung) - 1)]
        assert all(exps[i+1] > exps[i] for i in range(len(exps) - 1)), (a, q, exps)
        assert exps[-1] > 10, (a, q, exps[-1])
print('PASS: eq. (tilted-tail) the assembled bound decays super-polynomially -- its')
print('      effective exponent increases along n = 10^3..10^12 and passes M = 10')

print('ALL PASS: check_tilted_tail')
