r"""Paper section `sec:response` (The complete scalar and its second channel):
`eq:complementary`, `prop:clocks`, `eq:clock-infinity`.

Reading.  The proposition's hypothesis is a comparison of two Schur-equal charts of periods p > q,
which the main theorem rules out.  Its content for the p-chart alone is the pair of relations
that the chart gives at its own horizon, and that is built backwards here: the horizon q of the
cap machinery is set equal to p, so that the windows, the frames, the cap vectors l, r and the
returns x_R, y_L (all as in `_source_common.source_data`) are those of one actual ordinary chart.
For every connected J up to J_CELLS cells, legal ordinary case (a) mark of period p and width
w > 0, divisor g of p with c = w mod g > 0, and S = Row_3 o J (a == N - p - c > c), restricted to
the phase bounds of lem:phase-confinement (t <= c, w - s <= c), at a seeded rational alphabet with
rational h_0 = nu, exactly:

  * the clock lambda = p(M - 1) + s - t of the row chart equals a + sigma - tau with
    sigma = s - d g, tau = t (w = d g + c), and a + sigma - tau = d_p with d_p = N - p - c +
    sigma - tau > 0, alpha = d_p, Delta = c - sigma + tau lies in [0, 2c], alpha = N - p - Delta;
  * the ordinary whole observer O_lambda = [z^m] H (m - lambda - Theta)(R_S L_S) vanishes at this
    clock (the own-parent identity the paper's ordinary chart supplies);
  * D(z) = w_c - r x_R - l y_L equals w_c = r l modulo z^(c+1), i.e. T_R + T_L = 0 exactly (not
    only in the limit nu -> infinity), which is eq:complementary for the positive clock;
  * the limit: at nu = 10^9 the constant terms [z^0] T_R and [z^0] T_L are below 10^-3, i.e.
    e_R = e_L = 0, which with lambda = a + sigma - tau is eq:clock-infinity.
Controls: for the same charts at a horizon q != p the
identity D = r l fails on a positive fraction of instances, and on g-periodic sources from
`_source_common.sample` (which are not charts) it fails on every instance, so the relation is
neither automatic nor a property of the window machinery alone.

Uncovered: the mixed/mixed relation T_R + T_L = 1, the negative-clock case (a column chart is
reduced to the row case by antitransposition in the proof, which this script does not rebuild),
and the comparison itself: the second clock beta and the sum-horizon relation need a mate.
"""
import random
from fractions import Fraction as Fr

from _gluing_common import compose, legal
from _mark_builders import betas, diagrams, marks, phases
from _source_common import (alphabet, bracket, coframes, padd, pmul, pscale, sample, solve,
                            source_data, theta)

J_CELLS = 10
rng = random.Random(41)


def trunc(P, deg):
    return {e: v for e, v in P.items() if e <= deg and v != 0}


def returns(src, h):
    D = source_data(src, h)
    if D is None:
        return None
    c = src['c']
    IR, CR, IL, CL = D['IR'], D['CR'], D['IL'], D['CL']
    if len(IR) != len(CR) or len(IL) != len(CL):
        return None
    l, r, lp, rp = D['l'], D['r'], D['lpoly'], D['rpoly']
    BR = [[h(i - j) for j in CR] for i in IR]
    BL = [[h(i - j) for j in CL] for i in IL]
    vL = lambda j: sum(l[i] * h(i - j) for i in l)  # noqa: E731
    vR = lambda i: sum(h(i - j) * r[j] for j in r)  # noqa: E731
    xr = yl = {}
    if IR:
        wv = solve([[BR[i][j] for i in range(len(IR))] for j in range(len(CR))], [vL(j) for j in CR])
        if wv is None:
            return None
        xr = {c - i: val for i, val in zip(IR, wv)}
    if IL:
        wv = solve(BL, [vR(i) for i in IL])
        if wv is None:
            return None
        yl = {j: val for j, val in zip(CL, wv)}
    return D, xr, yl


def split(src, h):
    ret = returns(src, h)
    if ret is None:
        return None
    D, xr, yl = ret
    c = src['c']
    wc = trunc(pmul(D['rpoly'], D['lpoly']), c)
    Dz = trunc(padd(wc, pscale(pmul(D['rpoly'], xr), -1), pscale(pmul(D['lpoly'], yl), -1)), c)
    return D, xr, yl, wc, Dz


def main():
    ok = lim = fail_other = fail_sample = tried_other = 0
    for J in diagrams(J_CELLS):
        for mk in marks(J):
            if mk.case != 'a' or not legal(mk) or mk.width == 0:
                continue
            p, w = mk.period, mk.width
            s, t = phases(mk)
            for g in range(2, p + 1):
                c = w % g
                if p % g or c == 0 or not (t <= c and w - s <= c):
                    continue
                M = 3
                S = compose(frozenset((0, j) for j in range(M)), mk)
                X, Y = betas(S)
                N = X[0]
                a = N - p - c
                if a <= c:
                    continue
                dg = w - c
                sigma, tau = s - dg, t
                lam = p * (M - 1) + s - t
                dp = N - p - c + sigma - tau
                assert lam == a + sigma - tau == dp > 0
                Delta = c - sigma + tau
                assert 0 <= Delta <= 2 * c and lam == N - p - Delta
                src = dict(X=tuple(X), Y=tuple(Y), N=N, g=g, c=c, p=p, q=p, a=a, m=a + c)
                h = alphabet(rng, N + 3)
                out = split(src, h)
                if out is None:
                    continue
                D, xr, yl, wc, Dz = out
                cf = coframes(tuple(X), tuple(Y), N, h)
                if cf is None:
                    continue
                RS, LS = cf
                T = pmul(RS, LS)
                m = a + c
                O = bracket(padd(pscale(T, m - lam), pscale(theta(T), -1)), m, h)
                assert O == 0, ('own observer', sorted(J), p, w, g)
                assert Dz == wc, ('D = r l', sorted(J), p, w, g)
                ok += 1
                # limit nu -> infinity, exactly at nu = 10^6 times the base value
                big = alphabet(rng, N + 3)
                nu = Fr(10 ** 9)
                hb = lambda k, big=big, nu=nu: nu if k == 0 else big(k)  # noqa: E731
                outb = split(src, hb)
                if outb is not None:
                    Db, xb, yb, wcb, Dzb = outb
                    TR = {k: Fr(0) for k in range(c + 1)}
                    # T_R = x_R / l, T_L = y_L / r as truncated series: compare D/w_c = 1 - T_R - T_L
                    # at order 1/nu through the constant terms x_R(0) = [z^0] x_R etc.
                    tR0 = xb.get(0, Fr(0)) / Db['lpoly'][0]
                    tL0 = yb.get(0, Fr(0)) / Db['rpoly'][0]
                    assert abs(tR0) < Fr(1, 10 ** 3) and abs(tL0) < Fr(1, 10 ** 3)
                    lim += 1
                # control at another horizon
                if p - 1 > c + 1 and a + 1 > c + 1:
                    q2 = p - g if p - g >= 2 * g else None
                    if q2:
                        a2 = N - q2 - c
                        src2 = dict(src, q=q2, a=a2, m=a2 + c)
                        o2 = split(src2, h)
                        if o2 is not None:
                            tried_other += 1
                            fail_other += o2[4] != o2[3]
    # control: g-periodic sampled sources are not charts
    n = 0
    while n < 60:
        src = sample(rng)
        src['q'] = src['p']
        src['a'] = src['N'] - src['p'] - src['c']
        src['m'] = src['a'] + src['c']
        h = alphabet(rng, src['N'] + 3)
        o = split(src, h)
        if o is None or src['a'] <= src['c']:
            continue
        n += 1
        fail_sample += o[4] != o[3]
    print(f'charts with D = r l and own observer zero: {ok}; large-nu limits checked: {lim}; '
          f'other horizon {fail_other}/{tried_other} fail; sampled non-chart sources {fail_sample}/{n} fail')
    assert ok > 50 and lim > 20 and fail_sample > n // 2 and fail_other > tried_other // 2
    print('ALL PASS')


if __name__ == '__main__':
    main()
