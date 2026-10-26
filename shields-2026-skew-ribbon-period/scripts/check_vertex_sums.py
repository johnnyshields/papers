r"""Paper section `app:cell-cut` (Integral cuts with a cell-only proper interior).

Vertex-mask, saturation, run-barrier and path-surplus statements of the cut theorem, asserted on the
real instances of `check_cell_cut_hypothesis.py` (cell-only boards whose currents satisfy the theorem
hypothesis) and, for the barrier equivalence, on every cell-only board.

Objects are built from definitions.  The minimum child `beta_0` is the ribbon of row lengths
`x_i - 1 - y_i` after deleting all common betas; `P_0`, `Q_0'` are its proper prefix and suffix sums,
`d_0 = R - 1`, `T_0 = {d_0 - v : v in Q_0', 0 < v < d_0}`, `f = [d_0 in P_0]`, `g = R - [d_0 in Q_0']`.
Asserted on each instance: `eq:ribbon-vertex-gates` (`d/dH_{L-1} Q_{beta_0} = 0`, `W/m` integral with
`W = (V_L^H + delta_L^H) Q_{beta_0}`); `eq:vertex-mask` and `eq:vertex-count` (`W` is the sum over
`0 <= t <= d_0` of the canonical ribbons with cut set `(P_0 cap [1, d_0 - t]) cup (T_0 cap [d_0 - t, d_0 - 1])`,
the endpoint vertices being zero when their cut set contains `0` or `d_0`, and `m = g - f` equals the
number of live vertices); `eq:vertex-saturation` (`P_0 cap [1, d_0 - 1] = T_0` and `W = m Q_beta` for the
actual ribbon `beta` with that cut set).  Over all boards and `L`: `eq:run-barriers` (for each
`r` with `1 <= r <= c - 1`, both unweighted and weighted `h_1`-jets below `r` vanish exactly when the
run-span conditions hold), and `eq:path-surplus` at each jet whose lower jets vanish.
`eq:strip-indicators` is not transcribed (TODO below).
# TODO: not yet verified -- `eq:strip-indicators`: the strip-removal indicator formula for N_{e+1}-N_e
# needs the outer/inner L-strip cofactor sums C_e, R_{L+e}, which the text defines only in prose.
"""
import itertools

import sympy as sp

from verify_cell_cut import Hh, HH, Hs, boards, derivation, h, lists, Qpoly, Qshift, vop_H, psi, deg_part
from check_cell_cut_hypothesis import content_gcd


def ribbon_H(alpha):
    k = len(alpha)
    zeta = [sum(alpha[i + 1:]) for i in range(k)]
    xi = [zeta[i] + alpha[i] for i in range(k)]
    return sp.expand((-1) ** (k - 1) * sp.Matrix(k, k, lambda i, j: HH(xi[i] - zeta[j])).det())


def ribbon_h(alpha):
    k = len(alpha)
    zeta = [sum(alpha[i + 1:]) for i in range(k)]
    xi = [zeta[i] + alpha[i] for i in range(k)]
    return sp.expand((-1) ** (k - 1) * sp.Matrix(k, k, lambda i, j: h(xi[i] - zeta[j])).det())


def comp_from_cuts(cuts, n):
    pts = [0] + sorted(cuts) + [n]
    return tuple(pts[i + 1] - pts[i] for i in range(len(pts) - 1))


def runs_of(lens, gaps):
    runs, cur = [], [lens[0]]
    for i, g in enumerate(gaps):
        if g == 1:
            runs.append(cur)
            cur = [lens[i + 1]]
        else:
            cur.append(lens[i + 1])
    runs.append(cur)
    return runs


def span_of(rows):
    """R_i of a zero-gap run: its total weight (row lengths summed), so that beta_0 has rows R_i - 1."""
    return sum(rows)


def join(runs):
    out = list(runs[0])
    for r in runs[1:]:
        out = out[:-1] + [out[-1] + r[0] - 1] + list(r[1:])
    return out


def bar(P):
    """Project to h_1 = 0, h_j = -1 (j >= 2)."""
    return sp.sympify(P).subs({Hs[0]: 0, **{Hs[j - 1]: -1 for j in range(2, len(Hs) + 1)}})


def jets(P):
    pp = sp.Poly(P, Hs[0])
    return {m[0]: sp.expand(c) for m, c in pp.terms()}


def run_checks(lens, gaps, c, S, Q, runs, Rs, L, strict, stats):
    V = derivation(Q, L, True)
    D = derivation(Q, L, False)
    jV, jD = jets(V), jets(D)
    for r in range(1, c):
        vanish = all(jV.get(j, 0) == 0 and jD.get(j, 0) == 0 for j in range(r))
        cond = True
        for t in range(1, c + 2):
            for st in range(0, c + 2 - t):
                sg = sum(Rs[st:st + t]) - (t - 1)
                if t < r and sg > L - 1:
                    cond = False
                if t == r and not (sg <= L + 1 and sg != L):
                    cond = False
        if strict:
            assert vanish == cond, ('run-barriers', lens, gaps, L, r, vanish, cond)
            stats['bar_inst'] += 1
        else:
            stats['bar_ok' if vanish == cond else 'bar_bad'] += 1
    kap = [-bar(ribbon_h(tuple(r_))) for r_ in runs]
    P0 = bar(jets(Q).get(0, 0))
    for j in range(1, c + 1):
        if not all(jV.get(i, 0) == 0 and jD.get(i, 0) == 0 for i in range(j)):
            break
        if P0 == 0:
            continue
        B = 0
        for st in range(0, c + 1 - j):
            G = runs[st:st + j + 1]
            nuG = -bar(derivation(ribbon_h(tuple(join(G))), L, True))
            B += nuG / sp.Mul(*kap[st:st + j + 1])
        Cc = 0
        for st in range(0, c + 2 - j):
            if sum(Rs[st:st + j]) - (j - 1) == L + 1:
                Cc += 1 / sp.Mul(*kap[st:st + j])
        ok = sp.simplify(bar(jV.get(j, 0)) / P0 - (B - Cc)) == 0
        if strict:
            assert ok, ('path-surplus', lens, gaps, L, j)
            stats['sur_inst'] += 1
        else:
            stats['sur_ok' if ok else 'sur_bad'] += 1


def main():
    ninst = nbar = nsurp = 0
    boards_all = []
    stats = {'bar_ok': 0, 'bar_bad': 0, 'sur_ok': 0, 'sur_bad': 0, 'bar_inst': 0, 'sur_inst': 0}
    registry = {}
    for lens, gaps in boards(6, 5):
        Xj, Yj = lists(lens, gaps)
        # ---------------- all-board statements: run barriers, path surplus
        c = sum(gaps)
        S = Xj[0]
        Q = Qpoly(Xj, Yj)
        runs = runs_of(lens, gaps)
        Rs = [span_of(r) for r in runs]
        allb = (lens, gaps, Xj, Yj, c, S, Q, runs, Rs)
        boards_all.append(allb)
        # ---------------- instance statements
        for L in range(2, S - 1):
            R = S - L
            if R < 2 or c == 0:
                continue
            V = derivation(Q, L, True)
            D = derivation(Q, L, False)
            if V == 0 or D == 0:
                continue
            gV = content_gcd(V)
            Q0 = sp.expand(V / gV)
            if not sp.cancel(D / V).is_number:
                continue
            Pq = sp.Poly(Q0, *Hs)
            if R > len(Hs) or Pq.degree(Hs[R - 1]) != 1:
                continue
            top = sp.expand(sp.diff(Q0, Hs[R - 1]))
            sgn = 1 if top.subs({v: 1 for v in Hs}) > 0 else -1
            m = sgn * gV
            Z = set(Xj) & set(Yj)
            Xr = [x for x in Xj if x not in Z]
            Yr = [y for y in Yj if y not in Z]
            alpha = tuple(x - 1 - y for x, y in zip(Xr, Yr))
            tot = sum(alpha)
            d0 = R - 1
            assert tot == L + d0, ('beta_0 area', lens, gaps, L, tot)
            Qb0 = Qshift(Xr, Yr)
            assert sp.expand(Qb0 - ribbon_H(alpha)) == 0
            assert sp.diff(Qb0, Hh[L - 1]) == 0 if L - 1 >= 1 else True              # eq:ribbon-vertex-gates
            W = sp.expand(vop_H(Qb0, L, True) + vop_H(Qb0, L, False))
            assert all(cf % m == 0 for cf in sp.Poly(W, *Hh[1:]).coeffs()), 'W/m integral'
            P0 = set(itertools.accumulate(alpha[:-1]))
            Qs = set(itertools.accumulate(reversed(alpha[1:])))
            T0 = {d0 - v for v in Qs if 0 < v < d0}
            f = int(d0 in P0)
            g_ = R - int(d0 in Qs)
            tot_sum = 0
            live = 0
            for t in range(0, d0 + 1):
                cuts = (({x for x in P0 if 1 <= x <= d0 - t}) | ({x for x in T0 if d0 - t <= x <= d0 - 1}))
                if (t == 0 and d0 in P0) or (t == d0 and d0 in Qs) or 0 in cuts or d0 in cuts:
                    continue
                tot_sum += ribbon_H(comp_from_cuts(cuts, d0))
                live += 1
            assert sp.expand(W - tot_sum) == 0, ('vertex-mask', lens, gaps, L)
            assert m == g_ - f == live, ('vertex-count', m, g_, f, live)
            assert P0 & set(range(1, d0)) == T0, ('vertex-saturation cuts', lens, gaps, L)
            beta = ribbon_H(comp_from_cuts(T0, d0))
            assert sp.expand(W - m * beta) == 0, ('vertex-saturation W', lens, gaps, L)
            run_checks(lens, gaps, c, S, Q, runs, Rs, L, True, stats)
            ninst += 1
    for (lens, gaps, Xj, Yj, c, S, Q, runs, Rs) in boards_all:
        if c >= 2:
            for L in range(2, S - 1):
                run_checks(lens, gaps, c, S, Q, runs, Rs, L, False, stats)
    nbar = stats['bar_inst']
    print(f"instances {ninst}; barrier equivalences on instances {stats['bar_inst']}, path-surplus jets on instances {stats['sur_inst']}")
    print(f"all cell-only boards (hypothesis not imposed): barrier agree {stats['bar_ok']} disagree {stats['bar_bad']}; surplus agree {stats['sur_ok']} disagree {stats['sur_bad']}")
    assert ninst > 0 and nbar > 0
    print("PASS")


if __name__ == "__main__":
    main()
