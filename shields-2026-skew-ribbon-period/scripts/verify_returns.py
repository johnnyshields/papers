r"""Paper section `sec:response` (The complete scalar and its second channel).

Targets `eq:source-truncations`, `eq:cap-duality`, `eq:paired-current`, the elimination
formula `O = -eps J + s K - <R^0 C_1 + L^0 D_1>` behind `eq:whole-observers`,
and the exact identity `eq:gamma-functional`, on sampled periodic sources
(`_source_common.sample`: g-periodic boundary words, singleton pins).

Everything is solved from definitions at a seeded rational alphabet with rational `h_0 = nu`:
the whole coframes `R_S, L_S` from the proper matrix of the source; the window coframes `R^0, L^0`
from the base rows and columns below `a` (above `N - a`); the cap vectors `l, r` from their equations;
the splices `sminus, splus` from the flag formulas, their normalized functions `f_E, f_F` as `h_m`
minus the proper Schur complement of each splice, the contact vectors `R_E` (right, normalized at
column 0, solving every row but the top) and `L_F` (left, normalized at row `m`, solving every
column but 0), the cross kernel `K = L_F M R_E` and the balanced current
`J = L_F ((m - 0) M - X M + M Y) R_E` over the union of labels.  Asserted for every source:
`eq:source-truncations` through degree `m` (corrections `rho`, `zeta` solved from the square return
systems); `K = <R^0 L^0>`, `f_E = <R^0 l>`, `f_F = <L^0 r>` and the paired-current formula; the Hall
observer `O_H = [z^m] H R_S L_S` equals `K - <R^0 x_R + L^0 y_L>` and, for several clocks, the
ordinary observer `[z^m] H (m - lambda - Theta)(R_S L_S)` equals the elimination formula with
`C_1 = x_R^0 - lambda x_R + Theta l`, `D_1 = y_L^0 - lambda y_L + Theta r`.  The identity
`eq:gamma-functional` is checked as algebra in the functional `<.>` on random data satisfying its
hypothesis `r C_1 + l D_1 = s r l mod z^(c+1)`.
# TODO: not yet verified -- statements whose hypothesis is the original comparison itself (two
# Schur-equal source-minimal charts with periods `p > q`): `thm:scalar-synchronization`,
# `eq:unit-inclusion`, `eq:private-weights`, `lem:phase-confinement`, `lem:propagation`,
# `prop:whole-structure`, `eq:low-corner`, `eq:open-middle`, `lem:sum-horizon` on an actual
# comparison, `eq:complementary`, the end-pole expansion and outward filter of `thm:end-filter` on
# an actual comparison, `prop:alternative-scalar` and `eq:modified-cap-table`.  The main theorem
# concludes `p = q`, so no pair with `p > q` exists to sample; only the lemmas that do not
# assume Schur equality are checked on sampled sources (`verify_geometry.py`, this script,
# `verify_whole_sign.py`, `check_cramer_signs.py`).
"""
import random
from fractions import Fraction as Fr

from _source_common import (alphabet, bracket, coframes, fS, padd, pmul, pscale, sample, solve,
                            source_data, splice, theta)


def vec_coframe(Xl, Yl, N, h):
    """Right vector on columns (dict col -> value, R(0)=1) and left vector on rows (row -> value, L(N)=1)."""
    cf = coframes(Xl, Yl, N, h)
    if cf is None:
        return None
    R, L = cf
    return dict(R), {N - e: v for e, v in L.items()}


def trunc(P, deg):
    return {e: v for e, v in P.items() if e <= deg and v != 0}


def main():
    rng = random.Random(77)
    n = 0
    stats = dict(trunc=0, duality=0, observers=0, gamma=0)
    while n < 120:
        s = sample(rng)
        X, Y, N, c, q, a, m = (s[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a', 'm'))
        h = alphabet(rng, N + 3)
        D = source_data(s, h)
        cf = coframes(X, Y, N, h)
        if D is None or cf is None:
            continue
        RS, LS = cf
        R0, L0, l, r, lp, rp = D['R0'], D['L0'], D['l'], D['r'], D['lpoly'], D['rpoly']
        IR, CR, IL, CL = D['IR'], D['CR'], D['IL'], D['CL']
        BR = [[h(i - j) for j in CR] for i in IR]
        BL = [[h(i - j) for j in CL] for i in IL]
        P = {i: sum(coef * h(a + i - e) for e, coef in R0.items() if a + i - e >= 0) for i in range(c + 1)}
        Q = {j: sum(coef * h(m - j - e) for e, coef in L0.items() if m - j - e >= 0) for j in range(c + 1)}
        rho = solve(BR, [P[i] for i in IR]) if IR else []
        zeta_ = solve([[BL[i][j] for i in range(len(IL))] for j in range(len(CL))], [Q[j] for j in CL]) if IL else []
        if rho is None or zeta_ is None:
            continue
        n += 1
        # eq:source-truncations
        Rt = dict(R0)
        for j, v in zip(CR, rho):
            Rt[a + j] = Rt.get(a + j, 0) - v
        Lt = dict(L0)
        for i, v in zip(IL, zeta_):
            Lt[m - i] = Lt.get(m - i, 0) - v
        assert trunc(Rt, m) == trunc(RS, m) and trunc(Lt, m) == trunc(LS, m)
        stats['trunc'] += 1
        # splices, normalized functions, contact vectors, K and J
        E = splice(X, Y, N, a - 1, N - c - 1)
        F = splice(X, Y, N, c, q + c)
        fE, fF = fS(*E, h), fS(*F, h)
        vE, vF = vec_coframe(*E, h), vec_coframe(*F, h)
        if None in (fE, fF, vE, vF):
            continue
        RE = vE[0]
        LF = vF[1]
        K = sum(LF[x] * h(x - y) * RE[y] for x in LF for y in RE)
        Jv = sum(LF[x] * RE[y] * h(x - y) * (m - x + y) for x in LF for y in RE)
        assert K == bracket(pmul(R0, L0), m, h)                                          # K = <R0 L0>
        assert fE == bracket(pmul(R0, lp), m, h)                                          # f_E = <R0 l>
        assert fF == bracket(pmul(L0, rp), m, h)                                          # f_F = <L0 r>
        Jf = bracket(padd(theta(pmul(R0, L0)), pscale(pmul(R0, theta(lp)), -1),
                          pscale(pmul(L0, theta(rp)), -1)), m, h)
        assert Jv == Jf                                                                   # eq:paired-current
        stats['duality'] += 1
        # x_R, y_L, weighted projections
        vL = lambda j: sum(l[i] * h(i - j) for i in l)
        vR = lambda i: sum(h(i - j) * r[j] for j in r)
        uL = lambda j: sum((i - j) * l[i] * h(i - j) for i in l)
        uR = lambda i: sum((i - j) * h(i - j) * r[j] for j in r)

        def xR(vec):
            if not IR:
                return {}
            w = solve([[BR[i][j] for i in range(len(IR))] for j in range(len(CR))], [vec(j) for j in CR])
            return {c - i: val for i, val in zip(IR, w)}

        def yL(vec):
            if not IL:
                return {}
            w = solve(BL, [vec(i) for i in IL])
            return {j: val for j, val in zip(CL, w)}
        xr, yl, xr0, yl0 = xR(vL), yL(vR), xR(uL), yL(uR)
        # Hall observer
        OH = bracket(pmul(RS, LS), m, h)
        assert OH == K - bracket(padd(pmul(R0, xr), pmul(L0, yl)), m, h)
        # ordinary observers
        for lam in (Fr(-2), Fr(0), Fr(5, 3)):
            T = pmul(RS, LS)
            Oq = bracket(padd(pscale(T, m - lam), pscale(theta(T), -1)), m, h)
            C1 = padd(xr0, pscale(xr, -lam), theta(lp))
            D1 = padd(yl0, pscale(yl, -lam), theta(rp))
            assert Oq == -Jv + (m - lam) * K - bracket(padd(pmul(R0, C1), pmul(L0, D1)), m, h)
        stats['observers'] += 1
        # eq:gamma-functional as algebra
        for _ in range(2):
            sS = Fr(rng.randint(-5, 5), rng.randint(1, 3))
            C1 = {e: Fr(rng.randint(-4, 4)) for e in range(c + 1)}
            rl = trunc(pmul(rp, lp), c)
            # D1 = (s r l - r C1) / l  mod z^(c+1)
            num = trunc(padd(pscale(pmul(rp, lp), sS), pscale(pmul(rp, C1), -1)), c)
            D1 = {}
            rem = dict(num)
            for k in range(c + 1):                       # power-series division by l (l(0) = 1)
                coef = rem.get(k, 0)
                D1[k] = coef
                for e, v in lp.items():
                    if k + e <= c:
                        rem[k + e] = rem.get(k + e, 0) - coef * v
            assert trunc(padd(pmul(rp, C1), pmul(lp, D1)), c) == trunc({e: sS * v for e, v in rl.items()}, c)
            gam = {}
            rem = dict(C1)
            for k in range(c + 1):
                coef = rem.get(k, 0)
                gam[k] = coef
                for e, v in lp.items():
                    if k + e <= c:
                        rem[k + e] = rem.get(k + e, 0) - coef * v
            for eps in (0, 1):
                O = -eps * Jv + sS * K - bracket(padd(pmul(R0, C1), pmul(L0, D1)), m, h)
                Tk = lambda k: bracket(padd(pmul(R0, trunc(pmul({k: Fr(1)}, lp), c)),
                                            pscale(pmul(L0, trunc(pmul({k: Fr(1)}, rp), c)), -1)), m, h)
                rhs = (-eps * Jv + gam[0] * (K - fE) + (sS - gam[0]) * (K - fF)
                       - sum(gam[k] * Tk(k) for k in range(1, c + 1)))
                assert O == rhs, (O, rhs)
            stats['gamma'] += 1
    print(f"sources {n}: {stats}")
    print("PASS")


if __name__ == "__main__":
    main()
