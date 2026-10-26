r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

The native row-probe coframe at the empty section (app:aligned, prop:noncell-realization,
eq:empty-section).

For a connected inner E and an empty mark (width 0, period q = N_E), the row probe Row_j o U has
beta lists X = (N, I), Y = (C, 0) with N = jq.  Let A = JT(I, C) be its proper matrix and
G = 1 - sum u_c z^c the complete coframe, A u = (h_{I_i}).  At the empty section
(G^dag = g - 1 + S(z^q), H^dag = (l - 1 + Y(z^q) S(z^q)) / G^dag) the script asserts, in exact
rational arithmetic, for j = 1, 2, 3:
  * the complete coframe of the probe equals the power series G^dag / S on [0, N]
    (so the proper matrix is invertible and the section solves every proper row);
  * the top residual [z^N](H^dag G) equals Y_j;
  * ProbeLists: X_j = {jq} + U_t (X'_E + tq), Y_j = {0} + U_t (Y'_E + tq), X'_E = X_E minus its top,
    Y'_E = Y_E minus its bottom (0), as multisets (no label m q, 0 < m < j, is shared);
  * s_P(h) = (-1)^n det A * Y_j   (the Schur complement of the bordered matrix);
  * (-1)^n det A_j is the same number for two independent draws of (S, Y) and equals xi^j,
    xi = (-1)^{n_E} det A_E at the low labels, so Phi(h_j) = xi^j Y_j (the Lean statement
    empty_section_calibration).
"""
import random
import sys
from fractions import Fraction

import check_noncell_section as c
from check_row_probe_caps import (is_skew, connected, legal_marks, probe, random_skew, betas, solve)

def _det(M):
    n = len(M)
    M = [r[:] for r in M]
    d = Fraction(1)
    for k in range(n):
        p = next((r for r in range(k, n) if M[r][k] != 0), None)
        if p is None:
            return Fraction(0)
        if p != k:
            M[k], M[p] = M[p], M[k]
            d = -d
        d *= M[k][k]
        for r in range(k + 1, n):
            f = M[r][k] / M[k][k]
            M[r] = [x - f * y for x, y in zip(M[r], M[k])]
    return d

def main():
    rng = random.Random(5)
    done = 0
    for _ in range(20000):
        E = random_skew(rng, rng.randint(2, 4))
        if not is_skew(E) or not connected(E) or not 2 <= len(E) <= 9:
            continue
        for w, v, ph in legal_marks(E):
            if w != 0:
                continue
            q = c.N_E_(E)
            if q < 2:
                continue
            J = 3
            probes = {j: probe(E, v, j) for j in range(1, J + 1)}
            xiE, zeE = betas(E)
            for j in range(1, J + 1):
                if not (is_skew(probes[j]) and connected(probes[j])):
                    continue
                xj, zj = betas(probes[j])
                assert sorted(xj) == sorted([j * q] + [x + t * q for t in range(j) for x in xiE[1:]]), \
                    ('xi list of the probe', sorted(E), j, xj, xiE)
                assert sorted(zj) == sorted([0] + [z + t * q for t in range(j) for z in zeE[:-1]]), \
                    ('zeta list of the probe', sorted(E), j, zj, zeE)
            if not all(is_skew(P) and connected(P) for P in probes.values()):
                continue
            lo = {m: Fraction(rng.randint(-5, 5), rng.randint(1, 4)) for m in range(1, q)}
            hh = dict(lo)
            for m in range(q, 4 * q + 8):
                hh[m] = Fraction(rng.randint(-9, 9), rng.randint(1, 5))
            try:
                g = c.coframe_low(probes[2], hh, q)
            except (StopIteration, ZeroDivisionError):
                continue
            ncut = J * q + 4
            sig = {}
            for draw in range(2):
                Y = [Fraction(1)] + [Fraction(rng.randint(1, 6), rng.randint(1, 3)) for _ in range(J)]
                S = [Fraction(1)] + [Fraction(rng.randint(1, 6), rng.randint(1, 3)) for _ in range(J)]
                H = c.section(g, lo, q, None, Y, S, ncut)
                hv = {m: H[m] for m in range(1, ncut)}

                def h(m):
                    return Fraction(0) if m < 0 else (Fraction(1) if m == 0 else hv.get(m, Fraction(0)))
                Sq = [Fraction(0)] * ncut
                for i, s in enumerate(S):
                    if i * q < ncut:
                        Sq[i * q] = s
                Gd = [Fraction(0)] * ncut
                for k in range(q):
                    Gd[k] += g[k]
                Gd[0] -= 1
                for k in range(ncut):
                    Gd[k] += Sq[k]
                Gq = c.ser_mul(Gd, c.ser_inv(Sq, ncut), ncut)
                for j in range(1, J + 1):
                    xi, ze = betas(probes[j])
                    I, C = xi[1:], ze[:-1]
                    n = len(I)
                    N = xi[0]
                    A = [[h(I[i] - C[k]) for k in range(n)] for i in range(n)]
                    u = solve(A, [h(I[i]) for i in range(n)])
                    Gp = {0: Fraction(1)}
                    for k in range(n):
                        Gp[C[k]] = Gp.get(C[k], 0) - u[k]
                    for k in range(N + 1):
                        assert Gp.get(k, 0) == Gq[k], ('coframe is not G/S', sorted(E), j, k)
                    res = sum(co * h(N - k) for k, co in Gp.items())
                    assert res == Y[j], ('top residual is not Y_j', sorted(E), j)
                    sP = c.schur(probes[j], hv)
                    dA = _det(A)
                    assert sP == (-1) ** n * dA * res, ('Schur complement', sorted(E), j)
                    sig.setdefault(j, []).append((-1) ** n * dA)
            nE = len(xiE) - 1
            IE, CE = xiE[1:], zeE[:-1]
            AE = [[(lo.get(IE[i] - CE[k], Fraction(0)) if IE[i] - CE[k] > 0 else
                    (Fraction(1) if IE[i] == CE[k] else Fraction(0))) for k in range(nE)]
                  for i in range(nE)]
            xi_E = (-1) ** nE * _det(AE)
            for j in sig:
                assert sig[j][0] == sig[j][1], ('xi^j depends on S, Y', sorted(E), j)
                assert sig[j][0] == xi_E ** j, ('(-1)^n det A_j is not xi^j', sorted(E), j)
            done += 1
        if done >= 12:
            break
    assert done >= 5
    print('empty marks checked', done)
    print('ALL PASS')

if __name__ == '__main__':
    main()
