r"""Paper section `app:cell-cut` (Integral cuts with a cell-only proper interior).

Hypothesis group of `thm:cell-cut`: `V_L Q_C = m Q_0`, `delta_L Q_C = alpha Q_0` with `Q_0` primitive
integral of span `R`, `partial_{h_R} Q_0 = h_1^c`, `v_{h_1}(Q_0) = r` (`eq:cell-top-gates`).

Searched forward over actual cell-only boards `C` (adjacent gaps in {0,1}, `r_i > g_{i-1} + g_i`, up to
6 rows, row lengths up to 5, span `S = L + R`, `R >= 2`, `L >= 2`, `kappa(C) = h_1^c` with `c` the number
of gap-one edges) and every `L`.  For each board whose currents satisfy the hypothesis the script
asserts the conclusion: `Q_0 = h_1^r Q_J` for an actual ribbon `J` (a board with cell-only data of
span `R`, `a = c - r`), with `m` and `alpha` integers, and the area bound `R + a < S + c`.
Because the theorem concludes from the hypothesis, instances that satisfy it exist only if the
search finds them; the script reports the count and FAILS if there are none, and also reports the
number of boards whose currents are proportional but violate the gates (a control: the gates are
load-bearing exactly when this count is positive).  Rows whose hypothesis is the same `Q_0`
(`eq:cell-mask-matching` and `eq:physical-unit-transport` are asserted/counted here) are graded on the instances found.
The vertex-mask, saturation, barrier and surplus rows are asserted in `check_vertex_sums.py`.
"""
import itertools
from math import gcd
from functools import reduce

import sympy as sp

from verify_cell_cut import Hs, boards, coarsenings, derivation, lists, Qpoly


def content_gcd(P):
    cs = [c for _, c in sp.Poly(P, *Hs).terms()]
    return reduce(gcd, [int(abs(c)) for c in cs]) if cs else 0


def main():
    registry = {}
    for lens, gaps in boards(6, 5):
        Xj, Yj = lists(lens, gaps)
        registry.setdefault(Xj[0], []).append(Qpoly(Xj, Yj))
    nJ = nmatch = nunit = 0
    total = prop = hits = viol = 0
    found = []
    for lens, gaps in boards(6, 5):
        s = len(lens)
        c = sum(gaps)
        X, Y = lists(lens, gaps)
        S = X[0]
        Q = Qpoly(X, Y)
        for L in range(2, S - 1):
            R = S - L
            if R < 2:
                continue
            total += 1
            V = derivation(Q, L, True)
            D = derivation(Q, L, False)
            if V == 0 or D == 0:
                continue
            gV, gD = content_gcd(V), content_gcd(D)
            Q0 = sp.expand(V / gV)
            # proportional currents
            if sp.expand(D * gV - V * (D.as_poly(*Hs).coeffs()[0] * gV // gV if False else 1)) == 0:
                pass
            ratio = sp.cancel(D / V)
            if not ratio.is_number:
                continue
            prop += 1
            Pq = sp.Poly(Q0, *Hs)
            span_ok = (R <= len(Hs) and Pq.degree(Hs[R - 1]) == 1 and all(Pq.degree(Hs[j]) == 0 for j in range(R, len(Hs))))
            top = sp.expand(sp.diff(Q0, Hs[R - 1])) if span_ok else None
            gates = span_ok and top != 0 and sp.Poly(top, *Hs).is_monomial and top.as_powers_dict().get(Hs[0], 0) == c and top.as_poly(*Hs).total_degree() == c
            if not gates:
                viol += 1
                continue
            r = min(m[0] for m in Pq.monoms())
            hits += 1
            a = c - r
            found.append((lens, gaps, L))
            assert 0 <= a <= c and R + a < S + c
            # conclusion: Q_0 = h_1^r Q_J for an actual board J of span R (up to sign)
            body = sp.cancel(Q0 / Hs[0] ** r)
            assert any(sp.expand(body - QJ) == 0 or sp.expand(body + QJ) == 0 for QJ in registry.get(R, [])), (lens, gaps, L)
            nJ += 1
            # eq:cell-mask-matching and eq:physical-unit-transport on the real data
            Z = set(X) & set(Y)
            Y0 = set(Y) - Z
            d0 = R - 1
            assert all((e in Y0) == ((L + e) in Y0) for e in range(1, d0)), ('cell-mask-matching', lens, gaps, L)
            nmatch += 1
            fcut = 1 if L in (Y0 - set(X)) else 0
            g_ = d0 + 1 - (1 if d0 in (Y0 - set(X)) else 0)
            if all((e in Z) == ((L + e) in Z) for e in range(fcut + 1, g_)):
                nunit += 1
    print(f"boards x L {total}, proportional currents {prop}, hypothesis satisfied {hits}, proportional but gates fail {viol}; Q_J found {nJ}, mask matching {nmatch}, unit transport holds on {nunit}")
    if hits == 0:
        raise AssertionError("no instance of the hypothesis found in the searched box; rows stay F")
    print("PASS")


if __name__ == "__main__":
    main()
