#!/usr/bin/env python3
"""Paper section `sec:inflation-proof` (The exact inflation threshold).  Target `thm:sharp-inflation`, for EVERY
inflation parameter t >= 0 at each listed (a, b, c, alpha); with `cor:inflation-no-escape` as a consequence there.

`check_inflation_collapse_threshold.py` computes the complete class for t = 0 .. p + 2.  Here the parameter t is
removed by a shift argument, so a finite computation covers every t.

  (1) Inflation shifts every Jacobi-Trudi label by t.  For a profile (rho; overlaps) the beta lists of
      `_composition_engine.beta` satisfy x_i - x_{i+1} = rho_i - a_i + 1, unchanged when every row and every
      overlap grows by t, while y = x - rho loses t; so x_i - y_j becomes x_i - y_j + t.  Asserted on every
      candidate profile below, against the engine.
  (2) The complete class of a diagram D is cut out of the orderings of its row and overlap multisets (two Schur
      invariants), and the orderings for I_t D are the inflations of those for D; connectedness
      0 <= g_i < min(r_i, r_{i+1}) is preserved by inflation in both directions on these orderings.
  (3) Let m be the least Jacobi-Trudi label over D and every connected candidate, and T0 = max(0, 1 - m).
      For t >= T0 every label of every candidate is positive, so s_{I_t X} is the image of s_{I_T0 X} under
      the injective substitution h_k -> h_{k + t - T0}; equality between D and a candidate is therefore the
      same at every t >= T0, and the class at t is the inflation of the class at T0.
  So the statement for all t follows from the complete class at t = 0 .. max(T0, p), which is computed, with
  the set-level prediction of `thm:sharp-inflation` asserted at each.
"""
import itertools
import sys

import importlib.util
import os

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("eng", os.path.join(HERE, "_composition_engine.py"))
E = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(E)


def build(L, g):
    return E.cells_from_rho_a(list(L), [x + 1 for x in g])


def prof(cells):
    ri = E.row_intervals(cells)
    if ri is None:
        return None
    idx = sorted(ri)
    if idx != list(range(idx[0], idx[0] + len(idx))):
        return None
    L = tuple(ri[i][1] - ri[i][0] + 1 for i in idx)
    g = tuple(min(ri[idx[k]][1], ri[idx[k + 1]][1]) - max(ri[idx[k]][0], ri[idx[k + 1]][0])
              for k in range(len(idx) - 1))
    return (L, g)


def schur(cells):
    return tuple(sorted(dict(E.jt_of_cells(cells)).items()))


def inflate(L, g, t):
    return tuple(x + t for x in L), tuple(x + t for x in g)


def F_alpha(a, b, c, alpha):
    """G_alpha of `eq:thin-domain`: E_m = (a, (a+b)^{m-1}, b; c^m), joined with gap 0."""
    L, g = (), ()
    for i, m in enumerate(alpha):
        if i:
            g += (0,)
        L += (a,) + (a + b,) * (m - 1) + (b,)
        g += (c,) * m
    return L, g


def ribbon_class_size(alpha):
    """(|R(alpha)|, R(alpha)) by comparing ribbon Schur functions of every composition of |alpha|."""
    M = sum(alpha)
    comps = []
    for k in range(1, M + 1):
        for cut in itertools.combinations(range(1, M), k - 1):
            pts = (0,) + cut + (M,)
            comps.append(tuple(pts[i + 1] - pts[i] for i in range(k)))
    by = {}
    for bb in comps:
        by.setdefault(schur(E.cells_from_rho_a(list(bb), [1] * (len(bb) - 1))), []).append(bb)
    for v in by.values():
        if tuple(alpha) in v:
            return len(v), v

CASES = [
    (2, 3, 1, (1, 2)), (2, 3, 1, (2, 1)), (3, 4, 1, (1, 2)), (2, 4, 1, (1, 2)), (3, 5, 2, (1, 2)),
    (2, 5, 1, (1, 2)), (3, 4, 2, (1, 2)), (2, 3, 1, (1, 3)), (2, 3, 1, (3,)), (3, 4, 1, (2, 1)),
    (2, 3, 1, (1, 1, 2)), (4, 5, 1, (1, 2)),
]


def labels(L, g):
    x, y = E.beta(list(L), [s + 1 for s in g])
    return [xi - yj for xi in x for yj in y]


def candidates(L, g):
    n = len(L)
    out = []
    for Lp in set(itertools.permutations(L)):
        for gp in set(itertools.permutations(g)):
            if any(not (0 <= gp[i] < min(Lp[i], Lp[i + 1])) for i in range(n - 1)):
                continue
            out.append((Lp, gp))
    return out


def klass(L, g):
    D = build(L, g)
    target = schur(D)
    out = set()
    for Lp, gp in candidates(L, g):
        c2 = build(Lp, gp)
        if len(c2) == len(D) and E.is_connected_skew(c2) and prof(c2) == (Lp, gp) and schur(c2) == target:
            out.add(E.normalize(c2))
    return out


def main():
    for a, b, c, alpha in CASES:
        p = a - c
        rsize, members = ribbon_class_size(alpha)
        L0, g0 = F_alpha(a, b, c, alpha)
        cands = candidates(L0, g0)
        # (1) the uniform label shift, and (2) inflation commutes with the candidate set and connectedness
        for Lp, gp in cands:
            base = labels(Lp, gp)
            for t in (1, 2, 5):
                Lt, gt = inflate(Lp, gp, t)
                assert labels(Lt, gt) == [v + t for v in base]
        for t in (1, 3):
            assert sorted(candidates(*inflate(L0, g0, t))) == sorted(inflate(Lp, gp, t) for Lp, gp in cands)
        m = min(min(labels(Lp, gp)) for Lp, gp in cands)
        T0 = max(0, 1 - m)
        top = max(T0, p) + 1
        for t in range(0, top + 1):
            L, g = inflate(L0, g0, t)
            D = build(L, g)
            got = klass(L, g)
            if t < p:
                want = set()
                for beta in members:
                    Db = build(*inflate(*F_alpha(a, b, c, beta), t))
                    if E.is_connected_skew(Db):
                        want |= {E.normalize(Db), E.rotate(Db)}
                assert len(want) == 2 * rsize
            else:
                want = {E.normalize(D), E.rotate(D)}
                assert len(want) == 2
            assert got == want, (a, b, c, alpha, t, len(got), len(want))
        assert all(v + top >= 1 for Lp, gp in cands for v in labels(Lp, gp))
        print("E=(%d,%d;%d) alpha=%s p=%d: class asserted for t = 0..%d; every label positive from t = %d, "
              "so the class at t >= %d is the shift of that at %d: thm:sharp-inflation for every t"
              % (a, b, c, alpha, p, top, T0, top, top))
    print("ALL PASS")


if __name__ == "__main__":
    sys.exit(main())
