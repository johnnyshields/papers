"""Coordinator's independent check of lane O's leading-coefficient lemma (round 169).

CLAIM (r169-o.md, 'Sharpening'): for nonempty connected profiles P, Q with near-concatenation
(merger) P o Q, and L(P) = [h_{s(P)}] s_P where s(P) = x_1 - y_n is the span,
    L(P o Q) = L(P) L(Q),
each L independent of h_{s(P)} and containing no larger generator.  O proves it by the
block-triangular maximal cofactor.  The 1/2/4 class bound rests on it.

ROUTE, not O's: expand every Jacobi-Trudi determinant symbolically in sympy and read the
exact coefficient of the top generator; compare polynomials exactly.  No cofactor formula.

Merger (thm:exposure's convention): P o Q fuses P's last row with Q's first row,
rows (P_1..P_{n-1}, P_n + Q_1, Q_2..Q_m), gaps G_P then G_Q.

Asserts:
  (1) L(P o Q) = L(P) L(Q) exactly on every pair drawn from all connected zero-free profiles
      with 2-3 rows, row lengths <= 4 (and on one-row blocks, which O says the proof admits);
  (2) each L is free of its own top generator and of every larger one;
  (3) CONTROL: comparing with the top coefficient at the WRONG index (span minus one) fails,
      so the extraction is not vacuous.
Reports, without asserting, whether the identity also holds on non-zero-free profiles.
"""
import itertools
import sympy as sp

H = sp.symbols('h1:60')


def betas(rows, gaps):
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return x, y


def schur(rows, gaps):
    x, y = betas(rows, gaps)
    n = len(rows)
    hf = lambda k: sp.Integer(0) if k < 0 else (sp.Integer(1) if k == 0 else H[k - 1])
    return sp.expand(sp.Matrix(n, n, lambda i, j: hf(x[i] - y[j])).det(method='berkowitz')), x[0] - y[-1]


def lead(rows, gaps, shift=0):
    s, span = schur(rows, gaps)
    g = H[span - 1 - shift]
    return sp.expand(sp.Poly(s, g).coeff_monomial(g)), span


def merge(P, Q):
    (pr, pg), (qr, qg) = P, Q
    return tuple(pr[:-1]) + (pr[-1] + qr[0],) + tuple(qr[1:]), tuple(pg) + tuple(qg)


def valid(rows, gaps):
    return all(0 <= gaps[i] < min(rows[i], rows[i + 1]) for i in range(len(gaps)))


def zero_free(rows, gaps):
    x, y = betas(rows, gaps)
    return not (set(x) & set(y))


def profiles(nrows, rmax):
    for rows in itertools.product(range(1, rmax + 1), repeat=nrows):
        for gaps in itertools.product(range(0, rmax), repeat=nrows - 1):
            if valid(rows, gaps):
                yield rows, gaps


def main():
    pool = [((r,), ()) for r in (1, 2, 3)]
    for n in (2, 3):
        pool += [p for p in profiles(n, 4) if zero_free(*p)]
    ok = 0
    for P, Q in itertools.product(pool, repeat=2):
        M = merge(P, Q)
        if not valid(*M):
            continue
        lp, sp_ = lead(*P)
        lq, sq = lead(*Q)
        lm, sm = lead(*M)
        assert sp.expand(lm - lp * lq) == 0, (P, Q, M)
        for L, s in ((lp, sp_), (lq, sq), (lm, sm)):
            assert all(H[k - 1] not in L.free_symbols for k in range(s, 60)), "L contains its top or a larger generator"
        ok += 1
    print(f"PASS (1,2): L(P o Q) = L(P) L(Q) exactly on {ok} ordered pairs from {len(pool)} zero-free "
          f"profiles (1-3 rows, rows <= 4); every L free of its top and larger generators")

    fired = 0
    for P, Q in itertools.product(pool[3:12], repeat=2):
        M = merge(P, Q)
        if not valid(*M):
            continue
        lp, _ = lead(*P, shift=1)
        lq, _ = lead(*Q, shift=1)
        lm, _ = lead(*M, shift=1)
        if sp.expand(lm - lp * lq) != 0:
            fired += 1
    assert fired > 0, "CONTROL DID NOT FIRE: the wrong-index comparison also agrees"
    print(f"PASS (3, control fires): at index span-1 the product rule fails on {fired} pairs")

    bad = total = 0
    nz = [p for n in (2, 3) for p in profiles(n, 4) if not zero_free(*p)][:30]
    for P, Q in itertools.product(nz, repeat=2):
        M = merge(P, Q)
        if not valid(*M):
            continue
        lp, _ = lead(*P)
        lq, _ = lead(*Q)
        lm, _ = lead(*M)
        total += 1
        bad += sp.expand(lm - lp * lq) != 0
    print(f"REPORT (not asserted): on {total} pairs of NON-zero-free profiles the product rule fails on {bad}")
    print("ALL PASS")


if __name__ == "__main__":
    main()
