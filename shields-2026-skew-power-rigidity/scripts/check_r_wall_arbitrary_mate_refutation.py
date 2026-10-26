#!/usr/bin/env python3
"""Check the four-row obstruction to unrestricted arbitrary-mate wall bounds.

For every integer b >= 5 put

    E_b = (2, b, b,   b+1;  1, 1, 2)      (rows; gaps)
    H_b = (2, b, b+1, b;    1, 2, 1)

instances of the four-row exceptional family at (c,w,B) = (1,2,b).  Then

    X(E_b) = (3b-1, 3b-2, 2b-1, b+1)
    X(H_b) = (3b-1, 3b-2, 2b,   b)
    Y(E_b) = Y(H_b) = (3b-3, 2b-2, b-1, 0)

with S = 3b-1, u = S - x_2 = 1, v = y_3 = b-1, so p = min(u,v) = 1, and

    s_{I_t E_b} = s_{I_t H_b}   <=>   0 <= t < b-3,      tau(E_b,H_b) = b-3.

If that holds, the separation time is UNBOUNDED while p stays 1, so no bound on
arbitrary-mate separation time can be read off p.  The
pair is row-primitive (gcd of successive beta gaps is 1), so the unbounded
separation is not an artifact of a strippable affine row layer.

Checked here independently from the profiles.
"""
from collections import Counter
from itertools import permutations
from math import gcd


def betas(profile):
    rows, gaps = profile
    n = len(rows)
    assert len(gaps) == n - 1
    x, y = [0] * n, [0] * n
    x[-1] = rows[-1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)


def det_shift(X, Y, t):
    out = Counter()
    n = len(X)
    for p in permutations(range(n)):
        idx = []
        ok = True
        for i in range(n):
            d = X[i] + t - Y[p[i]]
            if d < 0:
                ok = False
                break
            if d > 0:
                idx.append(d)
        if not ok:
            continue
        inv = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        out[tuple(sorted(idx))] += (-1) ** inv
    return {m: c for m, c in out.items() if c}


def rotation(X, Y):
    span = X[0] + Y[-1]
    return (tuple(span - v for v in Y[::-1]), tuple(span - v for v in X[::-1]))


def main():
    print(f"{'b':>3} {'p':>3} {'tau':>5} {'b-3':>5}  betas match  distinct/nonrot  primitive")
    ok = True
    for b in range(5, 12):
        E = ((2, b, b, b + 1), (1, 1, 2))
        H = ((2, b, b + 1, b), (1, 2, 1))
        XE, YE = betas(E)
        XH, YH = betas(H)

        expE = (3 * b - 1, 3 * b - 2, 2 * b - 1, b + 1)
        expH = (3 * b - 1, 3 * b - 2, 2 * b, b)
        expY = (3 * b - 3, 2 * b - 2, b - 1, 0)
        bmatch = (XE == expE and XH == expH and YE == expY and YH == expY)

        S = XE[0]
        u = S - XE[1]
        v = YE[len(YE) - 2]
        p = min(u, v)

        distinct = (XE, YE) != (XH, YH)
        nonrot = rotation(XE, YE) != (XH, YH)

        gaps = []
        for L in (XE, YE):
            gaps += [L[i] - L[i + 1] for i in range(len(L) - 1)]
        prim = (gcd(*gaps) == 1) if len(gaps) > 1 else False

        # first separation time
        tau = None
        for t in range(0, 4 * b + 6):
            if det_shift(XE, YE, t) != det_shift(XH, YH, t):
                tau = t
                break

        row_ok = (bmatch and p == 1 and tau == b - 3 and distinct and nonrot and prim)
        assert row_ok, (b, bmatch, p, tau, distinct, nonrot, prim)
        assert sum(a < c for a in XE for c in YE) == 3
        assert sum(a < c for a in XH for c in YH) == 3
        assert set(XE).isdisjoint(YE) and set(XH).isdisjoint(YH)
        ok &= row_ok
        print(f"{b:>3} {p:>3} {str(tau):>5} {b-3:>5}  {str(bmatch):>11}  "
              f"{str(distinct and nonrot):>15}  {prim}"
              + ("" if row_ok else "   <-- MISMATCH"))

    print()
    if ok:
        print("ALL PASS")
        print("Tested separation times agree with tau = b-3 and p = 1.")
        print("The uniform unboundedness statement is proved in the paper.")
    else:
        print("FAIL -- the four-row identities do not reproduce as stated.")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
