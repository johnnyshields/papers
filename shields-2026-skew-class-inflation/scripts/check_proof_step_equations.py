#!/usr/bin/env python3
r"""Displayed equations that are steps inside proofs, asserted on their own rather than through the
theorem they serve.  Targets: `eq:unit-homogenization`, `eq:unit-extremes` (`lem:seam-coefficients`),
`eq:overlap-cut-set`, `eq:initial-zero-interval`, `eq:period-gcd`, `eq:cut-period-comparison`
(`lem:overlap-power-rigidity`), `eq:orientation-multiset` (`thm:two-row-thin-class`).

  (1) Zero-gap extremes.  For every connected upper-Hessenberg profile in a box with s >= 1 zero gaps,
      the homogenization u^n s_D(h_1/u, h_2/u, ...) has u^0 coefficient the product of the cut components
      and u^s coefficient (-1)^s s_C for the total contraction C, computed from full Jacobi-Trudi
      determinants; cut components and C have no zero gap.
  (2) Overlapped powers.  For every positive composition rho of the box and every 0 < delta <
      min(x_1, x_k): the cut set of theta = rho^{(delta) m} is the union of j Q + C with C inside
      {delta+1..Q-1}; its cut indicator f is zero on [0, delta] and Q-periodic where both positions lie
      in [0, T].  For every divisor q of T with q <= T/2: gcd(Q, q) divides delta; Q + q <= T; and the
      only cut word t on residues 1..q-1 with f(x) = t_{x mod q} for q not dividing x is the zero word
      (so no factor beta with two parts exists).  The comparison graph r -- (r + Q mod q) on 1..q-1,
      deleting the pairs with r + Q = 0 mod q, has as components exactly the nonzero residue classes
      mod h = gcd(Q, q) and one component for the zero class.
  (3) Orientations.  For a < b and every block order and orientation vector of l <= 5 blocks of sizes
      from a composition of M <= 7, the multiset of rows of the zero-seam contraction equals
      {a, b} u {a+b}^(M-1) exactly when all orientations agree.
"""
from itertools import combinations, product
from math import gcd

from check_ref1_class_inflation_exact import schur, valid, compositions


def hessenberg(p):
    rows, gaps = p
    return all(rows[i] > gaps[i - 1] + gaps[i] for i in range(1, len(rows) - 1))


def hom(poly, n):
    """Coefficients of u^e: monomials with n - e positive factors."""
    out = {}
    for m, c in poly.items():
        out.setdefault(n - len(m), {})[m] = c
    return out


def zero_seams(p):
    rows, gaps = p
    segs, cur_r, cur_g = [], [rows[0]], []
    for i, g in enumerate(gaps):
        if g == 0:
            segs.append((tuple(cur_r), tuple(cur_g)))
            cur_r, cur_g = [rows[i + 1]], []
        else:
            cur_r.append(rows[i + 1])
            cur_g.append(g)
    segs.append((tuple(cur_r), tuple(cur_g)))
    return segs


def contract_zero(p):
    rows, gaps = p
    out_r, out_g = [rows[0]], []
    for i, g in enumerate(gaps):
        if g == 0:
            out_r[-1] += rows[i + 1]
        else:
            out_g.append(g)
            out_r.append(rows[i + 1])
    return tuple(out_r), tuple(out_g)


def pmul(f, g):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            m = tuple(sorted(m1 + m2))
            out[m] = out.get(m, 0) + c1 * c2
    return {m: c for m, c in out.items() if c}


def check_zero_gap_extremes():
    cnt = 0
    for n in range(2, 6):
        for rows in product(range(1, 6), repeat=n):
            for gaps in product(*[range(min(rows[i], rows[i + 1])) for i in range(n - 1)]):
                p = (rows, gaps)
                s = sum(1 for g in gaps if g == 0)
                if s == 0 or not hessenberg(p):
                    continue
                hs = hom(schur(p), n)
                comps = zero_seams(p)
                prod = {(): 1}
                for cp in comps:
                    assert valid(cp) and hessenberg(cp) and all(g > 0 for g in cp[1]), (p, cp)
                    prod = pmul(prod, schur(cp))
                assert hs.get(0, {}) == prod, ("u^0", p)
                C = contract_zero(p)
                assert valid(C) and hessenberg(C) and all(g > 0 for g in C[1]), (p, C)
                want = {m: (-1) ** s * c for m, c in schur(C).items()}
                assert hs.get(s, {}) == want, ("u^s", p)
                cnt += 1
    assert cnt > 200
    return cnt


def theta_of(rho, delta, m):
    x1, xk = rho[0], rho[-1]
    mid = rho[1:-1]
    return (x1,) + mid + ((x1 + xk - delta,) + mid) * (m - 1) + (xk,)


def cutset(comp):
    s, out = 0, set()
    for x in comp[:-1]:
        s += x
        out.add(s)
    return out


def check_overlap_steps():
    cnt = ncheck = 0
    for k in range(2, 5):
        for rho in product(range(1, 7), repeat=k):
            W = sum(rho)
            for delta in range(1, min(rho[0], rho[-1])):
                Q = W - delta
                C = cutset(rho)
                assert C <= set(range(delta + 1, Q)), (rho, delta)           # eq:overlap-cut-set
                for m in range(2, 5):
                    th = theta_of(rho, delta, m)
                    T = sum(th)
                    assert T == m * Q + delta
                    assert cutset(th) == {j * Q + c for j in range(m) for c in C}
                    f = {x: int(x in cutset(th)) for x in range(T + 1)}
                    assert all(f[x] == 0 for x in range(delta + 1))          # eq:initial-zero-interval
                    for x in range(1, T - Q):
                        if x + Q < T:
                            assert f[x] == f[x + Q], (rho, delta, m, x)      # Q-periodicity inside (0,T)
                    for q in range(2, T // 2 + 1):
                        if T % q:
                            continue
                        h = gcd(Q, q)
                        assert delta % h == 0, (rho, delta, m, q)            # eq:period-gcd, h | delta
                        assert Q + q <= T
                        # cut words t on residues 1..q-1 consistent with f
                        forced = {}
                        ok = True
                        for x in range(1, T):
                            if x % q:
                                r = x % q
                                if forced.setdefault(r, f[x]) != f[x]:
                                    ok = False
                        if ok:
                            assert all(v == 0 for v in forced.values()), ("a nonzero cut word is consistent", rho, delta, m, q)
                        else:
                            ncheck += 1
                        # eq:cut-period-comparison graph
                        parent = {r: r for r in range(1, q)}
                        def find(a):
                            while parent[a] != a:
                                parent[a] = parent[parent[a]]
                                a = parent[a]
                            return a
                        for r in range(1, q):
                            if (r + Q) % q:
                                parent[find(r)] = find((r + Q) % q)
                        comps = {}
                        for r in range(1, q):
                            comps.setdefault(find(r), set()).add(r)
                        classes = {}
                        for r in range(1, q):
                            classes.setdefault(r % h, set()).add(r)
                        assert sorted(map(sorted, comps.values())) == sorted(map(sorted, classes.values())), \
                            ("components are the residue classes mod h", Q, q, h)
                        cnt += 1
    assert cnt > 100
    return cnt, ncheck


def check_orientations():
    cnt = 0
    for a in range(1, 5):
        for b in range(a + 1, 7):
            for M in range(1, 8):
                for alpha in compositions(M):
                    ell = len(alpha)
                    if ell > 5:
                        continue
                    for order in set(__import__("itertools").permutations(alpha)):
                        want = sorted([a, b] + [a + b] * (M - 1))
                        good = set()
                        for eps in product((0, 1), repeat=ell):       # 0: (a..b), 1: reversed
                            rows = []
                            for m, e in zip(order, eps):
                                blk = [a] + [a + b] * (m - 1) + [b]
                                rows.append(blk[::-1] if e else blk)
                            merged = list(rows[0])
                            for blk in rows[1:]:
                                merged[-1] += blk[0]
                                merged.extend(blk[1:])
                            if sorted(merged) == want:
                                good.add(eps)
                        assert good == ({(0,) * ell, (1,) * ell}), (a, b, order, good)
                        cnt += 1
    return cnt


def main():
    n1 = check_zero_gap_extremes()
    print("eq:unit-homogenization / eq:unit-extremes: %d zero-gap Hessenberg profiles, both extremes against full determinants" % n1)
    n2, n2b = check_overlap_steps()
    print("eq:overlap-cut-set, eq:initial-zero-interval, eq:period-gcd, eq:cut-period-comparison: %d (rho, delta, m, q) cases (%d with an inconsistent residue class)" % (n2, n2b))
    n3 = check_orientations()
    print("eq:orientation-multiset: %d (a, b, block order) cases; only the two uniform orientations keep the multiset" % n3)
    print("ALL PASS")


if __name__ == "__main__":
    main()
