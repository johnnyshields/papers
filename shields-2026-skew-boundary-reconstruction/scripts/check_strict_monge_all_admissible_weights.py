#!/usr/bin/env python3
"""`def:convex-weight`, `lem:strict-monge`, `lem:feasible-uncrossing`, `thm:monge-minor`: the
Strict-Monge statements for EVERY admissible convex weight at once, not at a list of sample weights.

An admissible weight is fixed by its increments D(k) = omega(k) - omega(k-1), with D(1) > 0 and
D(k) - D(k-1) > 0.  Put e_1 = D(1) and e_k = D(k) - D(k-1) (k >= 2); then the admissible weights
are exactly the points of the open orthant e_k > 0, and

    omega(m) = sum_{i=1}^{m} (m - i + 1) e_i

is a LINEAR form in e with nonnegative integer coefficients.  The omega-weight of an h-monomial is
therefore a vector of nonnegative integers (the coefficients of e_1, e_2, ...), and a difference of
two weights is a positive number for every e > 0 exactly when its coefficient vector is
componentwise >= 0 and not identically 0.  So "strictly smaller for every admissible weight" is a
finite integer statement, checked here without fixing any weight.

  (a) lem:strict-monge   : crossed minus aligned cost is >= 0 componentwise and nonzero, for every
                           (x, p, zeta) in a box (x = d - A', p = A' - A, zeta = d' - d).
  (b) lem:feasible-uncrossing : the premise-implies-conclusion on the same box.
  (c) thm:monge-minor    : for every selection of s rows A and s columns d (strictly increasing, s <= 5,
                           parameters below N): if the increasing matching is feasible then every
                           other surviving permutation has weight vector strictly above it at every
                           admissible weight (so the increasing term is the unique minimum, with
                           coefficient +1 and no cancellation possible); if it is infeasible no
                           permutation survives, so the minor vanishes.
  (d) control: with the strictness dropped (D(k) - D(k-1) = 0 allowed, i.e. a linear weight) the
      same comparison produces ties, so the strict increase of the increments is load-bearing.
"""

from itertools import combinations, permutations

N = 8                 # parameters 0..N-1
SMAX = 5              # minor size
EMAX = 30


def omega_vec(m):
    """Coefficient vector of omega(m) in e_1..e_EMAX."""
    v = [0] * EMAX
    for i in range(1, m + 1):
        v[i - 1] = m - i + 1
    return v


def vsub(u, v):
    return [a - b for a, b in zip(u, v)]


def positive(v):
    return all(c >= 0 for c in v) and any(c > 0 for c in v)


def total(vs):
    out = [0] * EMAX
    for v in vs:
        out = [a + b for a, b in zip(out, v)]
    return out


def main():
    # (a) Strict-Monge inequality
    na = 0
    for x in range(0, 9):
        for p in range(1, 9):
            for z in range(1, 9):
                crossed = total([omega_vec(x + p + z), omega_vec(x)])
                aligned = total([omega_vec(x + p), omega_vec(x + z)])
                assert positive(vsub(crossed, aligned)), ("strict Monge", x, p, z)
                na += 1
    # control: drop strictness (linear weight, all e_k = 0 for k >= 2) -> ties
    linear_ties = 0
    for x in range(0, 6):
        for p in range(1, 6):
            for z in range(1, 6):
                diff = vsub(total([omega_vec(x + p + z), omega_vec(x)]),
                            total([omega_vec(x + p), omega_vec(x + z)]))
                if diff[0] == 0:                 # e_1 coefficient: the only surviving term of a linear weight
                    linear_ties += 1
    assert linear_ties == 6 * 5 * 5, "a linear weight must tie on the whole box"

    # (b) feasible uncrossing
    nb = 0
    for A in range(0, N):
        for A2 in range(A + 1, N):
            for d in range(0, N):
                for d2 in range(d + 1, N + 1):
                    if d - A2 >= 0:
                        assert d - A >= 0 and d2 - A2 >= 0 and d2 - A >= 0
                        nb += 1

    # (c) the minor theorem, for every admissible weight
    nc_feas = nc_inf = nperm = 0
    for s in range(1, SMAX + 1):
        for rows in combinations(range(N), s):
            for cols in combinations(range(N), s):
                feasible_id = all(cols[i] >= rows[i] for i in range(s))
                surviving = []
                for sg in permutations(range(s)):
                    if all(cols[sg[i]] >= rows[i] for i in range(s)):
                        surviving.append(sg)
                if not feasible_id:
                    assert not surviving, ("infeasible increasing matching but a term survives", rows, cols)
                    nc_inf += 1
                    continue
                base = total([omega_vec(cols[i] - rows[i]) for i in range(s)])
                for sg in surviving:
                    if sg == tuple(range(s)):
                        continue
                    w = total([omega_vec(cols[sg[i]] - rows[i]) for i in range(s)])
                    assert positive(vsub(w, base)), ("not strictly above the increasing term", rows, cols, sg)
                    nperm += 1
                nc_feas += 1

    print("lem:strict-monge   : strict at every admissible weight on %d (x,p,zeta); linear weight ties on all 150 (control)" % na)
    print("lem:feasible-uncrossing premise -> conclusion on %d quadruples" % nb)
    print("thm:monge-minor    : %d feasible selections (every other surviving term strictly heavier at every"
          " admissible weight: %d comparisons), %d infeasible selections with no surviving term" % (nc_feas, nperm, nc_inf))
    print("ALL PASS")


if __name__ == "__main__":
    main()
