r"""Paper section `sec:balance` (Low-order balance and support separation).

Targets: `eq:uv`, `eq:three-difference`, `lem:low-order`, `eq:FE`,
`lem:small-core`, `lem:deletion`, `lem:color`, `thm:support`,
`rem:positive-equilibrium`, `prop:normalization` (`eq:gcd-normalization`,
`eq:w`, `eq:basic-periods`, `eq:mask`, `eq:mask-odd`).

The first block works with the actual cut indicators of compositions and the
ordinary inventories they define.  The matrix lemmas are checked exhaustively on
all skew-ternary matrices of at most five vertices (the paper's statements are
for every size; larger sizes are sampled and labeled as sampled).  `thm:support`
is swept over every pair of nonzero odd ternary functions with disjoint support
satisfying the balance equation on `Z/n` for every `n` up to a stated bound, which
also shows the hypothesis is non-vacuous.  `prop:normalization` is read off every
unequal, unreversed pair of compositions with equal three-block data.
"""
import itertools
import random
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd

from _ribbon_common import compositions, cuts, inv_upto, indicator, reverse, inventory_key, K_labeled


# ----------------------------------------------------------------- helpers
def tau_of(b, n):
    return [b[x % n] + b[(-x) % n] for x in range(n)]


def uv_of(b, c, n):
    u = [b[x] - c[(-x) % n] for x in range(n)]
    v = [b[x] - c[x] for x in range(n)]
    return u, v


def fe_holds(u, v, n):
    for x in range(n):
        for y in range(n):
            lhs = u[x] * v[y] + v[x] * u[y]
            s = (x + y) % n
            rhs = u[s] * (v[x] + v[y]) + v[s] * (u[x] + u[y])
            if lhs != rhs:
                return False
    return True


def subgroup_gen(n, support):
    g = n
    for x in support:
        g = gcd(g, x)
    return g          # the subgroup generated is gZ/nZ; proper iff g > 1


# ------------------------------------------------- eq:uv .. lem:low-order
def check_triangle_and_low_order():
    # eq:three-difference's ingredient: K_b(a,b',c') = 1/2 sum_{i<j} (tau_i tau_j - x_i x_j)
    cnt_tri = 0
    for n in range(3, 11):
        for a in compositions(n):
            b = indicator(a)
            tau = tau_of(b, n)
            xx = [b[t % n] - b[(-t) % n] for t in range(n)]
            S = cuts(a)
            for p in range(1, n - 1):
                for q in range(1, n - p):
                    r = n - p - q
                    lab = (p, q, r)
                    val = sum(tau[lab[i]] * tau[lab[j]] - xx[lab[i]] * xx[lab[j]]
                              for i in range(3) for j in range(i + 1, 3))
                    assert val % 2 == 0 and val // 2 == K_labeled(S, lab), (a, lab)
                    cnt_tri += 1
    print(f"PASS  triangle expansion of K_b on three labels: {cnt_tri} (cut set, triple) cases, "
          f"weight 3..10")

    pairs_total = pairs_equal2 = pairs_equal3 = 0
    for n in range(3, 13):
        comps = list(compositions(n))
        data = {}
        for a in comps:
            b = indicator(a)
            data[a] = (b, inv_upto(a, 2), inv_upto(a, 3))
        # group by two-block data: lem:low-order's first assertion says the ordinary
        # discrepancy through three blocks being zero forces this
        by2 = defaultdict(list)
        for a in comps:
            by2[tuple(sorted(data[a][1].items()))].append(a)
        for A, B in itertools.combinations(comps, 2):
            if n > 10 and tuple(sorted(data[A][1].items())) != tuple(sorted(data[B][1].items())):
                continue
            (b, i2b, i3b), (c, i2c, i3c) = data[A], data[B]
            diff3 = {lam: i3b.get(lam, 0) - i3c.get(lam, 0) for lam in set(i3b) | set(i3c)}
            diff3 = {k: v for k, v in diff3.items() if v}
            small = any(abs(v) in (1, 2) for v in diff3.values())
            pairs_total += 1
            if n <= 10 or True:
                # the proof's claim: any nonzero difference through three blocks has magnitude
                # one or two, so "no small discrepancy" is "no discrepancy"
                if diff3:
                    assert small, (A, B, diff3)
            eq2 = (i2b == i2c)
            if not diff3:
                pairs_equal3 += 1
                assert eq2, (A, B)                                      # two-block data agree
                u, v = uv_of(b, c, n)
                assert all(u[x] * v[x] == 0 for x in range(n)), (A, B)  # disjoint supports
                assert all(abs(u[x]) <= 1 and abs(v[x]) <= 1 for x in range(n))
                assert all(u[x] == -u[(-x) % n] and v[x] == -v[(-x) % n] for x in range(n))  # odd
                tau_b, tau_c = tau_of(b, n), tau_of(c, n)
                assert tau_b == tau_c, (A, B)                           # eq:uv
                assert fe_holds(u, v, n), (A, B)                        # eq:FE
            if eq2:
                pairs_equal2 += 1
                u, v = uv_of(b, c, n)
                # converse: after two-block equality, equality through three blocks <=> FE
                assert (not diff3) == fe_holds(u, v, n), (A, B)
                # eq:three-difference on every positive triple
                if n <= 9:
                    Sb, Sc = cuts(A), cuts(B)
                    for p in range(1, n - 1):
                        for q in range(1, n - p):
                            lab = (p, q, n - p - q)
                            dK = K_labeled(Sb, lab) - K_labeled(Sc, lab)
                            rhs = -sum(u[lab[i]] * v[lab[j]] + v[lab[i]] * u[lab[j]]
                                       for i in range(3) for j in range(i + 1, 3))
                            assert dK == rhs, (A, B, lab)
                            assert abs(dK) <= 2
    print(f"PASS  eq:uv, eq:three-difference, lem:low-order, eq:FE over {pairs_total} pairs of "
          f"compositions (weight 3..12; all pairs up to 10, two-block-equal pairs at 11, 12): "
          f"{pairs_equal2} two-block-equal pairs, {pairs_equal3} equal through three blocks")


# -------------------------------------------------------- matrix lemmas
def all_skew_ternary(k):
    idx = [(i, j) for i in range(k) for j in range(i + 1, k)]
    for vals in itertools.product((-1, 0, 1), repeat=len(idx)):
        A = [[0] * k for _ in range(k)]
        for (i, j), v in zip(idx, vals):
            A[i][j], A[j][i] = v, -v
        yield A


def has_constant_cut(A, verts):
    verts = list(verts)
    m = len(verts)
    if m < 2:
        return False
    first = verts[0]
    rest = verts[1:]
    for mask in range(0, 1 << len(rest)):
        P = [first] + [rest[i] for i in range(len(rest)) if mask >> i & 1]
        Q = [rest[i] for i in range(len(rest)) if not mask >> i & 1]
        if not Q:
            continue
        vals = {A[p][q] for p in P for q in Q}
        if len(vals) == 1:
            return True
    return False


def inseparable(A, verts):
    return len(verts) >= 2 and not has_constant_cut(A, verts)


def is_clan(A, C, k):
    for z in range(k):
        if z in C:
            continue
        if len({A[z][c] for c in C}) > 1:
            return False
    return True


def contract(A, k, C, rep):
    keep = [v for v in range(k) if v not in C or v == rep]
    return [[A[i][j] for j in keep] for i in keep], len(keep)


def check_small_core_and_deletion():
    ins = {3: 0, 4: 0, 5: 0}
    for k in (3, 4, 5):
        for A in all_skew_ternary(k):
            verts = range(k)
            if not inseparable(A, verts):
                continue
            ins[k] += 1
            # lem:small-core
            if k > 4:
                ok = False
                for sub in list(itertools.combinations(verts, 3)) + list(itertools.combinations(verts, 4)):
                    if inseparable(A, sub):
                        ok = True
                        break
                assert ok, A
            # lem:deletion, second assertion (k >= 5)
            if k >= 5:
                assert any(inseparable(A, [v for v in verts if v != z]) for z in verts), A
    # two-vertex matrices are separable
    assert all(not inseparable(A, range(2)) for A in all_skew_ternary(2))
    # lem:deletion, first assertion: contraction of a proper nonempty clan, k <= 5
    nclan = 0
    for k in (3, 4, 5):
        for A in all_skew_ternary(k):
            for size in range(2, k):
                for C in itertools.combinations(range(k), size):
                    if not is_clan(A, set(C), k):
                        continue
                    B, kb = contract(A, k, set(C), C[0])
                    assert inseparable(A, range(k)) == inseparable(B, range(kb)), (A, C)
                    nclan += 1
    # sampled six- and seven-vertex confirmation
    rng = random.Random(20261026)
    sampled = 0
    for k in (6, 7):
        for _ in range(4000):
            A = [[0] * k for _ in range(k)]
            for i in range(k):
                for j in range(i + 1, k):
                    v = rng.choice((-1, 0, 1))
                    A[i][j], A[j][i] = v, -v
            if not inseparable(A, range(k)):
                continue
            sampled += 1
            assert any(inseparable(A, [v for v in range(k) if v != z]) for z in range(k))
            assert any(inseparable(A, s) for r in (3, 4) for s in itertools.combinations(range(k), r))
    print(f"PASS  lem:small-core and lem:deletion: exhaustive over all skew-ternary matrices on "
          f"<= 5 vertices ({ins} inseparable at sizes 3/4/5; {nclan} clan contractions); "
          f"{sampled} sampled inseparable matrices on 6 and 7 vertices")


def pair_solutions(k):
    """All (U, V): disjoint-support skew-ternary matrices on k vertices satisfying
    eq:matrix-triangle on every triple, by backtracking over the entries."""
    pairs = [(i, j) for j in range(k) for i in range(j)]   # fill column by column
    state = {}
    states = [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]
    out = []

    def val(i, j):
        if i < j:
            return state[(i, j)]
        u, v = state[(j, i)]
        return (-u, -v)

    def triple_ok(i, j, kk):
        tot = 0
        for (a, b, c) in ((i, j, kk), (j, kk, i), (kk, i, j)):
            u1, v1 = val(a, b)
            u2, v2 = val(b, c)
            tot += u1 * v2 + v1 * u2
        return tot == 0

    def rec(t):
        if t == len(pairs):
            out.append(dict(state))
            return
        i, j = pairs[t]
        for s in states:
            state[(i, j)] = s
            ok = True
            if j >= 2:
                for a in range(j):
                    if a < i and (a, i) in state and (a, j) in state and (i, j) in state:
                        if not triple_ok(a, i, j):
                            ok = False
                            break
                    if a > i and a < j and (i, a) in state and (a, j) in state:
                        if not triple_ok(i, a, j):
                            ok = False
                            break
            if ok:
                rec(t + 1)
            del state[(i, j)]

    rec(0)
    return out


def components(k, edges):
    par = list(range(k))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for a, b in edges:
        par[f(a)] = f(b)
    return len({f(x) for x in range(k)})


def check_color_lemma():
    totals = {}
    for k in (3, 4, 5):
        sols = pair_solutions(k)
        n_ins = 0
        for st in sols:
            A = [[0] * k for _ in range(k)]
            red, blue = [], []
            for (i, j), (u, v) in st.items():
                A[i][j], A[j][i] = u + v, -(u + v)
                if u:
                    blue.append((i, j))
                if v:
                    red.append((i, j))
            if inseparable(A, range(k)):
                n_ins += 1
                assert components(k, blue) > 1 or components(k, red) > 1, st      # lem:color
        totals[k] = (len(sols), n_ins)
        # the scan really visited the triangle-satisfying pairs: a direct recount at k = 3
        if k == 3:
            direct = 0
            for combo in itertools.product([(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)], repeat=3):
                s = dict(zip([(0, 1), (0, 2), (1, 2)], combo))
                U = {k_: v[0] for k_, v in s.items()}
                V = {k_: v[1] for k_, v in s.items()}
                # eq:matrix-triangle on the single triple (0,1,2)
                tot = (U[(0, 1)] * V[(1, 2)] + V[(0, 1)] * U[(1, 2)]
                       + U[(1, 2)] * (-V[(0, 2)]) + V[(1, 2)] * (-U[(0, 2)])
                       + (-U[(0, 2)]) * V[(0, 1)] + (-V[(0, 2)]) * U[(0, 1)])
                direct += tot == 0
            assert direct == len(sols), (direct, len(sols))
    print("PASS  lem:color: exhaustive over every (U, V) with disjoint supports satisfying "
          "eq:matrix-triangle on <= 5 vertices; (solutions, with A inseparable) by size: "
          + ", ".join(f"{k}: {totals[k]}" for k in totals))


def positive_vector_exists(rows):
    """Exact test: is there d in Q^m with (row . d) > 0 for every row?  Rows are integer
    vectors of length m = 1 or 2 (the null-space basis coordinates of each vertex)."""
    m = len(rows[0])
    if any(all(x == 0 for x in r) for r in rows):
        return False
    if m == 1:
        return all(r[0] > 0 for r in rows) or all(r[0] < 0 for r in rows)
    cands = []
    rays = []
    for r in rows:
        rays += [(-r[1], r[0]), (r[1], -r[0])]
        cands.append(tuple(r))
    for a, b in itertools.combinations(rays, 2):
        cands.append((a[0] + b[0], a[1] + b[1]))
    return any(any(c) and all(r[0] * c[0] + r[1] * c[1] > 0 for r in rows) for c in cands)


def nullspace_integer_rows(A, k):
    import sympy as sp
    M = sp.Matrix(A)
    ns = M.nullspace()
    if not ns:
        return None, 0
    cols = []
    for v in ns:
        den = sp.ilcm(*[sp.fraction(x)[1] for x in v])
        cols.append([int(x * den) for x in v])
    return [[cols[j][i] for j in range(len(cols))] for i in range(k)], len(cols)


def check_positive_equilibrium():
    tested = 0
    for k in (2, 3, 4):
        for st in pair_solutions(k):
            A = [[0] * k for _ in range(k)]
            red, blue = [], []
            for (i, j), (u, v) in st.items():
                A[i][j], A[j][i] = u + v, -(u + v)
                if u:
                    blue.append((i, j))
                if v:
                    red.append((i, j))
            rows, dim = nullspace_integer_rows(A, k)
            if rows is None:
                continue
            if dim > 2:
                continue
            if positive_vector_exists(rows):
                tested += 1
                both = components(k, blue) == 1 and components(k, red) == 1
                assert not both, st            # rem:positive-equilibrium
    assert tested > 0
    print(f"PASS  rem:positive-equilibrium: on <= 4 vertices, {tested} disjoint-support triangle "
          f"pairs with a strictly positive null vector all have a disconnected support graph")


# ------------------------------------------------------------ thm:support
def check_support_theorem():
    results = {}
    for n in range(3, 19):
        m = (n - 1) // 2
        states = [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]
        sols = proper = 0
        for combo in itertools.product(states, repeat=m):
            if all(s == (0, 0) for s in combo):
                continue
            u = [0] * n
            v = [0] * n
            for x, (a, bb) in enumerate(combo, start=1):
                u[x], u[n - x] = a, -a
                v[x], v[n - x] = bb, -bb
            if not any(u) or not any(v):
                continue
            if not fe_holds(u, v, n):
                continue
            sols += 1
            gu = subgroup_gen(n, [x for x in range(1, n) if u[x]])
            gv = subgroup_gen(n, [x for x in range(1, n) if v[x]])
            assert gu > 1 or gv > 1, (n, u, v)         # at least one support is in a proper subgroup
            proper += 1
        results[n] = sols
    nonempty = sum(1 for s in results.values() if s)
    assert nonempty >= 3, results
    print(f"PASS  thm:support: every nonzero odd ternary disjoint pair solving eq:FE on Z/n has "
          f"a support generating a proper subgroup, n = 3..18; non-vacuous: solution counts "
          + ", ".join(f"n={n}:{s}" for n, s in results.items() if s))
    # the cyclic matrices realize eq:matrix-triangle exactly as eq:FE (the proof's first line)
    n = 12
    rng = random.Random(7)
    for _ in range(300):
        u = [0] * n
        v = [0] * n
        for x in range(1, n // 2):
            a, bb = rng.choice([(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)])
            u[x], u[n - x] = a, -a
            v[x], v[n - x] = bb, -bb
        U = lambda i, j: u[(j - i) % n]
        V = lambda i, j: v[(j - i) % n]
        mt = all(U(i, j) * V(j, k) + V(i, j) * U(j, k) + U(j, k) * V(k, i) + V(j, k) * U(k, i)
                 + U(k, i) * V(i, j) + V(k, i) * U(i, j) == 0
                 for i in range(n) for j in range(n) for k in range(n))
        assert mt == fe_holds(u, v, n)
    print("PASS  thm:support (proof): cyclic matrices satisfy eq:matrix-triangle exactly when "
          "eq:FE holds (300 random pairs on Z/12)")


# ---------------------------------------------------- prop:normalization
def periods_of(f, n):
    return [p for p in range(1, n + 1) if n % p == 0 and all(f[(x + p) % n] == f[x] for x in range(n))]


def check_normalization():
    npairs = 0
    shapes = Counter()
    for n in range(4, 15):
        comps = list(compositions(n))
        groups = defaultdict(list)
        for a in comps:
            groups[tuple(sorted(inv_upto(a, 3).items()))].append(a)
        for g in groups.values():
            for A, B in itertools.combinations(g, 2):
                if A == B or A == reverse(B):
                    continue
                b, c = indicator(A), indicator(B)
                found = None
                for gamma_c in (c, indicator(reverse(B))):
                    u, v = uv_of(b, gamma_c, n)
                    if not any(u) or not any(v):
                        continue
                    gu = subgroup_gen(n, [x for x in range(1, n) if u[x]])
                    d = subgroup_gen(n, [x for x in range(1, n) if v[x]])
                    Hu = {x for x in range(n) if x % gu == 0}
                    Hv = {x for x in range(n) if x % d == 0}
                    if gu != d and d % gu == 0 and gu < d:
                        found = (u, v, gu, d, Hu, Hv, gamma_c)
                        break
                assert found is not None, (A, B)
                u, v, gu, d, Hu, Hv, gc = found
                # both orientations exist as unions: the two subgroups are strictly nested
                assert Hv < Hu                                          # <supp v> = dZ  inside <supp u> = g_u Z
                assert (n % d == 0) and d < n
                w = [u[x] if x % d else 0 for x in range(n)]            # eq:w
                assert any(w) and all(w[x] == -w[(-x) % n] for x in range(n))
                assert all(w[(x + d) % n] == w[x] for x in range(n))
                pw = periods_of(w, n)
                e = min(pw)
                assert 3 <= e and d % e == 0 and e < n and n // d >= 3, (A, B, e, d, n)   # eq:basic-periods
                for p in range(e, d + 1):
                    if d % p or p % e:
                        continue
                    mask = [0 if x % p == 0 else b[x] for x in range(n)]  # eq:mask
                    assert all(mask[x] - mask[(-x) % n] == w[x] for x in range(n)), (A, B, p)  # eq:mask-odd
                npairs += 1
                shapes[(n, d // e)] += 1
    assert npairs > 0
    print(f"PASS  prop:normalization: for all {npairs} unequal, unreversed pairs equal through three "
          f"blocks (weight 4..14): nested subgroups, g_u | d properly after orientation, w nonzero "
          f"odd d-periodic, 3 <= e | d < n, n/d >= 3, and the masks have odd part w")


def main():
    check_triangle_and_low_order()
    check_small_core_and_deletion()
    check_color_lemma()
    check_positive_equilibrium()
    check_support_theorem()
    check_normalization()
    print("ALL PASS: verify_balance")


if __name__ == "__main__":
    main()
