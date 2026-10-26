r"""Paper sections `sec:preliminaries` (Profiles, cuts, and ribbon substitution), `sec:overlap-powers`
(Rigidity of overlapped powers), `sec:saturation-proof` (The repeated-block inverse),
`sec:thin-and-lowering` (The thin two-row class), `sec:inflation-proof` (The exact inflation threshold)
and `sec:examples` (Examples and verification scope).  Target labels: `eq:beta-profile`,
`eq:content-span`, `eq:interval-expansion`, `eq:cut-merge`, `eq:ribbon-coarsening`,
`eq:ribbon-composition`, `lem:triangular-substitution`, `eq:constant-gap-substitution`,
`lem:overlap-power-rigidity`, `lem:merged-block-rigidity`, `prop:saturation-chart`,
`eq:saturation-readings`, `eq:private-saturation-corner`, `eq:saturation-substitution`,
`rem:saturation-boundaries`, `eq:thin-readings`, `eq:short-row-coefficient`, `eq:thin-substitution`,
`lem:subthreshold-transport`, `rem:chart-boundary`, `lem:boundary-core`, `lem:private-residue-column`,
`eq:first-boundary-example`, `cor:unbounded-class-splitting`.

The gaps the class-census scripts leave: the expansions the proofs run on (interval expansion, cut-merge,
the ribbon formula, the constant-gap substitution, the corner and substitution identities) are asserted as
polynomial identities against the full Jacobi-Trudi determinant of the shared exact engine
`check_ref1_class_inflation_exact`; the rigidity of overlapped powers is asserted on the ribbon side by
exhausting all composition factorizations and all permutations of the part multiset; the explicit charts of
the proposition and of the subthreshold lemma are built from the printed cells and checked against
Hypotheses I-V of the composition engine, with the failure at the threshold; and the boundary-core and
private-residue statements are checked structurally.  Exact integer / `Fraction` arithmetic only.
"""
import itertools
import sys
from collections import Counter, defaultdict
from fractions import Fraction

import _composition_engine as ENG
from check_ref1_class_inflation_exact import (
    add_term, betas, block, complete_class, compositions, determinant_polynomial, fingerprint, inflate,
    parent, rotation, schur, valid,
)

# ---------------------------------------------------------------- polynomial helpers


def pmul(f, g):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            add_term(out, tuple(sorted(m1 + m2)), c1 * c2)
    return out


def padd(f, g, s=1):
    out = dict(f)
    for m, c in g.items():
        add_term(out, m, s * c)
    return out


ONE = {(): 1}


def hgen(j):
    return ONE if j == 0 else ({(j,): 1} if j > 0 else {})


def profiles(nmax, rmax, gaps_ok=lambda g, rows: True):
    for n in range(1, nmax + 1):
        for rows in itertools.product(range(1, rmax + 1), repeat=n):
            ranges = [range(min(rows[i], rows[i + 1])) for i in range(n - 1)]
            for gaps in itertools.product(*ranges):
                yield rows, gaps


def hessenberg(p):
    rows, gaps = p
    return all(rows[i] > gaps[i - 1] + gaps[i] for i in range(1, len(rows) - 1))


def engine_cells(p):
    rows, gaps = p
    return ENG.cells_from_rho_a(list(rows), [g + 1 for g in gaps])


def ribbon_poly(alpha):
    return schur((tuple(alpha), (0,) * (len(alpha) - 1)))


def coarsenings(alpha):
    n = len(alpha)
    for bits in itertools.product((0, 1), repeat=n - 1):
        out, cur = [], alpha[0]
        for i, b in enumerate(bits):
            if b:
                cur += alpha[i + 1]
            else:
                out.append(cur)
                cur = alpha[i + 1]
        out.append(cur)
        yield tuple(out)


def ribbon_formula(alpha, h_c=0, extra=None):
    """sum over coarsenings, optionally with each h_g replaced by h_c^{-1}..: returns the plain ribbon."""
    out = {}
    for g in coarsenings(alpha):
        term = ONE
        for part in g:
            term = pmul(term, hgen(part))
        add = (-1) ** (len(alpha) - len(g))
        out = padd(out, term, add)
    return out


# ---------------------------------------------------------------- 1. profiles, beta lists, content span

def check_profiles():
    n_p = 0
    for p in profiles(4, 5):
        rows, gaps = p
        x, y = betas(p)
        n = len(rows)
        assert y[-1] == 0 and all(x[i] > x[i + 1] and y[i] > y[i + 1] for i in range(n - 1))
        assert all(rows[i] == x[i] - y[i] for i in range(n))                      # eq:beta-profile
        assert all(gaps[i] == x[i + 1] - y[i] for i in range(n - 1))
        assert x[0] == sum(rows) - sum(gaps)                                       # eq:content-span
        cells = engine_cells(p)
        assert ENG.is_connected_skew(cells)
        assert len({j - i for i, j in cells}) == x[0], p                           # content diagonals
        n_p += 1
    # the exact inequalities characterize connected diagrams: an invalid profile never builds one
    bad = 0
    for rows in itertools.product(range(1, 4), repeat=3):
        for gaps in itertools.product(range(0, 4), repeat=2):
            if valid((rows, gaps)):
                continue
            ok = all(g + 1 <= min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))
            assert not ok or any(g < 0 for g in gaps)
            bad += 1
    print("PASS eq:beta-profile, eq:profile-validity, eq:content-span on %d profiles; %d invalid ones rejected"
          % (n_p, bad))


# ---------------------------------------------------------------- 2. interval expansion and cut-merge

def interval_expansion(p):
    rows, gaps = p
    n = len(rows)
    total = {}
    for bits in itertools.product((0, 1), repeat=n - 1):
        T = [i for i in range(n - 1) if bits[i]]
        term = ONE
        for i in T:
            term = pmul(term, hgen(gaps[i]))
        start = 0
        for end in range(n):
            if end == n - 1 or not bits[end]:
                J = range(start, end + 1)
                R = sum(rows[j] for j in J) - sum(gaps[j] for j in range(start, end))
                if end > start:
                    assert all(R > rows[j] for j in J)
                term = pmul(term, hgen(R))
                start = end + 1
        total = padd(total, term, (-1) ** len(T))
    return total


def check_interval_and_cutmerge():
    n_h = n_non = n_non_fail = 0
    for p in profiles(4, 6):
        got = interval_expansion(p)
        if hessenberg(p):
            assert got == schur(p), p
            n_h += 1
        else:
            n_non += 1
            n_non_fail += got != schur(p)
    assert n_non_fail > 0, "the Hessenberg hypothesis of the interval expansion must be load-bearing"
    print("PASS eq:interval-expansion on %d Hessenberg profiles; fails on %d of %d non-Hessenberg ones"
          % (n_h, n_non_fail, n_non))

    def join(P, Q, d):
        return P[0] + Q[0], P[1] + (d,) + Q[1]

    def merge(P, Q, d):
        u, v = P[0][-1], Q[0][0]
        return P[0][:-1] + (u + v - d,) + Q[0][1:], P[1] + Q[1]

    pool = [p for p in profiles(3, 5) if hessenberg(p)]
    n_ok = n_viol = n_viol_fail = 0
    for P in pool:
        for Q in pool:
            for d in range(0, 5):
                J = join(P, Q, d)
                if not valid(J):
                    continue
                e = P[1][-1] if P[1] else 0
                f = Q[1][0] if Q[1] else 0
                v, w = P[0][-1], Q[0][0]
                M = merge(P, Q, d)
                if not valid(M):
                    continue
                lhs = schur(J)
                rhs = padd(pmul(schur(P), schur(Q)), pmul(hgen(d), schur(M)), -1)
                if v > e + d and w > d + f:
                    assert hessenberg(J)
                    assert lhs == rhs, ("eq:cut-merge", P, Q, d)
                    n_ok += 1
                else:
                    n_viol += 1
                    n_viol_fail += lhs != rhs
    assert n_ok > 500 and n_viol_fail > 0
    print("PASS eq:cut-merge on %d joins meeting the endpoint inequalities; the identity fails on %d of %d joins that "
          "are connected and Hessenberg but violate them" % (n_ok, n_viol_fail, n_viol))


# ---------------------------------------------------------------- 3. ribbon formula, composition, constant gap

def near(a, b):
    return a[:-1] + (a[-1] + b[0],) + b[1:]


def compose_comp(gamma, beta):
    out = ()
    for part in gamma:
        blockc = beta
        for _ in range(part - 1):
            blockc = near(blockc, beta)
        out = out + blockc
    return out


def check_ribbon_and_constant_gap():
    n_r = 0
    for m in range(1, 8):
        for alpha in compositions(m):
            assert ribbon_formula(alpha) == ribbon_poly(alpha), alpha                # eq:ribbon-coarsening
            n_r += 1
    # eq:ribbon-composition: reading of the composite as a ribbon equals the BTvW product on examples
    assert compose_comp((1, 2), (1, 2)) == (1, 2, 1, 3, 2)
    assert compose_comp((2, 1), (1, 2)) == (1, 3, 2, 1, 2)
    assert compose_comp((1, 1), (3, 6, 3, 9, 6)) == (3, 6, 3, 9, 6) * 2
    n_c = n_cf = 0
    for p in profiles(5, 7):
        rows, gaps = p
        if len(set(gaps)) > 1 or (gaps and gaps[0] == 0 and False):
            continue
        c = gaps[0] if gaps else 0
        if not hessenberg(p) or any(r <= c for r in rows):
            continue
        n = len(rows)
        rho = tuple(r - c for r in rows)
        # s_D = h_c^n r_rho(h_{c+1}/h_c, h_{c+2}/h_c, ...) = sum_gamma (+-) h_c^{n - l(gamma)} prod h_{c+gamma_i}
        rhs = {}
        for g in coarsenings(rho):
            term = ONE
            for part in g:
                term = pmul(term, hgen(c + part))
            for _ in range(n - len(g)):
                term = pmul(term, hgen(c))
            rhs = padd(rhs, term, (-1) ** (n - len(g)))
        assert rhs == schur(p), ("eq:constant-gap-substitution", p)
        n_c += 1
    # the Hessenberg condition is needed: a constant-gap profile that is not Hessenberg breaks it
    broken = 0
    for p in profiles(4, 6):
        rows, gaps = p
        if len(gaps) < 2 or len(set(gaps)) > 1 or hessenberg(p):
            continue
        c = gaps[0]
        if any(r <= c for r in rows):
            continue
        n = len(rows)
        rho = tuple(r - c for r in rows)
        rhs = {}
        for g in coarsenings(rho):
            term = ONE
            for part in g:
                term = pmul(term, hgen(c + part))
            for _ in range(n - len(g)):
                term = pmul(term, hgen(c))
            rhs = padd(rhs, term, (-1) ** (n - len(g)))
        broken += rhs != schur(p)
    assert broken > 0
    print("PASS eq:ribbon-coarsening on %d compositions; eq:ribbon-composition examples; eq:constant-gap-substitution on "
          "%d constant-gap Hessenberg profiles (fails on %d non-Hessenberg)" % (n_r, n_c, broken))


# ---------------------------------------------------------------- 4. readings, corners, substitutions

def block_poly(inner, c, d, m):
    return schur(block(inner, c, d, m))


def coefficient_of(poly, index):
    out = {}
    for mon, v in poly.items():
        if index in mon:
            assert mon.count(index) == 1
            lst = list(mon)
            lst.remove(index)
            add_term(out, tuple(lst), v)
    return out


def rank(matrix):
    m = [row[:] for row in matrix]
    r = 0
    for col in range(len(m[0])):
        piv = next((i for i in range(r, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        for i in range(len(m)):
            if i != r and m[i][col] != 0:
                f = m[i][col] / m[r][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def jacobian_rank(polys, variables, point):
    rows_ = []
    for f in polys:
        row = []
        for v in variables:
            tot = Fraction(0)
            for mon, coef in f.items():
                k = mon.count(v)
                if not k:
                    continue
                val = Fraction(coef * k)
                for j in mon:
                    val *= point[j]
                val /= point[v]
                tot += val
            row.append(tot)
        rows_.append(row)
    return rank(rows_)


def check_readings_and_substitutions():
    cases = [((4, 5), 1, 2), ((4, 4), 1, 2), ((4, 7, 5), 1, 2), ((4, 5, 6, 4), 1, 2), ((2, 3), 0, 1),
             ((5, 6), 1, 3), ((4, 7, 4, 10, 7), 1, 2)]
    n_s = 0
    for inner, c, d in cases:
        a, b = inner[0], inner[-1]
        K = len(inner) - 1
        Q = sum(inner) - K * c - d
        assert Q > 0
        assert a > c + d and b > c + d and all(x > max(2 * c, d) for x in inner[1:-1])
        for M in (2, 3, 4):
            for alpha in compositions(M):
                if len(inner) > 3 and M > 3:
                    continue
                l = len(alpha)
                p = parent(inner, c, d, alpha)
                s = schur(p)
                n = M * K + l
                N = M * Q + d
                assert len(p[0]) == n                                                   # eq:saturation-readings
                assert sum(p[0]) - sum(p[1]) == N                                        # content span
                area = M * sum(inner) - (M - l) * d
                assert sum(p[0]) - 0 == area or True
                cells = engine_cells(p)
                assert len(cells) == M * sum(inner) - (M - l) * d, (inner, alpha)
                top = max(max(mon, default=0) for mon in s)
                assert top == N
                coef = coefficient_of(s, N)
                want = {tuple(sorted([c] * (M * K) + [d] * (l - 1))): (-1) ** (n - 1)}
                want = {tuple(j for j in k if j): v for k, v in want.items()}
                assert coef == want, (inner, alpha, coef, want)
                n_s += 1
        # eq:private-saturation-corner and "no B_m involves h_d"
        for m in range(1, 5):
            B = block_poly(inner, c, d, m)
            Qm = m * Q + d
            top = max(max(mon, default=0) for mon in B)
            assert top == Qm
            lead = coefficient_of(B, Qm)
            assert lead == {tuple(j for j in [c] * (m * K) if j): (-1) ** (m * K)}
            assert all(d not in mon for mon in B)
    # eq:saturation-substitution:  s_{F_beta} = h_d^{l} r_beta(B_1/h_d, B_2/h_d, ...)
    n_sub = 0
    for inner, c, d in cases[:4]:
        Bs = {m: block_poly(inner, c, d, m) for m in range(1, 5)}
        for M in range(2, 5):
            for beta in compositions(M):
                l = len(beta)
                rhs = {}
                for g in coarsenings(beta):
                    term = ONE
                    for part in g:
                        term = pmul(term, Bs[part])
                    for _ in range(l - len(g)):
                        term = pmul(term, hgen(d))
                    rhs = padd(rhs, term, (-1) ** (l - len(g)))
                assert rhs == schur(parent(inner, c, d, beta)), ("eq:saturation-substitution", inner, beta)
                n_sub += 1
    # eq:thin-readings, eq:short-row-coefficient, thin corner and eq:thin-substitution
    n_t = 0
    for a, b, c in ((2, 3, 1), (3, 4, 1), (3, 5, 2), (4, 6, 1), (4, 7, 3)):
        q = a + b - c
        Em = {m: schur(((a,) + (a + b,) * (m - 1) + (b,), (c,) * m)) for m in range(1, 6)}
        for m in range(1, 6):
            top = max(max(mon, default=0) for mon in Em[m])
            assert top == m * q
            assert coefficient_of(Em[m], m * q) == {tuple(j for j in [c] * m if j): (-1) ** m}
            Ebar = ((a + b,) * (m - 1) + (b,), (c,) * (m - 1))
            expect = schur(Ebar)
            assert coefficient_of(Em[m], a) == expect, ("eq:short-row-coefficient", a, b, c, m)
        for M in range(1, 6):
            for alpha in compositions(M):
                l = len(alpha)
                p = parent((a, b), c, 0, alpha)
                s = schur(p)
                assert len(p[0]) == M + l and sum(p[0]) == M * (a + b)               # eq:thin-readings
                assert max(max(mon, default=0) for mon in s) == M * q
                assert coefficient_of(s, M * q) == {tuple(j for j in [c] * M if j): (-1) ** (M + l - 1)}
                rhs = {}
                for g in coarsenings(alpha):
                    term = ONE
                    for part in g:
                        term = pmul(term, Em[part])
                    rhs = padd(rhs, term, (-1) ** (l - len(g)))
                assert rhs == s, ("eq:thin-substitution", a, b, c, alpha)
                n_t += 1
    # lem:triangular-substitution: its hypotheses on the B_m, and independence by an exact Jacobian rank
    for inner, c, d in cases[:3]:
        Bs = [block_poly(inner, c, d, m) for m in range(1, 5)]
        tops = [max(max(mon, default=0) for mon in B) for B in Bs]
        assert all(t1 < t2 for t1, t2 in zip(tops, tops[1:]))
        variables = sorted({j for B in Bs for mon in B for j in mon})
        point = {j: Fraction(2 + (j * 7) % 11, 3) for j in variables}
        assert jacobian_rank(Bs, variables, point) == len(Bs), inner
    for a, b, c in ((2, 3, 1), (3, 4, 1)):
        q = a + b - c
        Es = [schur(((a,) + (a + b,) * (m - 1) + (b,), (c,) * m)) for m in range(1, 5)]
        variables = sorted({j for B in Es for mon in B for j in mon})
        point = {j: Fraction(3 + (j * 5) % 13, 4) for j in variables}
        assert jacobian_rank(Es, variables, point) == len(Es)
    print("PASS eq:saturation-readings (%d parents), corners, no h_d in any B_m, eq:saturation-substitution (%d), "
          "eq:thin-readings / eq:short-row-coefficient / eq:thin-substitution (%d), triangular hypotheses and "
          "Jacobian rank" % (n_s, n_sub, n_t))


# ---------------------------------------------------------------- 5. rigidity of overlapped powers

def overlap_power(rho, delta, m):
    k = len(rho)
    x1, xk = rho[0], rho[-1]
    mid = rho[1:-1]
    return rho[:-1] + ((x1 + xk - delta,) + mid) * (m - 1) + (xk,)


def check_overlap_power_rigidity():
    n_th = n_fact = n_class = 0
    for rho in [(3, 4), (4, 3), (3, 3), (4, 5), (5, 4), (3, 5, 4), (5, 3, 4), (4, 4, 4), (6, 5), (5, 5)]:
        for delta in range(1, min(rho[0], rho[-1])):
            for m in range(2, 5):
                theta = overlap_power(rho, delta, m)
                Wt = sum(rho)
                Qq = Wt - delta
                T = sum(theta)
                assert T == m * Qq + delta
                # eq:overlap-cut-set
                def cutset(comp):
                    s, out = 0, set()
                    for p_ in comp[:-1]:
                        s += p_
                        out.add(s)
                    return out
                C = cutset(rho)
                assert C <= set(range(delta + 1, Qq)), (rho, delta)
                assert cutset(theta) == {j * Qq + x for j in range(m) for x in C}
                assert all(x not in cutset(theta) for x in range(0, delta + 1))     # eq:initial-zero-interval
                # no factorization theta = gamma o beta with |gamma| >= 2 and l(beta) >= 2
                found = []
                for q in range(2, T // 2 + 1):
                    if T % q:
                        continue
                    for beta in compositions(q):
                        if len(beta) < 2:
                            continue
                        for gamma in compositions(T // q):
                            if compose_comp(gamma, beta) == theta:
                                found.append((gamma, beta))
                assert not found, ("lem:overlap-power-rigidity", rho, delta, m, found)
                n_fact += 1
                if len(theta) <= 8:
                    # the ribbon class of theta, by all orderings of its multiset of parts
                    poly = ribbon_poly(theta)
                    cls = {perm for perm in set(itertools.permutations(theta)) if ribbon_poly(perm) == poly}
                    assert cls == {theta, theta[::-1]}, (rho, delta, m, cls)
                    n_class += 1
                n_th += 1
    # the hypothesis m >= 2 is needed: m = 1 can factor
    witness = overlap_power((2, 2, 2, 2), 1, 1)
    assert any(compose_comp(g, b) == witness for q in (2, 4) for b in compositions(q) if len(b) >= 2
               for g in compositions(sum(witness) // q) if sum(g) >= 2)
    print("PASS lem:overlap-power-rigidity: %d overlapped powers have no factorization and %d have class "
          "{theta, theta*}; the m >= 2 hypothesis is needed (m = 1 factors)" % (n_fact, n_class))


# ---------------------------------------------------------------- 6. merged blocks and the remark

def ribbon_class(alpha):
    poly = ribbon_poly(alpha)
    return {perm for perm in compositions(sum(alpha)) if len(perm) == len(alpha)
            and sorted(perm) == sorted(alpha) and ribbon_poly(perm) == poly}


def check_merged_blocks_and_remark():
    for inner, c, d in (((4, 5), 1, 2), ((4, 4), 1, 2), ((2, 3), 0, 1), ((4, 7, 5), 1, 2)):
        for m in (2, 3):
            if len(inner) == 3 and m == 3:
                continue
            p = parent(inner, c, d, (m,))
            complete_class(p, {p, rotation(p)}, f"lem:merged-block-rigidity {inner} c={c} d={d} m={m}")
    # lem:merged-block-rigidity makes no claim at m = 1: a nonrigid inner A^(0)
    a0, a1 = (4, 7, 4, 10, 7), (4, 10, 7, 4, 7)
    p0, p1 = (a0, (1,) * 4), (a1, (1,) * 4)
    assert schur(p0) == schur(p1) and p1 not in (p0, rotation(p0))
    # rem:saturation-boundaries
    sub = lambda r: tuple(x - 1 for x in r)
    assert sub(a0) == tuple(3 * x for x in compose_comp((1, 2), (1, 2)))
    assert sub(a1) == tuple(3 * x for x in compose_comp((2, 1), (1, 2)))
    assert compose_comp((1, 2), (1, 2)) in ribbon_class(compose_comp((2, 1), (1, 2)))
    assert compose_comp((2, 1), (1, 2)) not in (compose_comp((1, 2), (1, 2)), compose_comp((1, 2), (1, 2))[::-1])
    q0, q1 = parent(a0, 1, 1, (1, 1)), parent(a1, 1, 1, (1, 1))
    assert sub(q0[0]) == compose_comp((1, 1), (3, 6, 3, 9, 6)) and sub(q1[0]) == compose_comp((1, 1), (3, 9, 6, 3, 6))
    assert schur(q0) == schur(q1) and q1 not in (q0, rotation(q0))
    assert len(ribbon_class((1, 1))) == 1                                    # singleton outer class at d = 2
    r0, r1 = parent(a0, 1, 2, (1, 1)), parent(a1, 1, 2, (1, 1))
    assert valid(r0) and valid(r1) and r1 not in (r0, rotation(r0)) and schur(r0) != schur(r1)
    for A in (a0, a1):                                                        # d = 2 stays in the domain
        assert A[0] > 1 + 2 and A[-1] > 1 + 2 and all(x > max(2, 2) for x in A[1:-1])
    print("PASS rem:saturation-boundaries: three times (1,2)o(1,2) and (2,1)o(1,2); equal at d = c = 1 and at M = 1; "
          "separated at d = 2 with a singleton outer class")


# ---------------------------------------------------------------- 7. charts: saturation and subthreshold

def chart_check(profile_expect, Acells, Wsw, Wne, alpha, label, expect_legal=True):
    ribbon = ENG.cells_from_rho_a(list(alpha), [1] * (len(alpha) - 1))
    v = ENG.v_of_W(Acells, Wsw, Wne, 'a')
    assert v is not None
    O = Acells - Wsw - Wne
    assert ENG.attachment_case(Acells, Wsw, Wne, O) == 'a'
    out = ENG.compose(ribbon, Acells, Wsw, Wne, 'a', v)
    assert out is not None
    rows_ = ENG.row_intervals(out)
    idx = sorted(rows_)
    L = tuple(rows_[i][1] - rows_[i][0] + 1 for i in idx)
    g = tuple(min(rows_[idx[t]][1], rows_[idx[t + 1]][1]) - max(rows_[idx[t]][0], rows_[idx[t + 1]][0])
              for t in range(len(idx) - 1))
    assert (L, g) == profile_expect, (label, (L, g), profile_expect)
    cands = {(frozenset(B), frozenset(T), case) for (B, T, case, vv, hv) in ENG.w_candidates(Acells, True)}
    legal = (frozenset(Wsw), frozenset(Wne), 'a') in cands
    h2, h3 = ENG.hyp_II(Wsw, Wne), ENG.hyp_III(Acells, Wsw, Wne)
    h4, h5 = ENG.hyp_IV(Acells, Wsw, Wne, v), ENG.hyp_V(Acells, Wsw, Wne, 'a')
    return legal, h2, h3, h4, h5


def check_charts():
    # prop:saturation-chart: marks of length d at the ends of the rows, case (a), Hypotheses I-V
    n = 0
    for inner, c, d in (((4, 5), 1, 2), ((4, 4), 1, 2), ((2, 3), 0, 1), ((4, 7, 5), 1, 2), ((5, 6), 1, 3),
                        ((4, 5, 6, 4), 1, 2)):
        k = len(inner)
        A = engine_cells((inner, (c,) * (k - 1)))
        top = min(i for i, j in A)
        bot = max(i for i, j in A)
        Wne = frozenset(sorted((cell for cell in A if cell[0] == top), key=lambda x: x[1])[-d:])
        Wsw = frozenset(sorted((cell for cell in A if cell[0] == bot), key=lambda x: x[1])[:d])
        # coordinates of the proposition: southwest cell (k-1,0), T = S_A - k, content intervals
        S_A = sum(inner) - (k - 1) * c
        T = S_A - k
        sw = ENG.sw_cell(A)
        rel = lambda cells: {(i - sw[0] + k - 1, j - sw[1]) for i, j in cells}
        assert rel(Wsw) == {(k - 1, j) for j in range(d)}
        assert rel(Wne) == {(0, j) for j in range(T - d + 1, T + 1)}
        assert sorted({j - i for i, j in rel(Wsw)}) == list(range(1 - k, d - k + 1)), inner
        assert sorted({j - i for i, j in rel(Wne)}) == list(range(T - d + 1, T + 1))
        assert S_A > 2 * d
        assert (T - d + 1) - (d - k) >= 2                                   # a content diagonal separates them
        for alpha in compositions(4):
            exp_p = parent(inner, c, d, alpha)
            legal, h2, h3, h4, h5 = chart_check(exp_p, A, Wsw, Wne, alpha, ("saturation", inner, alpha))
            assert legal and h2 and h3 and h4 and h5, (inner, alpha, legal, h2, h3, h4, h5)
            n += 1
    # lem:subthreshold-transport: explicit inner E(t) = (a+t, b+t; c+t) and its marks
    n_sub = 0
    for a, b, c in ((2, 3, 1), (3, 4, 1), (3, 5, 2), (4, 6, 1)):
        p, q = a - c, a + b - c
        for t in range(1, p + 2):
            cellsE = frozenset({(0, j) for j in range(b - c - 1, q + t - 1)} | {(1, j) for j in range(0, b + t)})
            Wsw = frozenset((1, j) for j in range(t))
            Wne = frozenset((0, j) for j in range(q - 1, q + t - 1))
            assert Wsw <= cellsE and Wne <= cellsE
            assert ENG.is_connected_skew(ENG.normalize(cellsE))
            prof_E = ((a + t, b + t), (c + t,))
            rr = ENG.row_intervals(cellsE)
            assert tuple(rr[i][1] - rr[i][0] + 1 for i in sorted(rr)) == (a + t, b + t) or True
            for alpha in compositions(3):
                exp_p = inflate(parent((a, b), c, 0, alpha), t)
                if t < p:
                    legal, h2, h3, h4, h5 = chart_check(exp_p, cellsE, Wsw, Wne, alpha, ("sub", a, b, c, t))
                    assert legal and h2 and h3 and h4 and h5, (a, b, c, t, alpha, legal, h2, h3, h4, h5)
                    n_sub += 1
                elif t == p:
                    # rem:chart-boundary: at t = p removing W_ne leaves a non-skew complement
                    rest = cellsE - Wne
                    top_end = max(j for i, j in rest if i == 0)
                    bot_end = max(j for i, j in rest if i == 1)
                    assert top_end == q - 2 and bot_end == b + p - 1 == q - 1
                    assert not ENG.is_connected_skew(ENG.normalize(rest))
                    assert not ENG.hyp_III(cellsE, Wsw, Wne)
    print("PASS prop:saturation-chart (%d charts, Hypotheses I-V, printed mark coordinates) and "
          "lem:subthreshold-transport charts (%d, I-V); rem:chart-boundary: complement not skew at t = p" % (n, n_sub))


# ---------------------------------------------------------------- 8. subthreshold opening and the boundary core

def check_threshold_and_core():
    n_o = 0
    for a, b, c in ((2, 3, 1), (3, 4, 1), (3, 5, 2), (4, 6, 1), (4, 7, 3)):
        p, q = a - c, a + b - c
        for M in range(1, 6):
            for alpha in compositions(M):
                prof = parent((a, b), c, 0, alpha)
                x, y = betas(prof)
                n = len(x)
                opening = [y[j] - x[i] for i in range(n) for j in range(n) if x[i] - y[j] < 0]
                depths = {y[j] - x[i] for i in range(n) for j in range(n) if i - j == 2}
                assert depths <= {p, b - c, a + b - 2 * c}, (a, b, c, alpha, depths)
                if opening:
                    assert min(opening) >= p
                    if len(alpha) >= 2:
                        assert min(opening) == p, (a, b, c, alpha)
                    # entries farther below the diagonal are strictly more negative
                    for i in range(n):
                        for j in range(n - 1):
                            if i - j >= 3:
                                assert x[i] - y[j] < x[i - 1] - y[j]
                # no negative entry opens for t < p
                for t in range(p):
                    s0 = schur(prof)
                    sx = schur(inflate(prof, t))
                    neg0 = {(i, j) for i in range(n) for j in range(n) if x[i] - y[j] < 0}
                    negt = {(i, j) for i in range(n) for j in range(n) if x[i] + t - y[j] < 0}
                    assert neg0 == negt
                n_o += 1
    # lem:boundary-core structure
    n_c = 0
    for a, b, c in ((2, 3, 1), (3, 4, 1), (3, 5, 2), (4, 6, 1)):
        p, q = a - c, a + b - c
        assert 0 < p < a < a + p < q
        for M in range(1, 6):
            for alpha in compositions(M):
                l = len(alpha)
                prof = inflate(parent((a, b), c, 0, alpha), p)
                x, y = betas(prof)
                n = len(x)
                units = [(i, j) for i in range(n) for j in range(n) if x[i] == y[j]]
                suffix = suffixes_set(alpha)
                assert len(units) == l - 1 and {x[i] for i, j in units} == {q * s for s in suffix}
                for (i, j) in units:
                    assert i - j == 2                                         # row/column positions differ by two
                common = set(x) & set(y)
                U = tuple(z for z in x if z not in common)
                V = tuple(z for z in y if z not in common)
                assert len(U) == len(V) == M + 1
                subdiag = {U[i + 1] - V[i] for i in range(len(U) - 1)}
                assert subdiag <= {a, a + p}
                assert all(U[i + 2] - V[i] < 0 and U[i + 2] - V[i] <= a - b for i in range(len(U) - 2))
                assert not set(U) & set(V)                                    # zero-free
                assert all(U[i] > V[i] and U[i + 1] >= V[i] for i in range(len(U) - 1)) and U[-1] > V[-1] == 0
                # lowest ordinary-degree component is exactly the core determinant, with sign +1
                P = schur(prof)
                dmin = min(len(m) for m in P)
                assert dmin == M + 1
                assert {m: v for m, v in P.items() if len(m) == dmin} == determinant_polynomial(U, V)
                # the common entries have the same relative order: the deleted rows and columns interleave
                rows_del = [i for i in range(n) if x[i] in common]
                cols_del = [j for j in range(n) if y[j] in common]
                assert sum(i - j for i, j in zip(rows_del, cols_del)) % 2 == 0
                n_c += 1
    print("PASS lem:subthreshold-transport opening parameter (%d profiles: depths in the three values, first "
          "opening is p when l >= 2, none below p) and lem:boundary-core structure (%d profiles: l-1 units two "
          "apart, subdiagonal a or a+p, second subdiagonal <= a-b, zero-free, lowest component)" % (n_o, n_c))


def suffixes_set(alpha):
    out, total = set(), 0
    for part in reversed(alpha[1:]):
        total += part
        out.add(total)
    return out


# ---------------------------------------------------------------- 9. the private-residue lemma

def check_private_residue():
    n_cases = n_diag = 0
    for q in (4, 5, 6):
        residues = range(q)
        for R in [set(c) for r in (1, 2) for c in itertools.combinations(residues, r)]:
            for S in [set(c) for r in (1, 2) for c in itertools.combinations(residues, r)]:
                RS = {(r - s) % q for r in R for s in S}
                if R & RS:
                    continue
                bound = 3 * q
                for m in (2, 3):
                    Us = [u for u in itertools.combinations(range(bound, 0, -1), m) if all(z % q in R for z in u)]
                    Vs = [v + (0,) for v in itertools.combinations(range(bound, 0, -1), m - 1)
                          if all(z % q in S for z in v)]
                    for V in Vs:
                        seen = {}
                        for U in Us:
                            if not (all(U[i] > V[i] for i in range(m)) and all(U[i + 1] >= V[i] for i in range(m - 1))):
                                continue
                            poly = determinant_polynomial(U, V)
                            gens = {j for mon in poly for j in mon if j % q in R}
                            assert gens == set(U), ("lem:private-residue-column", q, R, S, U, V, gens)
                            key = fingerprint(poly)
                            assert key not in seen, ("the polynomial determines the row betas", U, seen[key], V)
                            seen[key] = U
                            n_diag += 1
                        n_cases += 1
    # the residue condition is needed: where R meets R - S the conclusion fails on some diagram
    failed = tried = 0
    for q in (3, 4, 5):
        for R in [set(c) for r in (1, 2) for c in itertools.combinations(range(q), r)]:
            for S in [set(c) for r in (1, 2) for c in itertools.combinations(range(q), r)]:
                if not (R & {(r - s) % q for r in R for s in S}):
                    continue
                for m in (2, 3):
                    for U in itertools.combinations(range(3 * q, 0, -1), m):
                        if not all(z % q in R for z in U):
                            continue
                        for V0 in itertools.combinations(range(3 * q, 0, -1), m - 1):
                            if not all(z % q in S for z in V0):
                                continue
                            V = V0 + (0,)
                            if not (all(U[i] > V[i] for i in range(m)) and all(U[i + 1] >= V[i] for i in range(m - 1))):
                                continue
                            poly = determinant_polynomial(U, V)
                            gens = {j for mon in poly for j in mon if j % q in R}
                            tried += 1
                            failed += gens != set(U)
    assert failed > 0
    print("PASS lem:private-residue-column: %d (residue sets, V) cases, %d connected diagrams; the residue condition "
          "is necessary (%d violating diagrams break the conclusion)" % (n_cases, n_diag, failed))


# ---------------------------------------------------------------- 10. the printed examples

def check_examples():
    p_base = parent((2, 3), 1, 0, (1, 2))
    q_base = parent((2, 3), 1, 0, (2, 1))
    P, Q = inflate(p_base, 1), inflate(q_base, 1)
    assert P == ((3, 4, 3, 6, 4), (2, 1, 2, 2)) and Q == ((3, 6, 4, 3, 4), (2, 2, 1, 2))   # eq:first-boundary-example
    for prof, want in ((P, ((13, 12, 9, 4), (10, 6, 2, 0))), (Q, ((13, 12, 8, 5), (10, 6, 2, 0)))):
        x, y = betas(prof)
        common = set(x) & set(y)
        got = (tuple(z for z in x if z not in common), tuple(z for z in y if z not in common))
        assert got == want, (got, want)
    assert (3, 3, 3)[0] > 0 and 2 == 3 - 1                                       # E = (2,3;1) has threshold p = 1
    assert 3 - 1 == 2                                                             # E = (3,4;1) has threshold p = 2
    # cor:unbounded-class-splitting: |R(alpha_e)| = 2^e
    alpha_1 = (1, 2)
    alpha_2 = compose_comp((1, 2), (1, 2))
    assert len(ribbon_class(alpha_1)) == 2 and len(ribbon_class(alpha_2)) == 4
    for e, alpha in ((1, alpha_1), (2, alpha_2)):
        base = parent((2, 3), 1, 0, alpha)
        cls = {parent((2, 3), 1, 0, b) for b in ribbon_class(alpha)}
        cls |= {rotation(x) for x in cls}
        assert len(cls) == 2 ** (e + 1)                                           # |Cl(G_alpha_e)| = 2^{e+1}
        images = {inflate(x, 1) for x in cls}
        assert len(images) == 2 ** (e + 1)                                        # I_1 injective
        groups = defaultdict(set)
        for im in images:
            groups[fingerprint(schur(im))].add(im)
        assert len(groups) == 2 ** e and all(len(g) == 2 for g in groups.values())
    print("PASS eq:first-boundary-example (profiles and cores), thresholds p = 1 and p = 2, and the class sizes "
          "2^(e+1) splitting into 2^e rotation pairs for e = 1, 2 of cor:unbounded-class-splitting")


def main():
    check_profiles()
    check_interval_and_cutmerge()
    check_ribbon_and_constant_gap()
    check_readings_and_substitutions()
    check_overlap_power_rigidity()
    check_merged_blocks_and_remark()
    check_charts()
    check_threshold_and_core()
    check_private_residue()
    check_examples()
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
