"""Corroboration for the cofactor-relation theorem and the steps its induction uses.

Paper section `sec:cofactors` (Linear relations among cofactors).

Every claim below is read off the manuscript and re-derived here from the
definitions, not from the proof's own bookkeeping.

Checked, for dense boards built from strict beta lists:

  (1) eq:cofactor-degree      deg D_ij = |C| - (a_i - b_j).
  (2) thm:cofactor-relations  rank{D_ij} = n^2 when C != C*, n(n+1)/2 when C = C*.
                              Repeated entry labels are tracked and must occur.
  (3) eq:interlaced-indices   d_1 > e_1 > d_2 > ... > e_{n-1} > d_n > 0 on symmetric boards.
  (4) eq:symmetric-leader     for i <= j the maximum-square matching of the reversed
                              symmetric matrix is UNIQUE and its monomial is the stated
                              product; the monomials are distinct for distinct (i,j).
  (5) eq:private-derivative   dD_ij/dh_N = (-1)^(n-1) D^R_{i-1,j} for i > 1, j < n,
                              and vanishes on the first row and last column.
  (6) the R = R* branch       u != v, and after the rotation normalizing u < v the label
                              h_{a_2} is private at (2,n), and Q is nonsymmetric.
  (7) lem:boundary-pair       D_1j and D_in are not proportional when a_i + b_j = N.

A guard that cannot fail is not a guard: non_vacuity() asserts that every sweep above
actually fired, separately for the nonsymmetric, symmetric, and repeated-label
populations, and that the R = R* branch of (6) was reached at all.
"""

from fractions import Fraction
from itertools import combinations, permutations

# ---------------------------------------------------------------- boards


def dense_boards(n, max_N):
    """Strict normalized lists A=(N=a_1>...>a_n), B=(b_1>...>b_n=0) with a_n > b_1."""
    out = []
    for N in range(1, max_N + 1):
        # A: a_1 = N, strictly decreasing, n entries, a_n >= 1
        for rest_a in combinations(range(1, N), n - 1):
            A = (N,) + tuple(sorted(rest_a, reverse=True))
            # B: b_n = 0, strictly decreasing, n entries, b_1 < a_n
            for rest_b in combinations(range(1, A[-1]), n - 1):
                B = tuple(sorted(rest_b, reverse=True)) + (0,)
                out.append((A, B))
    return out


def is_symmetric(A, B):
    """eq:rotation-condition: a_i + b_{n+1-i} = N."""
    N, n = A[0], len(A)
    return all(A[i] + B[n - 1 - i] == N for i in range(n))


def labels(A, B):
    return [[A[i] - B[j] for j in range(len(B))] for i in range(len(A))]


def n_distinct_labels(A, B):
    return len({x for row in labels(A, B) for x in row})


# ------------------------------------------------- polynomials as monomial dicts
# A monomial is a sorted tuple of positive h-indices.  h_0 = 1, h_j = 0 for j < 0.


def det_poly(idx):
    """Determinant of the matrix of h-indices, as {monomial: coeff}."""
    m = len(idx)
    if m == 0:
        return {(): Fraction(1)}
    out = {}
    for perm in permutations(range(m)):
        sign = perm_sign(perm)
        mono = []
        ok = True
        for r in range(m):
            e = idx[r][perm[r]]
            if e < 0:
                ok = False
                break
            if e > 0:  # h_0 = 1 contributes nothing
                mono.append(e)
        if not ok:
            continue
        key = tuple(sorted(mono))
        out[key] = out.get(key, Fraction(0)) + sign
    return {k: v for k, v in out.items() if v != 0}


def perm_sign(perm):
    seen = [False] * len(perm)
    sign = 1
    for i in range(len(perm)):
        if seen[i]:
            continue
        j, ln = i, 0
        while not seen[j]:
            seen[j] = True
            j = perm[j]
            ln += 1
        if ln % 2 == 0:
            sign = -sign
    return Fraction(sign)


def minor_idx(idx, di, dj):
    return [[idx[r][c] for c in range(len(idx[0])) if c != dj]
            for r in range(len(idx)) if r != di]


def cofactors(A, B):
    """Signed cofactors D_ij, as a dict (i,j) -> polynomial."""
    idx = labels(A, B)
    n = len(A)
    D = {}
    for i in range(n):
        for j in range(n):
            p = det_poly(minor_idx(idx, i, j))
            s = Fraction((-1) ** (i + j))
            D[(i, j)] = {k: s * v for k, v in p.items()}
    return D


def rank_of(polys):
    """Rank over Q of a list of polynomials regarded as coefficient vectors."""
    monos = sorted({m for p in polys for m in p})
    rows = [[p.get(m, Fraction(0)) for m in monos] for p in polys]
    return gauss_rank(rows)


def gauss_rank(rows):
    rows = [r[:] for r in rows]
    nr, nc = len(rows), len(rows[0]) if rows else 0
    rank, piv = 0, 0
    for col in range(nc):
        sel = None
        for r in range(rank, nr):
            if rows[r][col] != 0:
                sel = r
                break
        if sel is None:
            continue
        rows[rank], rows[sel] = rows[sel], rows[rank]
        pv = rows[rank][col]
        rows[rank] = [x / pv for x in rows[rank]]
        for r in range(nr):
            if r != rank and rows[r][col] != 0:
                f = rows[r][col]
                rows[r] = [a - f * b for a, b in zip(rows[r], rows[rank])]
        rank += 1
        piv += 1
        if rank == nr:
            break
    return rank


def total_degree(poly):
    return max(len(m) for m in poly) if poly else None


def weighted_degree(poly):
    """Sum of h-indices of any monomial; the cofactor is homogeneous in that grading."""
    degs = {sum(m) for m in poly}
    assert len(degs) == 1, degs
    return degs.pop()


# ---------------------------------------------------------------- the checks

STATS = dict(boards=0, nonsym=0, sym=0, repeated=0, repeated_nonsym=0,
             degree=0, leader=0, interlaced=0, deriv=0, deriv_zero=0,
             RR_branch=0, Q_nonsym=0, boundary_pairs=0, base_case=0,
             positive_indices=0)


def check_positivity(A, B):
    """Density means every Jacobi-Trudi index is positive, minors included.

    Recorded as a positive fact rather than left implicit, because it pins the SCOPE
    of everything below: on a dense board the convention h_j = 0 for j < 0 is never
    reached, so nothing here corroborates that convention.  A mutation removing the
    negative-index guard in det_poly is undetectable on this population, and that is
    a true statement about dense boards, not a gap in the sweep.
    """
    for row in labels(A, B):
        for e in row:
            assert e > 0, f"density violated: nonpositive index {e} in {A} {B}"
    STATS["positive_indices"] += 1


def check_degree(A, B, D):
    """(1) eq:cofactor-degree."""
    n = len(A)
    area = sum(A) - sum(B)
    for i in range(n):
        for j in range(n):
            p = D[(i, j)]
            assert p, f"cofactor vanished, contradicting density: {A} {B} {(i,j)}"
            got = weighted_degree(p)
            want = area - (A[i] - B[j])
            assert got == want, f"eq:cofactor-degree {A} {B} ({i},{j}): {got} != {want}"
            STATS["degree"] += 1


def check_rank(A, B, D):
    """(2) thm:cofactor-relations."""
    n = len(A)
    r = rank_of([D[(i, j)] for i in range(n) for j in range(n)])
    if is_symmetric(A, B):
        want = n * (n + 1) // 2
        assert r == want, f"symmetric rank {A} {B}: {r} != {want}"
    else:
        want = n * n
        assert r == want, f"nonsymmetric rank {A} {B}: {r} != {want}"
    return r


def check_interlaced_and_leader(A, B):
    """(3) eq:interlaced-indices and (4) eq:symmetric-leader, symmetric boards only."""
    n, N = len(A), A[0]
    d = [2 * A[i] - N for i in range(n)]
    e = [A[i] + A[i + 1] - N for i in range(n - 1)]
    chain = []
    for i in range(n):
        chain.append(d[i])
        if i < n - 1:
            chain.append(e[i])
    assert all(x > y for x, y in zip(chain, chain[1:])), f"eq:interlaced-indices {A}: {chain}"
    assert chain[-1] > 0, f"eq:interlaced-indices positivity {A}: {chain}"
    STATS["interlaced"] += 1

    # reversed-column symmetric matrix S_ij = h_{a_i + a_j - N}
    S = [[A[i] + A[j] - N for j in range(n)] for i in range(n)]
    seen = {}
    for i in range(n):
        for j in range(i, n):
            rows = [r for r in range(n) if r != i]
            cols = [c for c in range(n) if c != j]
            # maximize sum of squares over surviving matchings
            best, arg, ties = None, None, 0
            for perm in permutations(range(n - 1)):
                idxs = [S[rows[r]][cols[perm[r]]] for r in range(n - 1)]
                if any(x < 0 for x in idxs):
                    continue
                w = sum(x * x for x in idxs)
                if best is None or w > best:
                    best, arg, ties = w, tuple(sorted(idxs)), 1
                elif w == best:
                    ties += 1
            assert ties == 1, f"max-square matching not unique {A} ({i},{j}): {ties} ties"
            # order-preserving pairing is the claimed argmax
            op = tuple(sorted(S[rows[r]][cols[r]] for r in range(n - 1)))
            assert arg == op, f"argmax is not order-preserving {A} ({i},{j})"
            # and it equals eq:symmetric-leader (1-indexed i+1, j+1)
            ii, jj = i + 1, j + 1
            formula = ([d[t - 1] for t in range(1, ii)]
                       + [e[t - 1] for t in range(ii, jj)]
                       + [d[t - 1] for t in range(jj + 1, n + 1)])
            assert tuple(sorted(formula)) == op, (
                f"eq:symmetric-leader {A} ({ii},{jj}): {sorted(formula)} != {list(op)}")
            assert all(x > 0 for x in formula), f"leader index not positive {A}"
            key = tuple(sorted(formula))
            assert key not in seen, (
                f"leaders collide {A}: ({ii},{jj}) and {seen[key]} both {list(key)}")
            seen[key] = (ii, jj)
            STATS["leader"] += 1


def check_private_derivative(A, B, D):
    """(5) eq:private-derivative."""
    n, N = len(A), A[0]
    # h_N is private at (1,n) -- i.e. label N occurs exactly once in the board
    flat = [x for row in labels(A, B) for x in row]
    assert flat.count(N) == 1, f"h_N not private {A} {B}"
    R = (tuple(A[1:]), tuple(B[:-1]))          # (A \ {N}, B \ {0})
    DR = cofactors(R[0], R[1])
    sign = Fraction((-1) ** (n - 1))
    for i in range(n):
        for j in range(n):
            dd = ddh(D[(i, j)], N)
            if i == 0 or j == n - 1:
                assert not dd, f"derivative should vanish {A} {B} ({i},{j})"
                STATS["deriv_zero"] += 1
            else:
                want = {k: sign * v for k, v in DR[(i - 1, j)].items()}
                assert dd == want, f"eq:private-derivative {A} {B} ({i},{j})"
                STATS["deriv"] += 1
    return R


def ddh(poly, k):
    """Partial derivative with respect to h_k."""
    out = {}
    for mono, c in poly.items():
        mult = mono.count(k)
        if not mult:
            continue
        rest = list(mono)
        rest.remove(k)
        key = tuple(sorted(rest))
        out[key] = out.get(key, Fraction(0)) + c * mult
    return {k2: v for k2, v in out.items() if v != 0}


def check_RR_branch(A, B):
    """(6) the R = R* branch: u != v, h_{a_2} private at (2,n) after u < v, Q nonsymmetric."""
    n, N = len(A), A[0]
    R = (tuple(A[1:]), tuple(B[:-1]))
    if not is_symmetric_pair(R[0], R[1]):
        return False
    STATS["RR_branch"] += 1
    u, v = N - A[1], B[n - 2]
    assert u != v, f"u = v on a nonsymmetric parent {A} {B}"
    # the manuscript rotates to make u < v; verify the claim in that orientation
    AA, BB = (A, B) if u < v else rotate(A, B)
    NN = AA[0]
    uu, vv = NN - AA[1], BB[n - 2]
    assert uu < vv, f"rotation did not normalize u < v: {AA} {BB}"
    flat = [x for row in labels(AA, BB) for x in row]
    assert flat.count(AA[1]) == 1, (
        f"h_a2 not private at (2,n) after normalization {AA} {BB}")
    # every first-row label outside the corner is at most N - v < a_2.
    # The corner is (1,n), so 0-indexed the non-corner first-row sites are j < n-1.
    first = [AA[0] - BB[j] for j in range(0, n - 1)]
    assert max(first) <= NN - vv < AA[1], f"first-row bound fails {AA} {BB}"
    Q = (tuple(x for x in AA if x != AA[1]), tuple(BB[:-1]))
    assert not is_symmetric_pair(Q[0], Q[1]), f"Q is symmetric {AA} {BB}"
    STATS["Q_nonsym"] += 1
    return True


def is_symmetric_pair(A, B):
    """Symmetry of a possibly unnormalized pair: A = c - B as sets for some c."""
    if len(A) != len(B):
        return False
    c = A[0] + B[-1]
    return sorted(A) == sorted(c - b for b in B)


def rotate(A, B):
    """Rotate the board: complement both lists in N and swap roles."""
    N = A[0]
    nA = tuple(sorted((N - b for b in B), reverse=True))
    nB = tuple(sorted((N - a for a in A), reverse=True))
    sh = nB[-1]
    return tuple(x - sh for x in nA), tuple(x - sh for x in nB)


def check_order_one_is_symmetric():
    """Nonsymmetry supplies order >= 2, so the paper need not assume it.

    thm:dilation requires order at least two, yet the introduction says that on the
    nonsymmetric dense class the formula carries no hypothesis beyond density and
    nonsymmetry.  That is exact only if nonsymmetry already forces order >= 2.

    It does, by identity rather than by census: at n = 1 the normalized lists are
    A = (N), B = (0), and eq:rotation-condition reads a_1 + b_1 = N + 0 = N, which
    holds always.  Every order-one core is therefore rotation-fixed.  The loop below
    is a regression guard on is_symmetric, not evidence for the claim.
    """
    for N in range(1, 200):
        assert is_symmetric((N,), (0,)), f"order-one core not symmetric at N={N}"
    print("order-one cores are all symmetric: nonsymmetry supplies order >= 2.")


def check_base_case(A, B):
    """The n = 2 base case: on a nonsymmetric dense board the four labels are distinct."""
    flat = [x for row in labels(A, B) for x in row]
    assert len(set(flat)) == 4, f"n=2 base case: labels not distinct {A} {B}: {flat}"
    STATS["base_case"] += 1


def check_boundary_pair(A, B, D):
    """(7) lem:boundary-pair."""
    n, N = len(A), A[0]
    for i in range(1, n):
        for j in range(0, n - 1):
            if A[i] + B[j] != N:
                continue
            P, Qq = D[(0, j)], D[(i, n - 1)]
            assert rank_of([P, Qq]) == 2, (
                f"lem:boundary-pair: proportional cofactors {A} {B} i={i+1} j={j+1}")
            STATS["boundary_pairs"] += 1


# ---------------------------------------------------------------- driver


def non_vacuity():
    assert STATS["boards"] >= 200, STATS
    assert STATS["nonsym"] >= 100, STATS
    assert STATS["sym"] >= 5, STATS
    assert STATS["repeated"] >= 20, STATS
    assert STATS["repeated_nonsym"] >= 20, STATS
    assert STATS["degree"] >= 800, STATS
    assert STATS["interlaced"] >= 5, STATS
    assert STATS["leader"] >= 15, STATS
    assert STATS["deriv"] >= 100, STATS
    assert STATS["deriv_zero"] >= 100, STATS
    assert STATS["base_case"] >= 50, STATS
    assert STATS["positive_indices"] == STATS["boards"], STATS
    assert STATS["RR_branch"] >= 1, STATS
    assert STATS["Q_nonsym"] >= 1, STATS
    assert STATS["boundary_pairs"] >= 5, STATS
    print("NON-VACUITY: every sweep fired.")
    for k in sorted(STATS):
        print(f"  {k:18s} {STATS[k]}")


def main():
    check_order_one_is_symmetric()
    plan = [(2, 11), (3, 11), (4, 12)]
    for n, max_N in plan:
        boards = dense_boards(n, max_N)
        print(f"n = {n}: {len(boards)} dense boards, N <= {max_N}")
        for A, B in boards:
            STATS["boards"] += 1
            sym = is_symmetric(A, B)
            STATS["sym" if sym else "nonsym"] += 1
            rep = n_distinct_labels(A, B) < n * n
            if rep:
                STATS["repeated"] += 1
                if not sym:
                    STATS["repeated_nonsym"] += 1
            D = cofactors(A, B)
            check_positivity(A, B)
            check_degree(A, B, D)
            check_rank(A, B, D)
            if sym:
                check_interlaced_and_leader(A, B)
            else:
                # lem:boundary-pair is stated for NONSYMMETRIC dense C only.  At n = 2
                # the collision a_i + b_j = N with i > 1, j < n IS the symmetry
                # condition, so the lemma has no content there and the paper says so
                # in its own base case; applying it to a symmetric board finds
                # D_11 = D_22 and refutes nothing.
                check_boundary_pair(A, B, D)
                if n == 2:
                    # The proof handles n = 2 as a separate base case: the four labels
                    # are distinct unless a_2 = N - b_1, which is exactly symmetry.
                    # eq:private-derivative and the R = R* branch belong to the n >= 3
                    # step and are not claimed here -- at n = 2 the child R has order
                    # one and is trivially rotation-invariant, so "Q nonsymmetric"
                    # is not a claim the paper makes.
                    check_base_case(A, B)
                else:
                    check_private_derivative(A, B, D)
                    check_RR_branch(A, B)

    # The extremal repeated-label witness found by the sweep: a nonsymmetric dense
    # board of order four whose 16 sites carry only 8 distinct entry labels, whose
    # 16 signed cofactors are nevertheless independent.  This is the sharpest
    # corroboration of the claim that the nonsymmetric clause permits arbitrarily
    # many repeated entry labels.
    A, B = (8, 6, 5, 4), (3, 2, 1, 0)
    n = len(A)
    d = n_distinct_labels(A, B)
    print(f"\nextremal repeated-label witness A={A} B={B}")
    print(f"  labels {labels(A, B)}")
    print(f"  distinct labels {d} of {n*n}, symmetric={is_symmetric(A, B)}")
    D = cofactors(A, B)
    r = rank_of([D[(i, j)] for i in range(n) for j in range(n)])
    print(f"  cofactor rank {r} of {n*n}")
    assert d == 8 and r == 16, "extremal witness changed; re-derive before trusting it"

    non_vacuity()
    print("\nALL PASS")


if __name__ == "__main__":
    main()
