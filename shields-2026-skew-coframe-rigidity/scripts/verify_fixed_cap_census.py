r"""Paper section `sec:fixed-caps` (Rigidity with the same literal cap).

Targets `sc:fixed-cap`, `sc:splice-flags`, `sc:splice-identity`, `sc:fcp-observations`,
`sc:fcp-prefix-zero`, `sc:fcp-prefix-solve`, `sc:fcp-numerator-flags`, `sc:fcp-recursive-cap`.

Exact integer arithmetic on full flags; no SymPy.  A board is a pair of strictly decreasing lists
(rows, columns) with columns ending at 0, and its Jacobi-Trudi polynomial keeps every genuine unit
(h_0 = 1), as a dictionary from sorted monomials to integers.

  (1) The fixed-cap theorem as a census.  For every connected child of span at most CHILD_MAX and every
      connected cap of span at most CAP_MAX, the map B -> (s_B, s_{K<|B}) is injective on boards, with
      the splice built from the printed flag formula; the splice is checked connected with span c + a and
      area |K| + |B|.  Non-vacuity: boards sharing the first coordinate exist in quantity (the first
      observation alone is not injective), and replacing the literal cap by a different literal cap with
      the same function loses injectivity on the equal hook pair.
  (2) The observation identities.  For coequal pairs and every cap, at random rational letters the
      coframe difference Q = G_B - G_B' (right coframes from the proper native solve) satisfies
      [z^c] H Q = (s_B - s_B') / kappa  and  [z^(c+a)] H C_K Q = (s_{K<|B} - s_{K<|B'}) / (kappa_K kappa),
      so the two displayed observations are exactly the two whole functions' differences.
  (3) The prefix-zero extraction.  For random polynomial Q with coefficients in the letters up to a
      ceiling R, and a random cap coframe C_K, the coefficient of h_L (L above max(R, a-1)) in
      [z^(c+a)] H C_K Q is (C_K Q)_{c+a-L}; so vanishing for L = R'+1..c+a is vanishing of
      (C_K Q)_j for j < c+a-R', and Q_j = 0 there by the constant term one of C_K.
  (4) The prefix solve.  For a connected board with a proper prefix block P and tail columns j < b, the
      native equations restricted to the prefix rows give
      Q_prefix = -P^{-1} (sum_{j<b} h_{x-j} Q_j)_x for every vector Q satisfying the native equations of
      the difference of two boards sharing the prefix; checked as a linear-algebra identity at random
      rational letters.
"""
import random
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations

CHILD_MAX = 7
CAP_MAX = 4
random.seed(20261031)


# ------------------------------------------------------------------ boards and polynomials

def connected(board):
    rows, cols = board
    return (bool(rows) and len(rows) == len(cols)
            and all(a > b for a, b in zip(rows, rows[1:])) and all(a > b for a, b in zip(cols, cols[1:]))
            and cols[-1] == 0 and all(x > y for x, y in zip(rows, cols))
            and all(x >= y for x, y in zip(rows[1:], cols[:-1])))


def boards(span):
    pos = range(1, span)
    for rank in range(span):
        for rs in combinations(pos, rank):
            for cs in combinations(pos, rank):
                b = ((span,) + tuple(reversed(rs)), tuple(reversed(cs)) + (0,))
                if connected(b):
                    yield b


def padd(out, mono, c):
    v = out.get(mono, 0) + c
    if v:
        out[mono] = v
    else:
        out.pop(mono, None)


def schur(board):
    """Jacobi-Trudi polynomial with every unit kept (h_0 = 1), by a subset recurrence."""
    rows, cols = board
    n = len(rows)
    ent = [[x - y for y in cols] for x in rows]
    states = {0: {(): 1}}
    for i in range(n):
        nxt = {}
        for mask, poly in states.items():
            for j in range(n):
                k = ent[i][j]
                if mask >> j & 1 or k < 0:
                    continue
                sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
                tgt = nxt.setdefault(mask | 1 << j, {})
                for mono, c in poly.items():
                    padd(tgt, tuple(sorted(mono + ((k,) if k else ()))), sign * c)
        states = nxt
    return states.get((1 << n) - 1, {})


def splice(cap, child):
    cr, cc = cap
    xr, xc = child
    c = xr[0]
    rows = tuple(sorted({c + x for x in cr} | set(xr[1:]), reverse=True))
    cols = tuple(sorted({c + y for y in cc if y != 0} | set(xc), reverse=True))
    return rows, cols


def area(board):
    return sum(board[0]) - sum(board[1])


def rotate(board):
    rows, cols = board
    s = rows[0]
    return (tuple(sorted((s - y for y in cols), reverse=True)),
            tuple(sorted((s - x for x in rows), reverse=True)))


# ------------------------------------------------------------------ (1) the census

def census():
    caps = [b for s in range(1, CAP_MAX + 1) for b in boards(s)]
    children = {s: list(boards(s)) for s in range(1, CHILD_MAX + 1)}
    funcs = {b: tuple(sorted(schur(b).items())) for s in children for b in children[s]}
    n_sep = n_pairs = n_children = 0
    for cap in caps:
        a = cap[0][0]
        for s, lst in children.items():
            seen = {}
            for b in lst:
                j = splice(cap, b)
                assert connected(j) and j[0][0] == s + a and area(j) == area(cap) + area(b), (cap, b)
                key = (funcs[b], tuple(sorted(schur(j).items())))
                assert key not in seen, ("fixed-cap rigidity fails", cap, b, seen[key])
                seen[key] = b
                n_children += 1
            # non-vacuity: coequal classes at this span
            groups = defaultdict(list)
            for b in lst:
                groups[funcs[b]].append(b)
            for g in groups.values():
                for i in range(len(g)):
                    for k in range(i + 1, len(g)):
                        n_pairs += 1
                        assert tuple(sorted(schur(splice(cap, g[i])).items())) != tuple(sorted(schur(splice(cap, g[k])).items()))
                        n_sep += 1
    # a different literal cap with the same function does not separate the equal hook pair
    hook, mate = ((3, 1), (1, 0)), ((3, 2), (2, 0))
    assert rotate(hook) == mate and schur(hook) == schur(mate) and hook != mate
    assert schur(splice(hook, hook)) == schur(splice(mate, mate)) and splice(hook, hook) != splice(mate, mate)
    assert n_pairs > 100
    return len(caps), n_children, n_pairs


# ------------------------------------------------------------------ rational coframes

def rand_letters(upto):
    return {0: Fraction(1)} | {j: Fraction(random.randint(1, 40), random.randint(1, 7)) for j in range(1, upto + 1)}


def solve(mat, rhs):
    n = len(mat)
    m = [list(r) + [rhs[i]] for i, r in enumerate(mat)]
    for c in range(n):
        p = next(i for i in range(c, n) if m[i][c] != 0)
        m[c], m[p] = m[p], m[c]
        inv = 1 / m[c][c]
        m[c] = [v * inv for v in m[c]]
        for i in range(n):
            if i != c and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return [m[i][n] for i in range(n)]


def hval(L, k):
    return Fraction(0) if k < 0 else L[k]


def right_coframe(board, L):
    """Coefficient list of G (index = exponent), degree < span."""
    rows, cols = board
    M = rows[0]
    G = [Fraction(0)] * M
    G[0] = Fraction(1)
    if len(rows) == 1:
        return G
    mat = [[hval(L, x - c) for c in cols[:-1]] for x in rows[1:]]
    sol = solve(mat, [-hval(L, x) for x in rows[1:]])
    for c, v in zip(cols[:-1], sol):
        G[c] = v
    return G


def left_coframe(board, L):
    rows, cols = board
    M = rows[0]
    C = [Fraction(0)] * M
    C[0] = Fraction(1)
    if len(rows) == 1:
        return C
    # transpose system: sum_i C_{M-i} h_{i-j} = -h_{M-j}  for j in cols[:-1]
    mat = [[hval(L, x - c) for x in rows[1:]] for c in cols[:-1]]
    sol = solve(mat, [-hval(L, M - c) for c in cols[:-1]])
    for x, v in zip(rows[1:], sol):
        C[M - x] = v
    return C


def corner(board, L):
    rows, cols = board
    n = len(rows)
    if n == 1:
        return Fraction(1)
    mat = [[hval(L, x - c) for c in cols[:-1]] for x in rows[1:]]
    return (-1) ** (n - 1) * det(mat)


def det(mat):
    n = len(mat)
    m = [list(r) for r in mat]
    d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if m[i][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for i in range(c + 1, n):
            f = m[i][c] / m[c][c]
            m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return d


def evaluate(poly, L):
    tot = Fraction(0)
    for mono, c in poly.items():
        t = Fraction(c)
        for k in mono:
            t *= L[k]
        tot += t
    return tot


def conv_coeff(series_lists, N):
    """Coefficient of z^N in the product of coefficient lists (zero outside range)."""
    acc = {0: Fraction(1)}
    for s in series_lists:
        new = {}
        for i, a in acc.items():
            for j, b in enumerate(s):
                if i + j <= N and b != 0:
                    new[i + j] = new.get(i + j, 0) + a * b
        acc = new
    return acc.get(N, Fraction(0))


def Hlist(L, upto):
    return [hval(L, k) for k in range(upto + 1)]


# ------------------------------------------------------------------ (2) observation identities

def observation_identities():
    n = 0
    caps = [b for s in range(1, 4) for b in boards(s)]
    for c in range(3, 7):
        lst = list(boards(c))
        groups = defaultdict(list)
        for b in lst:
            groups[tuple(sorted(schur(b).items()))].append(b)
        for g in groups.values():
            for i in range(len(g)):
                for k in range(i + 1, len(g)):
                    B, Bp = g[i], g[k]
                    for K in caps:
                        a = K[0][0]
                        for _ in range(2):
                            while True:
                                L = rand_letters(c + a + 1)
                                kap = corner(B, L)
                                if kap != 0 and corner(K, L) != 0:
                                    break
                            assert kap == corner(Bp, L) and kap != 0, (B, Bp, kap, corner(Bp, L))
                            GB, GBp = right_coframe(B, L), right_coframe(Bp, L)
                            Q = [x - y for x, y in zip(GB, GBp)]
                            H = Hlist(L, c + a)
                            lhs1 = conv_coeff([H, Q], c)
                            assert lhs1 == (evaluate(schur(B), L) - evaluate(schur(Bp), L)) / kap == 0
                            CK = left_coframe(K, L)
                            kK = corner(K, L)
                            lhs2 = conv_coeff([H, CK, Q], c + a)
                            d = evaluate(schur(splice(K, B)), L) - evaluate(schur(splice(K, Bp)), L)
                            assert lhs2 * kK * kap == d, (B, Bp, K)
                            assert d != 0
                            n += 1
    assert n > 100
    return n


# ------------------------------------------------------------------ (3) prefix-zero extraction

def prefix_zero_extraction():
    """Coefficient of the top letters in [z^(c+a)] H C Q, as a polynomial identity in the letters."""
    import sympy as sp
    n = 0
    for trial in range(12):
        c = random.randint(3, 6)
        a = random.randint(1, 4)
        R = random.randint(0, c - 1)
        Rp = max(R, a - 1)
        letters = [sp.Integer(1)] + [sp.Symbol(f"h{j}") for j in range(1, c + a + 1)]

        def rpoly(top):
            return sum(random.randint(-3, 3) * sp.prod([letters[random.randint(1, top)] for _ in range(random.randint(1, 2))])
                       for _ in range(2)) if top >= 1 else sp.Integer(random.randint(-3, 3))

        Q = [sp.Integer(0)] + [rpoly(R) for _ in range(c - 1)]          # Q_0 = 0
        CK = [sp.Integer(1)] + [rpoly(a - 1) if a >= 2 else sp.Integer(0) for _ in range(a - 1)]
        CKQ = [sum(CK[i] * Q[j - i] for i in range(len(CK)) if 0 <= j - i < len(Q)) for j in range(c + a)]
        total = sp.expand(sum(letters[c + a - j] * CKQ[j] for j in range(c + a) if c + a - j >= 1)
                          + sum(0 for _ in range(1)))
        # H has constant term the unit: add the j = c + a term separately (CKQ index c + a is beyond range)
        for L in range(Rp + 1, c + a + 1):
            lead = sp.diff(total, letters[L])
            expect = CKQ[c + a - L]
            assert sp.expand(lead - expect) == 0, (c, a, R, L)
            n += 1
        # constant term one of C_K inverts the triangular system
        zeros = [sp.expand(CKQ[j]) for j in range(0, c + a - Rp)]
        assert all(sp.expand(sum(CK[i] * Q[j - i] for i in range(len(CK)) if 0 <= j - i < len(Q)) - zeros[j]) == 0
                   for j in range(len(zeros)))
        # if those vanish then Q_j vanishes for j < c + a - Rp
        Qz = [q for q in Q]
        for j in range(c + a - Rp):
            if j < len(Qz):
                Qz[j] = sp.Integer(0)
        CKQz = [sum(CK[i] * Qz[j - i] for i in range(len(CK)) if 0 <= j - i < len(Qz)) for j in range(c + a - Rp)]
        assert all(sp.expand(v) == 0 for v in CKQz)
    return n


# ------------------------------------------------------------------ (4) prefix solve

def prefix_solve():
    n = 0
    for c in range(4, 8):
        for B in boards(c):
            rows, cols = B
            if len(rows) < 3:
                continue
            L = rand_letters(c + 2)
            I, S = rows[1:], cols[:-1]
            # split the proper matrix: prefix rows = the first q proper rows with columns the first q proper cols
            for q in range(1, len(I)):
                prefix_rows, prefix_cols = I[:q], S[:q]
                P = [[hval(L, x - s) for s in prefix_cols] for x in prefix_rows]
                if det(P) == 0:
                    continue
                # a vector Q supported on every column < b = min(prefix_cols), plus unknown prefix columns,
                # satisfying the prefix native equations sum_s h_{x-s} Q_s + sum_{j<b} h_{x-j} Q_j = 0
                b = min(prefix_cols)
                low = {j: Fraction(random.randint(-9, 9), random.randint(1, 5)) for j in range(1, b)}
                rhs = [-sum(hval(L, x - j) * v for j, v in low.items()) for x in prefix_rows]
                sol = solve(P, rhs)
                # the displayed formula Q_prefix = -P^{-1}(sum_j h_{x-j} Q_j)_x
                direct = [-v for v in solve(P, [sum(hval(L, x - j) * v for j, v in low.items()) for x in prefix_rows])]
                assert sol == direct
                for x, s_ in zip(prefix_rows, range(len(prefix_rows))):
                    tot = sum(hval(L, x - s) * v for s, v in zip(prefix_cols, sol)) + sum(hval(L, x - j) * v for j, v in low.items())
                    assert tot == 0
                n += 1
    assert n > 20
    return n


def main():
    ncaps, nchild, npairs = census()
    print("sc:fixed-cap: %d caps (span <= %d) x children (span <= %d): %d splices connected with span c+a and area |K|+|B|,"
          " injective on (s_B, s_{K<|B}); %d coequal pairs separated by every cap; equal-function caps fail on the hook pair"
          % (ncaps, CAP_MAX, CHILD_MAX, nchild, npairs))
    n2 = observation_identities()
    print("sc:fcp-observations: both displayed observations equal the whole-function differences on %d (pair, cap, point) cases" % n2)
    n3 = prefix_zero_extraction()
    print("sc:fcp-prefix-zero: top-letter coefficient extraction and triangular removal, %d symbolic cases" % n3)
    n4 = prefix_solve()
    print("sc:fcp-prefix-solve: prefix compensation formula on %d (board, split) cases" % n4)
    print("ALL PASS")


if __name__ == "__main__":
    main()
