"""Independent literal-cell checks of the four-row wall conclusion.

Profiles are converted to cells before every Jacobi--Trudi evaluation.  Exact
modular elimination certifies inequalities; equal controls are proved by literal
rotation or by full interval-polynomial expansion.  There is no use of the
parameter classifier or selected-coefficient implementation.
"""
from collections import Counter
from hashlib import sha256
from itertools import product

PRIME = 2**61 - 1


def compositions(n):
    if n == 0:
        yield ()
    else:
        for a in range(1, n + 1):
            for tail in compositions(n - a):
                yield (a,) + tail


def build_inner(a, b, c, e, f, p):
    return (a + p, a + b + e, b + c + f, c + p), (a, b, c)


def parent(E, alpha, t):
    r, g = E
    rows, gaps = [], []
    for part in alpha:
        block_rows, block_gaps = list(r), list(g)
        for _ in range(part - 1):
            block_rows[-1] += r[0]
            block_rows.extend(r[1:])
            block_gaps.extend(g)
        if rows:
            gaps.append(0)
        rows.extend(block_rows)
        gaps.extend(block_gaps)
    return tuple(x + t for x in rows), tuple(x + t for x in gaps)


def cells(profile):
    r, g = profile
    assert len(g) == len(r) - 1
    assert all(0 <= s < min(r[i], r[i + 1]) for i, s in enumerate(g))
    start = [0] * len(r)
    for i in range(len(r) - 2, -1, -1):
        start[i] = start[i + 1] + r[i + 1] - g[i] - 1
    shape = frozenset((i, j) for i in range(len(r)) for j in range(start[i], start[i] + r[i]))
    lam = tuple(max(j for ii, j in shape if ii == i) + 1 for i in range(len(r)))
    mu = tuple(min(j for ii, j in shape if ii == i) for i in range(len(r)))
    assert all(lam[i] >= lam[i + 1] and mu[i] >= mu[i + 1] for i in range(len(r) - 1))
    assert sum(r) == len(shape)
    return shape


def index_board(shape):
    n = 1 + max(i for i, _ in shape)
    lam, mu = [], []
    for i in range(n):
        cols = sorted(j for ii, j in shape if ii == i)
        assert cols == list(range(cols[0], cols[-1] + 1))
        lam.append(cols[-1] + 1)
        mu.append(cols[0])
    return tuple(tuple(lam[i] - mu[j] - i + j for j in range(n)) for i in range(n))


def normalize(shape):
    a, b = min(i for i, _ in shape), min(j for _, j in shape)
    return frozenset((i - a, j - b) for i, j in shape)


def rotate(shape):
    return normalize(frozenset((-i, -j) for i, j in shape))


def alphabet(maxlabel, seed):
    return [1] + [1 + int.from_bytes(sha256(f'{seed}:{j}'.encode()).digest(), 'big') % (PRIME - 1)
                  for j in range(1, maxlabel + 1)]


def value(board, H):
    mat = [[H[d] if d >= 0 else 0 for d in row] for row in board]
    det = 1
    for i in range(len(mat)):
        k = next((k for k in range(i, len(mat)) if mat[k][i]), None)
        if k is None:
            return 0
        if k != i:
            mat[k], mat[i] = mat[i], mat[k]
            det = -det
        pivot = mat[i][i]
        det = det * pivot % PRIME
        inv = pow(pivot, -1, PRIME)
        for k in range(i + 1, len(mat)):
            if mat[k][i] == 0:
                continue
            factor = mat[k][i] * inv % PRIME
            for j in range(i + 1, len(mat)):
                mat[k][j] = (mat[k][j] - factor * mat[i][j]) % PRIME
            mat[k][i] = 0
    return det % PRIME


def interval_polynomial(profile):
    rows, gaps = profile
    board = index_board(cells(profile))
    n = len(rows)
    assert all(board[i][j] < 0 for i in range(n) for j in range(i - 1))
    result = Counter()
    for mask in range(1 << (n - 1)):
        ends = [0] + [j + 1 for j in range(n - 1) if mask & (1 << j)] + [n]
        mon = []
        for lo, hi in zip(ends, ends[1:]):
            mon.append(sum(rows[lo:hi]) - sum(gaps[lo:hi - 1]))
            mon.extend(g for g in gaps[lo:hi - 1] if g)
        result[tuple(sorted(mon))] += (-1) ** (n - (len(ends) - 1))
    return {m: c for m, c in result.items() if c}


def main():
    outer_pairs = [(a, a[::-1]) for M in range(3, 6) for a in compositions(M) if a < a[::-1]]
    assert len(outer_pairs) == sum((2 ** (M - 1) - 2 ** (M // 2)) // 2 for M in range(3, 6)) == 9
    H = [alphabet(300, seed) for seed in range(3)]
    separated = symmetric = later = 0
    for pars in product(range(1, 4), repeat=6):
        a, b, c, e, f, p = pars
        E = build_inner(*pars)
        for alpha, rev in outer_pairs:
            F = cells(parent(E, alpha, p))
            G = cells(parent(E, rev, p))
            if a == c and e == f:
                assert rotate(F) == G and F != G
                symmetric += 1
                continue
            assert F != G and rotate(F) != G
            A, B = index_board(F), index_board(G)
            assert any(value(A, h) != value(B, h) for h in H), (pars, alpha)
            separated += 1
        # Independent checks after the wall, rather than inferring them in code.
        alpha, rev = (1, 2), (2, 1)
        if a != c or e != f:
            A = index_board(cells(parent(E, alpha, p + 2)))
            B = index_board(cells(parent(E, rev, p + 2)))
            assert any(value(A, h) != value(B, h) for h in H), (pars, 'later')
            later += 1
    assert separated == (3**6 - 3**4) * 9 == 5832
    assert symmetric == 3**4 * 9 == 729
    assert later == 3**6 - 3**4 == 648
    print('LITERAL-CELL BOX parameters 1..3; every reversed pair of outer words of sizes 3..5:')
    print('wall inequalities =', separated, '; literal symmetric rotations =', symmetric)
    print('additional inequalities at p+2 =', later)
    E = build_inner(1, 1, 1, 2, 3, 1)
    f, g = parent(E, (1, 2), 0), parent(E, (2, 1), 0)
    F, G = cells(f), cells(g)
    assert F != G and rotate(F) != G
    pf, pg = interval_polynomial(f), interval_polynomial(g)
    assert pf == pg
    for h in H:
        def evaluate(poly):
            ans = 0
            for mon, coeff in poly.items():
                term = coeff
                for d in mon:
                    term = term * h[d] % PRIME
                ans += term
            return ans % PRIME
        assert evaluate(pf) == value(index_board(F), h) == value(index_board(G), h)
    print('CONTROL: dropping t>=p fails on exact pre-wall nonrotation equality;', len(pf), 'monomials.')
    # At the wall the same pair is separated by literal-cell determinants.
    Fw, Gw = cells(parent(E, (1, 2), 1)), cells(parent(E, (2, 1), 1))
    assert value(index_board(Fw), H[0]) != value(index_board(Gw), H[0])
    print('CONTROL: treating outer reversal as always equal at the wall is rejected.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
