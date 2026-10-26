r"""Paper section `app:coincident` (Positive coincident attachment phases).

Marked-band determinant against the weighted seam polynomial.

Section: app:coincident, "The whole marked-band determinant" (eq:marked-floor,
eq:weighted-seam-ribbon).

For a g-periodic ordinary mark with marked residues J (rows) and K (columns) and phase tau, the
marked matrix of the coincident source of L cells has rows {L g + tau} u (i g + J) and columns
{tau} u (i g + K), i = 0..L, entry h_{row - col}, zeroed when the row residue is below the column
residue (the degree-L top component).  All high variables are zero except the ports
x_m = h_{m g + u}; every low variable is a symbol.  The script asserts, for each L, that the
determinant equals E * s^(L-1) * W_L(x; q), where s = det (h_{j-k}) over J x K is the band block,
q = (s^-1)_{0,u} = d s / d h_u / s, and E is the end factor read off at L = 1.
"""
import itertools
import sympy as sp

g, u = 5, 3
TESTS = [(2, [1, 3], [0, 1]), (1, [3], [0]), (2, [3, 1], [0, 2]), (1, [0, 3], [0, 2])]


def seam(x, q, L):
    tot = 0
    for r in range(L):
        for T in itertools.combinations(range(1, L), r):
            cuts = [0, *T, L]
            term = (-1) ** len(T)
            for t in T:
                term *= q
            for a, b in zip(cuts, cuts[1:]):
                term *= x[b - a]
            tot += term
    return tot


def run(tau, J, K, L, h):
    rows = [L * g + tau] + [i * g + j for i in range(L + 1) for j in J]
    cols = [tau] + [i * g + k for i in range(L + 1) for k in K]
    return sp.Matrix(len(rows), len(cols),
                     lambda a, b: 0 if rows[a] % g < cols[b] % g else h(rows[a] - cols[b])).det()


for tau, J, K in TESTS:
    xs = sp.symbols('x0:7')
    lo = {r: sp.Symbol('h%d' % r) for r in range(1, g)}

    def h(j):
        if j < 0:
            return 0
        if j == 0:
            return 1
        if j < g:
            return lo[j]
        return xs[j // g] if j % g == u else 0
    sM = sp.Matrix(len(J), len(K), lambda a, b: h(J[a] - K[b]) if J[a] % g >= K[b] % g else 0)
    s = sp.expand(sM.det())
    q = sp.simplify(sp.diff(s, lo[u]) / s)  # h_u = h3 is lo[u]
    assert u in J and 0 in K
    d1 = run(tau, J, K, 1, h)
    E = sp.simplify(d1 / xs[1])
    for L in (2, 3, 4):
        d = run(tau, J, K, L, h)
        W = seam({m: xs[m] for m in range(1, L + 1)}, q, L)
        diff = sp.simplify(d - E * s ** (L - 1) * W)
        print(tau, J, K, L, 'OK' if diff == 0 else ('MISMATCH', sp.factor(d), sp.factor(E * s ** (L - 1) * W)))
