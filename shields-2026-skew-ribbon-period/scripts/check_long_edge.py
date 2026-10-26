r"""Paper section `app:coincident` (Positive coincident attachment phases).

Long edges of the band-path inverse against the contact currents.

Section: app:coincident, lem:coincident-reader ("The full finite inverse is the sum over increasing
band paths", the long-edge contraction to -[J_u + (lambda - u) K_u]).

Bands 0..L carry varying diagonal blocks M_a (rows labeled by the row residues J_a, columns by the
column residues K_a, both inside [0, u], with u in every J_a and 0 in every K_a).  The coupling from
band c to band a > c is the rank-one x_{a-c} E_{u,0}.  The script asserts, with exact rationals:

1. for a > b the inverse block X_{a,b} is rank one,
   X_{a,b} = sigma_{b,a} (M_a^{-1} e_u)(e_0^T M_b^{-1}),
   sigma_{b,a} = -sum_{b <= c < a} x_{a-c} t_{b,c}, with t the port recursion of the varying
   ratios q_a = (M_a^{-1})_{0,u};
2. with only adjacent couplings x_1 = y, t_{b,a} = (-y)^(a-b) prod_{b < c <= a} q_c;
3. for a clock lambda the long-edge contraction e_0^T M_F^{-1} E M_E^{-1} e_u with
   E_{x,y} = (x - y - lambda) h_{x-y} is q_F q_E (-[J + (lambda - u) K]), where L, R are the
   normalized coframes (L = row 0 of M_F^{-1} / q_F, R = column u of M_E^{-1} / q_E), J is the
   balanced current at the contacts (u, 0) and K the pairing; for the Hall line E_{x,y} = h_{x-y}
   it is q_F q_E K;
4. the normalized coframes are contact vectors: L M_F = e_0 / q_F with L_u = 1, and
   M_E R = e_u / q_E with R_0 = 1.
"""
import random
import sympy as sp

random.seed(7)
u = 4
LAM = sp.Rational(11, 3)


def rnd():
    return sp.Rational(random.randint(-9, 9), random.randint(1, 5))


H = {k: (rnd() if k >= 0 else 0) for k in range(-u - 1, u + 1)}
H[0] = 1


def block(J, K):
    return sp.Matrix(len(J), len(K), lambda i, j: H[J[i] - K[j]])


def sets():
    while True:
        J = sorted({u} | set(random.sample(range(u), 2)))
        K = sorted({0} | set(random.sample(range(1, u + 1), 2)))
        M = block(J, K)
        if M.det() != 0 and M.inv()[K.index(0), J.index(u)] != 0:
            return J, K, M


def check_paths(L):
    bands = [sets() for _ in range(L + 1)]
    x = {d: rnd() for d in range(1, L + 1)}
    sizes = [len(b[0]) for b in bands]
    off = [sum(sizes[:a]) for a in range(L + 1)]
    n = sum(sizes)
    A = sp.zeros(n, n)
    for a, (J, K, M) in enumerate(bands):
        A[off[a]:off[a] + sizes[a], off[a]:off[a] + sizes[a]] = M
        for c in range(a):
            A[off[a] + J.index(u), off[c] + bands[c][1].index(0)] = x[a - c]
    X = A.inv()
    q = [b[2].inv()[b[1].index(0), b[0].index(u)] for b in bands]

    def t(b, a):
        if a < b:
            return 0
        if a == b:
            return 1
        return -q[a] * sum(x[a - c] * t(b, c) for c in range(b, a))

    for a in range(L + 1):
        for b in range(a):
            Ja, Ka, Ma = bands[a]
            Jb, Kb, Mb = bands[b]
            sig = -sum(x[a - c] * t(b, c) for c in range(b, a))
            col = Ma.inv()[:, Ja.index(u)]
            row = Mb.inv()[Kb.index(0), :]
            blk = X[off[a]:off[a] + sizes[a], off[b]:off[b] + sizes[b]]
            assert blk == sig * col * row, (a, b)
            assert t(b, a) == q[a] * sig
    y = sp.Symbol('y')
    xa = {1: y}
    for d in range(2, L + 1):
        xa[d] = 0

    def ta(b, a):
        if a < b:
            return 0
        if a == b:
            return 1
        return -q[a] * sum(xa[a - c] * ta(b, c) for c in range(b, a))

    for b in range(L + 1):
        for a in range(b, L + 1):
            assert sp.expand(ta(b, a) - (-y) ** (a - b) * sp.prod(q[b + 1:a + 1])) == 0


def check_edge():
    JE, KE, ME = sets()
    JF, KF, MF = sets()
    qE = ME.inv()[KE.index(0), JE.index(u)]
    qF = MF.inv()[KF.index(0), JF.index(u)]
    Lv = {JF[i]: MF.inv()[KF.index(0), i] / qF for i in range(len(JF))}
    Rv = {KE[j]: ME.inv()[j, JE.index(u)] / qE for j in range(len(KE))}
    for k in range(len(KF)):
        v = sum(Lv[x] * H[x - KF[k]] for x in JF)
        assert v == (1 / qF if KF[k] == 0 else 0)
    for i in range(len(JE)):
        v = sum(H[JE[i] - y] * Rv[y] for y in KE)
        assert v == (1 / qE if JE[i] == u else 0)
    assert Lv[u] == 1 and Rv[0] == 1
    pair = sum(Lv[x] * H[x - y] * Rv[y] for x in JF for y in KE)
    bal = sum(Lv[x] * (u - 0 - x + y) * H[x - y] * Rv[y] for x in JF for y in KE)
    rowF = MF.inv()[KF.index(0), :]
    colE = ME.inv()[:, JE.index(u)]
    Eclk = sp.Matrix(len(JF), len(KE), lambda i, j: (JF[i] - KE[j] - LAM) * H[JF[i] - KE[j]])
    Ehall = sp.Matrix(len(JF), len(KE), lambda i, j: H[JF[i] - KE[j]])
    assert (rowF * Eclk * colE)[0, 0] == qF * qE * (-(bal + (LAM - u) * pair))
    assert (rowF * Ehall * colE)[0, 0] == qF * qE * pair


for L in (1, 2, 3, 4):
    check_paths(L)
for _ in range(6):
    check_edge()
print('rank-one inverse blocks, adjacent port paths, long-edge contraction: PASS')
