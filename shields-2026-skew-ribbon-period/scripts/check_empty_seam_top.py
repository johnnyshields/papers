r"""Paper section `app:empty` (Empty overlaps and zero span remainder).

Top band of an empty composite (`lem:empty-seams`, `eq:empty-floor`).

Labels: a connected diagram of span N has row labels X (top N) and column labels Y (bottom 0).
For an outer ribbon D (labels {m} u S_D / S_D u {0}) and an inner E of span p = A g whose core is
Row_A o V (V of span g, labels {g} u I_V / C_V u {0}), the inner E restores common betas: Z_j in
the open band (j g, (j + 1) g) and the selected seams k g, k in S_0 (0 < k < A).  The flag law
gives the labels of F = D o_empty E:

    X_F = p X_D  u  U_{c < m} (c p + I_E),   Y_F = p Y_D  u  U_{c < m} (c p + C_E).

Assign degree floor(j / g) to h_j; the top band is the board with residue inversions
zeroed (`bandTop_boardDet`, proved in Lean).  This checks, on random such data:

1. the top band component of Q_F = det(h_{x - y}) is +-(prod of the band blocks) times the
   residue-zero block, the band blocks being the boards of the open g-bands;
2. the residue-zero block is the board of R_F = D o_empty A_0 with h_k -> h_{g k}, where A_0 is
   the ribbon of A cells with seam set S_0; i.e. its labels are g X_R, g Y_R with
   X_R = A X_D u U_c (c A + S_0) u ..., the flag law at span A;
3. each residue-zero internal label of E is a common beta, and each band has as many row labels
   as column labels (the facts read off the core).
"""
import random
import sympy as sp

HV = {}


def h(k, scale=1):
    """h_k evaluated at a random integer point (h_0 = 1, h_k = 0 for k < 0); `scale` reads
    h_{scale k}."""
    if k < 0:
        return sp.Integer(0)
    if k == 0:
        return sp.Integer(1)
    return HV[scale * k]


def board(X, Y, scale=1):
    X = sorted(X, reverse=True)
    Y = sorted(Y, reverse=True)
    n = len(X)
    if n == 0:
        return sp.Integer(1)
    return sp.Matrix(n, n, lambda i, j: h(X[i] - Y[j], scale)).det(method='bareiss')


def valid(X, Y):
    """Beta lists of a connected profile: strictly decreasing, zeta_i < xi_i, and
    0 <= xi_{j+1} - zeta_j < min(r_j, r_{j+1})."""
    X = sorted(X, reverse=True)
    Y = sorted(Y, reverse=True)
    if len(X) != len(Y) or len(set(X)) != len(X) or len(set(Y)) != len(Y):
        return False
    r = [x - y for x, y in zip(X, Y)]
    if min(r) <= 0:
        return False
    for j in range(len(X) - 1):
        gj = X[j + 1] - Y[j]
        if gj < 0 or gj >= min(r[j], r[j + 1]):
            return False
    return True


def top_band(X, Y, g):
    """The top band of det(h_{x - y}) for the weight floor(k / g) of h_k, as the determinant of
    the board with every residue inversion (x mod g < y mod g) zeroed (`bandTop_boardDet`)."""
    X = sorted(X, reverse=True)
    Y = sorted(Y, reverse=True)
    n = len(X)
    M = sp.Matrix(n, n, lambda i, j: 0 if X[i] % g < Y[j] % g else h(X[i] - Y[j]))
    return M.det(method='bareiss')


def rand_inner(g):
    """A random connected V of span g: labels {g} u I, C u {0} inside (0, g)."""
    for _ in range(200):
        k = random.randint(0, g - 1)
        I = random.sample(range(1, g), k)
        C = random.sample(range(1, g), k)
        if valid([g] + I, C + [0]):
            return I, C
    return [], []


def run(seed):
    random.seed(seed)
    HV.clear()
    HV.update({k: sp.Integer(random.randint(2, 10 ** 6)) for k in range(1, 400)})
    g = random.choice([2, 3, 4])
    A = random.choice([2, 3])
    m = random.choice([2, 3])
    I_V, C_V = rand_inner(g)
    S_0 = [k for k in range(1, A) if random.random() < 0.5]
    I_E, C_E = [], []
    for j in range(A):
        free = [t for t in range(1, g) if t not in I_V and t not in C_V]
        Z = [t for t in free if random.random() < 0.4]
        I_E += [j * g + t for t in I_V + Z]
        C_E += [j * g + t for t in C_V + Z]
    I_E += [k * g for k in S_0]
    C_E += [k * g for k in S_0]
    p = A * g
    if not valid([p] + I_E, C_E + [0]):
        return None
    S_D = [k for k in range(1, m) if random.random() < 0.5]
    X_D, Y_D = [m] + S_D, S_D + [0]
    X_F = [p * x for x in X_D] + [c * p + t for c in range(m) for t in I_E]
    Y_F = [p * y for y in Y_D] + [c * p + t for c in range(m) for t in C_E]
    if not valid(X_F, Y_F):
        return None
    # 3. the core facts
    for k in range(1, A):
        assert (k * g in I_E) == (k * g in C_E)
    for b in range(A):
        assert len([x for x in I_E if b * g < x < (b + 1) * g]) == \
            len([y for y in C_E if b * g < y < (b + 1) * g])
    # 1. the top band against the blocks
    top = top_band(X_F, Y_F, g)
    X0 = [x for x in X_F if x % g == 0]
    Y0 = [y for y in Y_F if y % g == 0]
    zero_block = board(X0, Y0)
    bands = sp.Integer(1)
    for b in range(m * A):
        Xb = [x for x in X_F if b * g < x < (b + 1) * g]
        Yb = [y for y in Y_F if b * g < y < (b + 1) * g]
        assert len(Xb) == len(Yb)
        bands *= board(Xb, Yb)
    prod = bands * zero_block
    assert prod != 0 and (top == prod or top == -prod), (seed, g, A, m)
    # 2. the residue-zero block is R_F = D o A_0 at h_k -> h_{g k}
    X_R = [A * x for x in X_D] + [c * A + k for c in range(m) for k in S_0]
    Y_R = [A * y for y in Y_D] + [c * A + k for c in range(m) for k in S_0]
    assert sorted(X0) == sorted(g * x for x in X_R)
    assert sorted(Y0) == sorted(g * y for y in Y_R)
    assert board(X_R, Y_R, g) == zero_block
    return (g, A, m)


if __name__ == '__main__':
    done = 0
    for s in range(3000):
        if run(s) is not None:
            done += 1
        if done >= 60:
            break
    assert done >= 60, done
    print(f'top band of empty composite: {done} random cases pass')
