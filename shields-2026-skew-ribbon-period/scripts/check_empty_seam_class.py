r"""Paper section `app:empty` (Empty overlaps and zero span remainder).

The seam-ribbon class of `lem:empty-seams`: R_F = D o A_0 ~ R_H = C o B_0.

Ribbons are compositions.  The empty composite of ribbons is the Billera--Thomas--van
Willigenburg composition  alpha o beta = beta^{.alpha_1} . ... . beta^{.alpha_k},  where
beta^{.m} is the m-fold near concatenation and `.` is concatenation.

For coprime A > B >= 2 and mu >= 1 this enumerates every D (mu B cells), A_0 (A cells),
C (mu A cells), B_0 (B cells) with s_{D o A_0} = s_{C o B_0}, and checks the conclusion of the
seam step and the outer factorization `eq:empty-outer-factors` (D = T o Row_B, C = T' o Row_A with
s_T = s_T'): in one orientation (rows, or columns of both = the conjugate compositions) every part
of D is divisible by B and every part of C by A, and A_0, B_0 are lines in that orientation.
"""
import itertools
import random
import sympy as sp

random.seed(7)
HV = {k: random.randint(2, 10 ** 9) for k in range(1, 200)}


def h(k):
    return 0 if k < 0 else (1 if k == 0 else HV[k])


def compositions(n):
    for cuts in itertools.product([0, 1], repeat=n - 1):
        out, cur = [], 1
        for c in cuts:
            if c:
                out.append(cur)
                cur = 1
            else:
                cur += 1
        out.append(cur)
        yield tuple(out)


def near(a, b):
    return a[:-1] + (a[-1] + b[0],) + b[1:]


def npow(b, m):
    out = b
    for _ in range(m - 1):
        out = near(out, b)
    return out


def comp(alpha, beta):
    out = ()
    for a in alpha:
        out += npow(beta, a)
    return out


def conj(alpha):
    """The transpose ribbon: cut set complemented and reversed."""
    n = sum(alpha)
    cuts = set(itertools.accumulate(alpha[:-1]))
    tc = sorted(n - c for c in range(1, n) if c not in cuts)
    out, prev = [], 0
    for c in tc + [n]:
        out.append(c - prev)
        prev = c
    return tuple(out)


def ribbon_schur(alpha):
    """Jacobi--Trudi value of the ribbon with rows alpha (top to bottom)."""
    k = len(alpha)
    # beta lists: zeta_i = sum_{j > i} alpha_j, xi_i = zeta_i + alpha_i (overlaps one)
    zeta = [sum(alpha[i + 1:]) for i in range(k)]
    xi = [zeta[i] + alpha[i] for i in range(k)]
    return sp.Matrix(k, k, lambda i, j: h(xi[i] - zeta[j])).det(method='bareiss')


def is_line(a):
    return len(a) == 1


def ok(D, A0, C, B0, A, B):
    if all(d % B == 0 for d in D) and all(c % A == 0 for c in C) and is_line(A0) and is_line(B0):
        return True
    Dt, Ct = conj(D), conj(C)
    return (all(d % B == 0 for d in Dt) and all(c % A == 0 for c in Ct)
            and len(conj(A0)) == 1 and len(conj(B0)) == 1)


def outer_factors(D, C, A, B):
    """`eq:empty-outer-factors`: in the orientation of the seam step, D = T o Row_B and
    C = T' o Row_A with T, T' ribbons of mu cells and s_T = s_T'.  Returns None when no
    orientation gives them."""
    for Dp, Cp in ((D, C), (conj(D), conj(C))):
        if all(d % B == 0 for d in Dp) and all(c % A == 0 for c in Cp):
            T = tuple(d // B for d in Dp)
            Tp = tuple(c // A for c in Cp)
            if comp(T, (B,)) == Dp and comp(Tp, (A,)) == Cp and ribbon_schur(T) == ribbon_schur(Tp):
                return T, Tp
    return None


def run(A, B, mu):
    left = {}
    for D in compositions(mu * B):
        for A0 in compositions(A):
            R = comp(D, A0)
            left.setdefault(ribbon_schur(R), []).append((D, A0, R))
    bad, hits = [], 0
    for C in compositions(mu * A):
        for B0 in compositions(B):
            R = comp(C, B0)
            v = ribbon_schur(R)
            for (D, A0, RF) in left.get(v, []):
                if mu * B < 2 or mu * A < 2:
                    continue
                hits += 1
                if not ok(D, A0, C, B0, A, B) or outer_factors(D, C, A, B) is None:
                    bad.append((D, A0, C, B0, RF, R))
    return hits, bad


if __name__ == '__main__':
    for (A, B, mu) in [(3, 2, 1), (3, 2, 2), (5, 2, 1), (4, 3, 1), (5, 3, 1), (3, 2, 3), (5, 2, 2)]:
        hits, bad = run(A, B, mu)
        print(A, B, mu, 'equal pairs', hits, 'violations', len(bad))
        for b in bad[:6]:
            print('   D', b[0], 'A0', b[1], 'C', b[2], 'B0', b[3], 'R_F', b[4], 'R_H', b[5])
        assert hits > 0, (A, B, mu)
        assert not bad, (A, B, mu)


def run_multisets(A, B, mu):
    """Same conclusion from equal row and column multisets alone (no Schur equality)."""
    key = lambda R: (tuple(sorted(R)), tuple(sorted(conj(R))))
    left = {}
    for D in compositions(mu * B):
        for A0 in compositions(A):
            R = comp(D, A0)
            left.setdefault(key(R), []).append((D, A0, R))
    bad, hits = [], 0
    for C in compositions(mu * A):
        for B0 in compositions(B):
            R = comp(C, B0)
            for (D, A0, RF) in left.get(key(R), []):
                hits += 1
                if not ok(D, A0, C, B0, A, B):
                    bad.append((D, A0, C, B0, RF, R))
    return hits, bad


if __name__ == '__main__':
    for (A, B, mu) in [(3, 2, 1), (3, 2, 2), (5, 2, 1), (4, 3, 1), (5, 3, 1), (3, 2, 3), (5, 2, 2)]:
        hits, bad = run_multisets(A, B, mu)
        print('multisets', A, B, mu, 'pairs', hits, 'violations', len(bad))
        for b in bad[:4]:
            print('   D', b[0], 'A0', b[1], 'C', b[2], 'B0', b[3], 'R_F', b[4], 'R_H', b[5])
        assert hits > 0, (A, B, mu)
        assert not bad, (A, B, mu)
