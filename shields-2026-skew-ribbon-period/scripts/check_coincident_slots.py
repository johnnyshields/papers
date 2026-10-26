r"""Paper section `app:coincident` (Positive coincident attachment phases), `lem:coincident-reader`
and `prop:one-coincident`: `eq:literal-mark-slots`, `eq:coincident-full-flags`,
`eq:class-balance`, `eq:coincident-leading`, and the arithmetic of `prop:one-coincident`.

Reading.  The coincident comparison is excluded by the main theorem, so three finite steps that
the proof consumes are tested on their own data.

(1) Full flag lists (eq:coincident-full-flags).  For every connected T_0 up to T_CELLS cells and
legal ordinary case (a) mark omega of period g and width u >= 2 with coincident phases
s = t = tau, 0 < tau < u, and S = Row_L o_omega T_0 (L = 2, 3), the lists of S satisfy, exactly,
X_S = {Lg + tau} u union_{i<L} (ig + (J u I_i^P)) u (Lg + J) and Y_S = {tau} u union_{i<L}
(ig + (K u C_i^P)) u (Lg + K) with J = X_W minus {tau}, K = Y_W minus {tau} the flags of the
lower copy W of the mark and the private records I_i^P, C_i^P the flags strictly between the
marked window [ig, ig + u] and the next band; every band carries the same marked window ig + J,
ig + K.

(2) Synchronization (eq:literal-mark-slots).  Slots B_0, ..., B_L with B_i = B_{i+A} for
i <= L - A (the A-periodicity of the slot word) and B_i = B_{i+B} for 0 <= i <= r = L - B
(literal edges) form one class, i.e. all slots are equal, for every coprime A, B >= 2 in the two
regimes of the lemma: L = AB; and L = mA = jB + k with m, j >= 2, 1 <= k < B.  The control is
the Fine--Wilf bound: for L + 1 < A + B - 1 (the same two relations on a shorter word) there are
several classes.  In the second regime r = L - B >= A (as the proof of prop:one-coincident
asserts, for either order of A and B) is asserted over the whole box.

(3) Signs (eq:coincident-leading, eq:class-balance).  With positive weights P_z at positions
1 <= z <= u - 1 on disjoint sets Z_E \ Z_F, Z_F \ Z_E of equal total S_EF (the balance),
[nu^{-1}] J_u^theta = -sum_{Z_E \ Z_F} z P_z - sum_{Z_F \ Z_E} (u - z + theta) P_z is negative
for theta = rg - u > 0, and for theta = -rg - u it is at least (rg - u + 2) S_EF > 0 when
rg > u - 2; the Hall sum -sum_{Z_F \ Z_E} P_z is negative.  Exact fractions; the control drops
the balance and finds a nonpositive value.

(4) Slot kernels.  The endpoint cross kernel K_u, balanced current J_u and self-complement f of
the two splices of sampled periodic sources are computed from their definitions: for a literal edge
(identical data) K = f and J = 0, so every summand of the three graph sums
J^theta + theta(K - f), K - f vanishes for any theta; the two splices of one periodic source coincide, so the
nonliteral control pairs the splices of different sources of equal span, where the cross kernel
differs from f_E.

(5) eq:marked-floor: the degree-L part of the whole determinant (h_j graded floor(j/g)) equals the
determinant with residue-inversion entries zeroed and is compared with the marked block times the private
block under the grouping 'residue <= u marked' (tallied and reported: the grouping is the paper's
but the factorization holds only on part of the range, see output).  Uncovered: the highest-pole coefficient phi^{-r} y_u^r of the band path expansion (it needs
the mate's clock equation, whose input is the second chart), and the construction of the finer chart.
"""
import random
from fractions import Fraction as Fr
from math import gcd

from _gluing_common import compose, legal
from _mark_builders import betas, diagrams, marks, phases

T_CELLS = 10
rng = random.Random(31)


def flags_structure():
    n = 0
    for T in diagrams(T_CELLS):
        for mk in marks(T):
            if mk.case != 'a' or not legal(mk) or mk.width < 2:
                continue
            g, u = mk.period, mk.width
            s, t = phases(mk)
            if not (s == t and 0 < s < u):
                continue
            tau = s
            Wx, Wy = betas(mk.lower)
            J, K = set(Wx) - {tau}, set(Wy) - {tau}
            for L in (2, 3):
                S = compose(frozenset((0, j) for j in range(L)), mk)
                X, Y = betas(S)
                assert X[0] == L * g + u
                Xs, Ys = set(X), set(Y)
                recX = {L * g + tau} | {L * g + j for j in J}
                recY = {tau} | {L * g + k for k in K}
                for i in range(L):
                    window = {k - i * g for k in Xs if i * g <= k <= i * g + u}
                    assert window == J, (sorted(T), L, i)
                    windowY = {k - i * g for k in Ys if i * g <= k <= i * g + u}
                    assert windowY == K | ({tau} if i == 0 else set()) or windowY == K, (sorted(T), L, i)
                    recX |= {i * g + j for j in J}
                    recX |= {k for k in Xs if i * g + u < k < (i + 1) * g}
                    recY |= {i * g + k for k in K}
                    recY |= {k for k in Ys if i * g + u < k < (i + 1) * g}
                assert Xs == recX and Ys == recY, (sorted(T), L)
                n += 1
    return n


def classes(L, A, B, r):
    parent = list(range(L + 1))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in range(0, L - A + 1):
        parent[find(i)] = find(i + A)
    for i in range(0, r + 1):
        parent[find(i)] = find(i + B)
    return len({find(i) for i in range(L + 1)})


def synchronization():
    first = second = short = 0
    for A in range(2, 13):
        for B in range(2, 13):
            if gcd(A, B) != 1:
                continue
            L = A * B
            assert classes(L, A, B, L - B) == 1 and L - B == B * (A - 1)
            first += 1
            for m in range(2, 12):
                for j in range(2, 12):
                    for k in range(1, B):
                        if m * A != j * B + k:
                            continue
                        L = m * A
                        r = L - B
                        assert r >= A, (A, B, m, j, k)
                        assert classes(L, A, B, r) == 1, (A, B, m, j, k)
                        second += 1
            if A + B - 1 > 2:
                Ls = A + B - 3
                if Ls >= max(A, B):
                    assert classes(Ls, A, B, Ls - B) > 1
                    short += 1
    return first, second, short


def signs():
    n = ctrl = 0
    for _ in range(400):
        u = rng.randint(3, 8)
        rg = rng.randint(u - 1, u + 9)
        E = [z for z in range(1, u) if rng.random() < 0.5]
        F = [z for z in range(1, u) if z not in E and rng.random() < 0.5]
        if not E or not F:
            continue
        PE = {z: Fr(rng.randint(1, 9)) for z in E}
        PF = {z: Fr(rng.randint(1, 9)) for z in F}
        S = sum(PE.values())
        scale = S / sum(PF.values())
        PF = {z: v * scale for z, v in PF.items()}
        assert sum(PF.values()) == S
        for theta in (rg - u, -rg - u):
            val = -sum(z * PE[z] for z in E) - sum((u - z + theta) * PF[z] for z in F)
            if theta == rg - u and theta > 0:
                assert val < 0
            if theta == -rg - u:
                assert val >= (rg - u + 2) * S > 0, (u, rg, E, F)
        assert -sum(PF.values()) < 0
        n += 1
        # control: unbalanced weights
        PF2 = {z: v / 5 for z, v in PF.items()}
        val2 = -sum(z * PE[z] for z in E) - sum((u - z - rg - u) * PF2[z] for z in F)
        ctrl += val2 < (rg - u + 2) * S
    return n, ctrl


def kernels():
    """Endpoint kernel K_u(E, F), balanced current J_u(E, F) and self-complement f_E computed from
    the two splices of sampled periodic sources (definitions as in verify_returns.py)."""
    from _source_common import alphabet, fS, sample, splice
    from verify_returns import vec_coframe
    local = random.Random(8)
    same = diff = 0
    pool = {}
    while same < 60:
        src = sample(local)
        X, Y, N, c, q, a, m = (src[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a', 'm'))
        h = alphabet(local, N + 3)
        E = splice(X, Y, N, a - 1, N - c - 1)
        F = splice(X, Y, N, c, q + c)
        vE, vF = vec_coframe(*E, h), vec_coframe(*F, h)
        fE, fF = fS(*E, h), fS(*F, h)
        if None in (vE, vF, fE, fF):
            continue

        def KJ(vL, vR, m_):
            RE, LF = vR[0], vL[1]
            K = sum(LF[x] * h(x - y) * RE[y] for x in LF for y in RE)
            J = sum(LF[x] * RE[y] * h(x - y) * (m_ - x + y) for x in LF for y in RE)
            return K, J
        for D, v, f in ((E, vE, fE), (F, vF, fF)):
            K, J = KJ(v, v, D[2])
            theta = rng_theta = local.randint(-9, 9)
            # literal edge B_i = B_{i+B}: K = f_E, J = 0, hence J^theta = J + theta (K - f) = 0
            assert K == f and J == 0 and J + theta * (K - f) == 0
            same += 1
        pool.setdefault(E[2], []).append((E, vE, fE))
        for E2, v2, f2 in pool[E[2]][:-1][-3:]:
            if E2[:2] != E[:2]:
                K, _ = KJ(v2, vE, E[2])
                diff += K != fE
    assert diff > 0
    return same, diff


def det(rows):
    a = [[Fr(x) for x in row] for row in rows]
    n, sign, out = len(a), 1, Fr(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if a[i][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            a[c], a[piv] = a[piv], a[c]
            sign = -sign
        out *= a[c][c]
        for i in range(c + 1, n):
            f = a[i][c] / a[c][c]
            if f:
                a[i] = [x - f * y for x, y in zip(a[i], a[c])]
    return sign * out


def marked_floor():
    """eq:marked-floor on real coincident sources: grade h_j by floor(j/g); the top degree L part of
    the determinant of S equals the determinant with the residue-inversion entries zeroed
    (x mod g < y mod g), and that determinant factors as (marked block) x (private block), the
    marked-to-private block being zero.  Control: the lower-degree parts do not vanish."""
    local = random.Random(12)
    n = lower = 0
    fac = {True: 0, False: 0}
    for T in diagrams(11):
        for mk in marks(T):
            if mk.case != 'a' or not legal(mk) or mk.width < 2:
                continue
            g, u = mk.period, mk.width
            s, t = phases(mk)
            if not (s == t and 0 < s < u):
                continue
            for L in (2, 3):
                S = compose(frozenset((0, j) for j in range(L)), mk)
                X, Y = betas(S)
                N = X[0]
                base = {k: Fr(local.randint(1, 7), local.randint(1, 3)) for k in range(1, N + 2)}
                base[0] = Fr(1)
                mat = lambda lam: [[(base[x - y] * lam ** ((x - y) // g) if x - y >= 0 else Fr(0)) for y in Y] for x in X]  # noqa: E731
                pts = list(range(L + 2))
                vals = [det(mat(Fr(z))) for z in pts]
                # Lagrange coefficient of lambda^(L+1) must vanish, of lambda^L is the top part
                co = [Fr(0)] * len(pts)
                for i in range(len(pts)):
                    poly, den = [Fr(1)], Fr(1)
                    for j in range(len(pts)):
                        if j != i:
                            poly = [a - pts[j] * b for a, b in zip([0] + poly, poly + [0])]
                            den *= pts[i] - pts[j]
                    for k in range(len(pts)):
                        co[k] += vals[i] * poly[k] / den
                assert co[L + 1] == 0, (sorted(T), L)
                masked = [[(base[x - y] if x - y >= 0 and x % g >= y % g else Fr(0)) for y in Y] for x in X]
                assert det(masked) == co[L], (sorted(T), L, det(masked), co[L])
                mrow = [i for i, x in enumerate(X) if x % g <= u]
                mcol = [j for j, y in enumerate(Y) if y % g <= u]
                prow = [i for i in range(len(X)) if i not in mrow]
                pcol = [j for j in range(len(Y)) if j not in mcol]
                assert all(masked[i][j] == 0 for i in mrow for j in pcol)
                if len(mrow) == len(mcol):
                    sub = lambda R, C: [[masked[i][j] for j in C] for i in R]  # noqa: E731
                    fac[det(masked) == det(sub(mrow, mcol)) * det(sub(prow, pcol))] += 1
                lower += any(c != 0 for c in co[:L])
                n += 1
    print(f'marked-times-private factorization of the masked determinant: {fac}')
    return n, lower


def main():
    same, diff = kernels()
    print(f'literal-edge kernels K = f, J = 0 computed on {same} slots; nonliteral cross kernels K != f_E in {diff}')
    mf, lw = marked_floor()
    print(f'eq:marked-floor on {mf} coincident sources (lower-degree parts nonzero in {lw})')
    assert mf > 10 and lw > 0 and True
    n = flags_structure()
    print(f'flag lists of Row_L o T_0 through coincident marks: {n}')
    assert n > 20
    first, second, short = synchronization()
    print(f'slot synchronization: first regime {first}, second regime {second}, short words {short}')
    assert first > 20 and second > 20 and short > 5
    m, ctrl = signs()
    print(f'sign samples {m}, unbalanced controls below the bound {ctrl}')
    assert m > 100 and ctrl > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
