"""Non-vacuity witness for the one-sided containment inside the dilation theorem.

Paper section `sec:dilation` (Integral dilation).

thm:dilation states an EQUALITY under a cofactor-independence hypothesis.  Only one
inclusion consumes that hypothesis:

    iota_t K(C) (+) A_off(tC)  SUBSET  K(tC)        -- no cofactor hypothesis
    K(tC)  SUBSET  iota_t K(C) (+) A_off(tC)        -- consumes independence

This script exhibits a core OUTSIDE the hypothesis where the free inclusion still has
content, which is what a widening owes: a witness in the newly admitted part of the range.

The witness is the paper's own symmetric control C = (A,B) with A=(4,3), B=(1,0):
symmetric, so its cofactors are dependent by the symmetric clause of
thm:cofactor-relations, so thm:dilation does not apply to it at all.

Checked here:
  (1) C is symmetric and its signed cofactors are dependent (rank 3 of 4).
  (2) K(C) = 0, so the inherited summand is zero and A_off carries the whole RHS.
  (3) At t=2 the arithmetic space is ZERO, so the containment there is vacuous.
      This is why t=2 is a control and not the witness.
  (4) At t=3 the arithmetic space has dimension 1, the containment HOLDS, and the
      reverse inclusion FAILS -- dim K(3C) is strictly larger.  So on this core the
      free half is true and non-trivial while the equality is false.
  (5) Units are computed by two independent routes and compared exactly: cofactor
      expansion, and the restored (k+1)x(k+1) determinant read by ordinary degree.
      For a single restored position the degree-(k+1) component is -eps*U_z and the
      degree-k component is eps*s_C, so both halves of the first-components identity
      are checked rather than one.

This is a finite witness and corroborates only.  It establishes that the containment is
non-vacuous outside the hypothesis and that the equality is false there; it proves no
universal statement, and no count below is a premise for anything in the paper.
"""

from fractions import Fraction
from itertools import permutations

# ------------------------------------------------------------------ polynomials


def perm_sign(p):
    seen = [False] * len(p)
    s = 1
    for i in range(len(p)):
        if seen[i]:
            continue
        j, ln = i, 0
        while not seen[j]:
            seen[j] = True
            j = p[j]
            ln += 1
        if ln % 2 == 0:
            s = -s
    return s


def det_poly(idx):
    """Determinant of a matrix of h-indices as {sorted-monomial: coeff}. h_0=1, h_{<0}=0."""
    m = len(idx)
    if m == 0:
        return {(): Fraction(1)}
    out = {}
    for p in permutations(range(m)):
        mono, ok = [], True
        for r in range(m):
            e = idx[r][p[r]]
            if e < 0:
                ok = False
                break
            if e > 0:
                mono.append(e)
        if not ok:
            continue
        k = tuple(sorted(mono))
        out[k] = out.get(k, Fraction(0)) + perm_sign(p)
    return {k: v for k, v in out.items() if v}


def mul_h(poly, *idxs):
    """Multiply a polynomial by h_{i1} h_{i2} ...; a nonpositive index is handled."""
    out = {}
    extra = [i for i in idxs if i > 0]
    if any(i < 0 for i in idxs):
        return {}
    for mono, c in poly.items():
        k = tuple(sorted(list(mono) + extra))
        out[k] = out.get(k, Fraction(0)) + c
    return {k: v for k, v in out.items() if v}


def add_into(acc, poly):
    for k, v in poly.items():
        acc[k] = acc.get(k, Fraction(0)) + v
        if acc[k] == 0:
            del acc[k]


# ------------------------------------------------------------------ cores


def cofactors(A, B):
    idx = [[A[i] - B[j] for j in range(len(B))] for i in range(len(A))]
    n = len(A)
    D = {}
    for i in range(n):
        for j in range(n):
            minor = [[idx[r][c] for c in range(n) if c != j] for r in range(n) if r != i]
            s = Fraction((-1) ** (i + j))
            D[(i, j)] = {k: s * v for k, v in det_poly(minor).items()}
    return D


def is_symmetric(A, B):
    N, n = A[0], len(A)
    return all(A[i] + B[n - 1 - i] == N for i in range(n))


def omega(A, B):
    N = A[0]
    return [z for z in range(1, N) if z not in set(A) | set(B)]


def modulus(A, B):
    from math import gcd
    N = A[0]
    g = 0
    for a in A:
        g = gcd(g, N - a)
    for b in B:
        g = gcd(g, b)
    return g


def unit(A, B, z, D):
    """U_z^C = sum over a_i > z > b_j of D_ij h_{a_i-z} h_{z-b_j}."""
    acc = {}
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            if a > z > b:
                add_into(acc, mul_h(D[(i, j)], a - z, z - b))
    return acc


def rank_and_nullity(polys):
    """Rank of the span, and the nullspace of lambda -> sum lambda_z U_z."""
    monos = sorted({m for p in polys for m in p})
    cols = len(polys)
    rows = [[p.get(m, Fraction(0)) for p in polys] for m in monos]
    # gaussian elimination, tracking pivot columns
    r, piv = 0, []
    rows = [row[:] for row in rows]
    for c in range(cols):
        sel = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                sel = i
                break
        if sel is None:
            continue
        rows[r], rows[sel] = rows[sel], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
        if r == len(rows):
            break
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for fc in free:
        v = [Fraction(0)] * cols
        v[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            v[pc] = -rows[i][fc]
        basis.append(v)
    return r, basis


def a_off_basis(A, B, t):
    """Restrictions to Omega_{tC} of phi on Z/(tg)Z with phi(r)+phi(tN-r)=0, phi(r)=0 if t|r."""
    tA, tB = tuple(t * a for a in A), tuple(t * b for b in B)
    g, N = modulus(A, B), A[0]
    tg, tN = t * g, t * N
    om = omega(tA, tB)
    # solve for phi on Z/tg Z
    cols = tg
    eqs = []
    for r in range(tg):
        e = [Fraction(0)] * cols
        e[r % tg] += 1
        e[(tN - r) % tg] += 1
        eqs.append(e)
        if r % t == 0:
            f = [Fraction(0)] * cols
            f[r % tg] = Fraction(1)
            eqs.append(f)
    # nullspace of eqs
    rows = [e[:] for e in eqs]
    rr, piv = 0, []
    for c in range(cols):
        sel = None
        for i in range(rr, len(rows)):
            if rows[i][c] != 0:
                sel = i
                break
        if sel is None:
            continue
        rows[rr], rows[sel] = rows[sel], rows[rr]
        pv = rows[rr][c]
        rows[rr] = [x / pv for x in rows[rr]]
        for i in range(len(rows)):
            if i != rr and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rr])]
        piv.append(c)
        rr += 1
    free = [c for c in range(cols) if c not in piv]
    out = []
    for fc in free:
        phi = [Fraction(0)] * cols
        phi[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            phi[pc] = -rows[i][fc]
        out.append([phi[z % tg] for z in om])
    return om, out


def in_span(vec, basis):
    if not basis:
        return all(x == 0 for x in vec)
    rows = [b[:] for b in basis] + [vec[:]]
    r0, _ = _rank(rows[:-1]), None
    r1 = _rank(rows)
    return r1 == r0


def _rank(rows):
    rows = [r[:] for r in rows]
    if not rows:
        return 0
    cols = len(rows[0])
    r = 0
    for c in range(cols):
        sel = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                sel = i
                break
        if sel is None:
            continue
        rows[r], rows[sel] = rows[sel], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def restored_determinant(A, B, z):
    """Determinant of the diagram with z restored to both lists, and the sign eps.

    eps is the product of the permutation signs for regrouping X as (A,z) and Y as (B,z):
    moving z from its position to the end is a cycle, whose sign is (-1)^(len-1-pos).
    """
    X = sorted(list(A) + [z], reverse=True)
    Y = sorted(list(B) + [z], reverse=True)
    eps = 1
    for L in (X, Y):
        p = L.index(z)
        eps *= (-1) ** (len(L) - 1 - p)
    idx = [[X[i] - Y[j] for j in range(len(Y))] for i in range(len(X))]
    return det_poly(idx), eps


def by_ordinary_degree(poly, d):
    """The component of ordinary degree d -- monomials with exactly d positive factors."""
    return {m: c for m, c in poly.items() if len(m) == d}


def neg(poly):
    return {m: -c for m, c in poly.items()}


def edge_quadratics_vanish(A, B, t, phi_on_omega, om):
    """Each positive-edge quadratic is killed individually, not merely the unit sum.

    This is strictly stronger than the sum vanishing: a sum can vanish by cancellation
    among the cofactors even when an individual edge does not, and the distinction is
    exactly the one the paper draws after its endpoint-normalization lemma.
    """
    tA, tB = tuple(t * a for a in A), tuple(t * b for b in B)
    lam = dict(zip(om, phi_on_omega))
    bad = []
    for a in tA:
        for b in tB:
            if a <= b:
                continue
            # Q_lambda(b,a) = sum_{b<z<a} lambda_z h_{a-z} h_{z-b}; as a polynomial it
            # vanishes iff the coefficient of each distinct monomial h_{a-z}h_{z-b} is 0.
            acc = {}
            for z in range(b + 1, a):
                c = lam.get(z, Fraction(0))
                if c:
                    k = tuple(sorted((a - z, z - b)))
                    acc[k] = acc.get(k, Fraction(0)) + c
            acc = {k: v for k, v in acc.items() if v}
            if acc:
                bad.append((b, a, acc))
    return bad


def fmt(poly):
    if not poly:
        return "0"
    parts = []
    for m, c in sorted(poly.items()):
        s = "*".join(f"h{i}" for i in m) or "1"
        parts.append(("+ " if c > 0 else "- ") + (f"{abs(c)}*" if abs(c) != 1 else "") + s)
    return " ".join(parts).lstrip("+ ").strip()


# ------------------------------------------------------------------ the witness


# (dim A_off, dim K(tC)) required at each t.  Asserted, not printed: a witness that
# silently became vacuous would otherwise still reach ALL PASS.
EXPECT = {2: (0, 2), 3: (1, 4)}


def main():
    A, B = (4, 3), (1, 0)
    n = len(A)
    print(f"WITNESS CORE  A={A}  B={B}")
    print(f"  symmetric (a_i + b_(n+1-i) = N):  {is_symmetric(A, B)}")
    D = cofactors(A, B)
    print(f"  M_C indices: {[[A[i]-B[j] for j in range(n)] for i in range(n)]}")
    for (i, j), p in sorted(D.items()):
        print(f"    D_{i+1}{j+1} = {fmt(p)}")
    rk, _ = rank_and_nullity([D[(i, j)] for i in range(n) for j in range(n)])
    print(f"  cofactor rank {rk} of {n*n}  ->  cofactors DEPENDENT: {rk < n*n}")
    assert is_symmetric(A, B) and rk == 3, "witness core changed"
    print("  => thm:dilation does NOT apply to this core.  It is outside the hypothesis.")

    om = omega(A, B)
    g = modulus(A, B)
    print(f"\n  Omega_C = {om}   g(C) = {g}   N = {A[0]}")
    U = {z: unit(A, B, z, D) for z in om}
    for z in om:
        print(f"    U_{z} = {fmt(U[z])}")
    _, base_null = rank_and_nullity([U[z] for z in om])
    print(f"  dim K(C) = {len(base_null)}   (inherited summand is zero)")
    assert len(base_null) == 0

    # second, independent route to the same units: restore z and read the determinant
    # by ordinary degree.  degree k+1 gives -eps*U_z, degree k gives eps*s_C.
    print("\n  SECOND ROUTE -- restored determinant, read by ordinary degree:")
    sC = det_poly([[A[i] - B[j] for j in range(n)] for i in range(n)])
    for z in om:
        full, eps = restored_determinant(A, B, z)
        top = by_ordinary_degree(full, n + 1)
        low = by_ordinary_degree(full, n)
        want_top = neg(U[z]) if eps == 1 else U[z]
        want_low = sC if eps == 1 else neg(sC)
        print(f"    z={z}  eps={eps:+d}")
        print(f"      degree {n+1}: {fmt(top)}")
        print(f"      cofactor route gives -eps*U_{z} = {fmt(want_top)}")
        print(f"      degree {n}:   {fmt(low)}   vs  eps*s_C = {fmt(want_low)}")
        assert top == want_top, f"two routes disagree on U_{z}"
        assert low == want_low, f"two routes disagree on s_C at z={z}"
    print("    both routes agree exactly, on both degree components")

    for t in (2, 3):
        print(f"\n=== t = {t} ===")
        tA, tB = tuple(t * a for a in A), tuple(t * b for b in B)
        tom, aoff = a_off_basis(A, B, t)
        Dt = cofactors(tA, tB)
        Ut = {z: unit(tA, tB, z, Dt) for z in tom}
        _, kt = rank_and_nullity([Ut[z] for z in tom])
        rhs = len(base_null) + len(aoff)
        print(f"  Omega_(tC) = {tuple(tom)}")
        print(f"  dim A_off({t}C) = {len(aoff)}")
        if aoff:
            print(f"    basis    = {tuple(int(x) for x in aoff[0])}")
        print(f"  dim K({t}C)      = {len(kt)}")
        print(f"  dim RHS         = {rhs}  (iota_t K(C) (+) A_off)")

        # the free containment: every A_off vector really is in K(tC)
        ok = True
        for v in aoff:
            assert any(x != 0 for x in v), "arithmetic basis vector is zero"
            acc = {}
            for c, z in zip(v, tom):
                if c:
                    for k, val in Ut[z].items():
                        acc[k] = acc.get(k, Fraction(0)) + c * val
            acc = {k: x for k, x in acc.items() if x}
            if acc:
                ok = False
                print(f"    *** A_off vector NOT in K({t}C): residual {fmt(acc)}")
            # strictly stronger than the sum vanishing
            bad = edge_quadratics_vanish(A, B, t, v, tom)
            assert not bad, f"edge quadratic not killed at {bad[:1]}"
        print(f"  CONTAINMENT  RHS subset K({t}C): {ok}")
        if aoff:
            print(f"  each positive-edge quadratic killed individually: True")
        assert ok, "the free containment failed -- this refutes the widening"
        assert (len(aoff), len(kt)) == EXPECT[t], (
            f"t={t}: got A_off {len(aoff)}, nullity {len(kt)}; expected {EXPECT[t]}")

        if rhs < len(kt):
            print(f"  EQUALITY FAILS: K({t}C) is strictly larger ({len(kt)} > {rhs}).")
        elif rhs == len(kt):
            print(f"  equality holds here.")
        if len(aoff) == 0:
            print("  NOTE: A_off is zero, so the containment is VACUOUS at this t.")
            print("        This is the control, not the witness.")
        else:
            print("  NON-VACUOUS: the containment carries content outside the hypothesis.")

    # the control's units, by name
    tA2, tB2 = tuple(2 * a for a in A), tuple(2 * b for b in B)
    D2 = cofactors(tA2, tB2)
    u1, u7 = unit(tA2, tB2, 1, D2), unit(tA2, tB2, 7, D2)
    # built literally rather than as a determinant, which is easy to mis-transpose
    want = {tuple(sorted((1, 5, 6))): Fraction(1),
            tuple(sorted((1, 4, 7))): Fraction(-1)}
    print(f"\n  control units on 2C:  U_1 = {fmt(u1)}")
    print(f"                        U_7 = {fmt(u7)}")
    assert u1 == u7, "U_1 and U_7 differ on 2C"
    assert u1 == want, f"U_1 is not h1*(h5*h6-h4*h7): {fmt(u1)}"
    print("    U_1 = U_7 = h1*(h5*h6 - h4*h7), as expected")

    print("\nA finite witness: corroboration only, and no count above is a premise.")
    print("\nALL PASS")


if __name__ == "__main__":
    main()
