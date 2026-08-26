"""Two questions, settled in exact arithmetic before the Lean route is chosen.

(1) Is the existence half GENERAL?  For arbitrary Q, B and r >= 1 with
    Q.coeff 0 != 0, does the recursively defined

        F_M = Q_0^{-1} (B_M - sum_{i<M} d_{M-i} F_i),   d_j = Q_j + [j=r] z

    satisfy the convolution system  sum_{j=0}^{M} d_j F_{M-j} = B_M ?
    Tested on several unrelated (Q, B, r), symbolically in z.

(2) Do the two thresholds compose at the panel?  `panelReductionCoeff` gives
    P_m = F_{m+2} only for m >= 4.  Check where the identity actually starts,
    and confirm 4 is safe (not that 4 is tight -- it is not).
"""

import sympy as sp

z = sp.symbols("z")


def d_coeff(Qc, r, j):
    """d_j = C(Q_j) + [j = r] X, as a polynomial in z."""
    q = Qc[j] if j < len(Qc) else 0
    return sp.expand(q + (z if j == r else 0))


def F_seq(Qc, Bc, r, n):
    """The recursive solution, n+1 terms."""
    assert Qc[0] != 0
    F = []
    for M in range(n + 1):
        b = Bc[M] if M < len(Bc) else 0
        S = sum(d_coeff(Qc, r, M - i) * F[i] for i in range(M))
        F.append(sp.expand(sp.Rational(1, 1) / Qc[0] * (b - S)))
    return F


def check_general() -> None:
    cases = [
        ([1, 2, 3], [5, 7, 11], 1),
        ([2, -1, 0, 4], [1, 0, 0, 0, 9], 1),
        ([1, sp.Rational(-7, 4), sp.Rational(7, 8), sp.Rational(-1, 8)],
         [1, 0, sp.Rational(3, 2), -2, 5], 1),
        ([3, 1, -2, 5], [0, 1, 2, 3, 4, 5], 2),
        ([1, 0, 0, 0, 0, 7], [2, 2, 2], 3),
    ]
    for Qc, Bc, r in cases:
        n = 8
        F = F_seq(Qc, Bc, r, n)
        for M in range(n + 1):
            lhs = sp.expand(sum(d_coeff(Qc, r, j) * F[M - j] for j in range(M + 1)))
            rhs = Bc[M] if M < len(Bc) else 0
            assert sp.simplify(lhs - rhs) == 0, (Qc, Bc, r, M, lhs, rhs)
        print(f"  Q={Qc} B={Bc} r={r}: convolution system holds for M = 0..{n}")
    print("GENERAL: existence half holds for every (Q, B, r) tested, symbolically in z")


def check_panel_threshold() -> None:
    """P_m against F_{m+2} at the panel."""
    Qc = [1, sp.Rational(-7, 4), sp.Rational(7, 8), sp.Rational(-1, 8)]
    # 64 B = t^6 - 22t^5 + 141t^4 - 252t^3 + 548t^2 - 288t + 64, so B_j = coeff/64
    B64 = [64, -288, 548, -252, 141, -22, 1]           # ascending
    Bc = [sp.Rational(c, 64) for c in B64]
    n = 14
    F = F_seq(Qc, Bc, 1, n)

    # the panel's own recurrence, from cor:panel-B-attractor
    P = [z**2 + z + 1, sp.expand(-z**3 + sp.Rational(3, 4) * z**2
                                 - sp.Rational(1, 4) * z + sp.Rational(15, 4))]
    for m in range(2, n):
        prev3 = P[m - 3] if m >= 3 else 0
        P.append(sp.expand(-(z - sp.Rational(7, 4)) * P[m - 1]
                           - sp.Rational(7, 8) * P[m - 2]
                           + sp.Rational(1, 8) * prev3))

    first_ok = None
    for m in range(0, n - 2):
        agree = sp.simplify(sp.expand(P[m] - F[m + 2])) == 0
        if m <= 5:
            print(f"  m = {m}: P_m == F_(m+2)?  {agree}")
        if agree and first_ok is None:
            first_ok = m
        if not agree:
            first_ok = None
    print(f"  identity first holds, and holds thereafter, from m = {first_ok}")
    assert first_ok == 2, first_ok
    # the Lean threshold from panelReductionCoeff is 4; check it is safe
    for m in range(4, n - 2):
        assert sp.simplify(sp.expand(P[m] - F[m + 2])) == 0
    print("  m >= 4 (panelReductionCoeff's threshold) is inside the true range m >= 2")


def check_rate_exponent() -> None:
    """The rate transports as (1/3)^(m+2) <= (1/3)^m, so K is not enlarged."""
    for m in range(0, 6):
        assert sp.Rational(1, 3) ** (m + 2) <= sp.Rational(1, 3) ** m
    print("  (1/3)^(m+2) <= (1/3)^m for all m, so the F-index rate carries to the P-index")


if __name__ == "__main__":
    print("(1) generality of the existence half")
    check_general()
    print("(2) threshold composition at the panel")
    check_panel_threshold()
    check_rate_exponent()
    print("ALL PASS")
