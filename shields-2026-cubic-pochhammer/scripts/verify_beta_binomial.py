#!/usr/bin/env python3
r"""Paper section 2 (Beta-binomial representation).

Re-derives the reduction of the degree-m coefficient convolution to a
beta-binomial expectation, pinning every step to the definitions rather than
transcribing.  With N = 3m and P ~ Beta(u,v), J | P ~ Bin(N,P):

  * the paired weights w_r = f_r f_{m-r}, eq. (2.1), are symmetric and, under
    log-concavity with no internal zeros, nondecreasing toward the center;
  * the coefficient convolution C_{m,f}(u,v), eq. (2.2), with C_{m,f}(0,v)=0;
  * the Pochhammer identity
        (u)_j (v)_{N-j} / ((j-1)!(N-j-1)!) = (u+v)_N/N! * j(N-j) P(J=j),
    which turns eq. (2.2) into the beta-binomial expectation eq. (2.3);
  * the endpoint-killing binomial identity j(N-j)C(N,j)=N(N-1)C(N-2,j-1);
  * the mixture identity eq. (2.4)
        C_{m,f}(u,v) = (u+v)_N/N! * N(N-1) * E G_{m,w}(P),
    with the kernel G_{m,w}, eq. (2.5), verified as a single symbolic identity
    against eq. (2.2);
  * the p <-> 1-p symmetry of G_{m,w}, eq. (2.5), for symmetric weights;
  * the residue bookkeeping  j = 0 (mod 3)  <=>  j-1 = 2 (mod 3).

Symbolic work uses SymPy; the log-concavity checks use exact Fractions.
"""
from __future__ import annotations

import random
from fractions import Fraction
from math import comb, factorial

import sympy as sp


# ===========================================================================
# 2.1  Paired weights w_r = f_r f_{m-r}: symmetry and center-monotonicity
# ===========================================================================
def rand_logconcave(rng: random.Random, lo: int, hi: int) -> dict:
    """Positive log-concave sequence with no internal zeros on [lo, hi]."""
    f = {lo: Fraction(rng.randint(1, 6))}
    ratio = Fraction(rng.randint(4, 12), rng.randint(1, 3))
    for n in range(lo, hi):
        f[n + 1] = f[n] * ratio
        ratio *= Fraction(rng.randint(1, 20), rng.randint(21, 40))  # nonincreasing
    ks = sorted(f)
    for i in range(1, len(ks) - 1):
        assert f[ks[i]] ** 2 >= f[ks[i - 1]] * f[ks[i + 1]]          # log-concave
    return f


def check_weight_structure(trials: int = 400, seed: int = 20260721) -> None:
    rng = random.Random(seed)
    for _ in range(trials):
        lo = rng.randint(1, 3)
        hi = rng.randint(lo + 2, lo + 8)
        f = rand_logconcave(rng, lo, hi)
        m = rng.randint(2 * lo + 1, 2 * hi - 1)

        def fval(k: int) -> Fraction:
            return f.get(k, Fraction(0))

        w = {r: fval(r) * fval(m - r) for r in range(1, m)}
        # symmetry w_r = w_{m-r}
        for r in range(1, m):
            assert w[r] == w[m - r]
        # nondecreasing toward the center: w_{r+1} >= w_r for 1 <= r < floor(m/2)
        for r in range(1, m // 2):
            assert w[r + 1] >= w[r]
        # the underlying cross-product consequence f_{a+1}f_b >= f_a f_{b+1}, a<b
        ks = sorted(f)
        for i in range(len(ks)):
            for j in range(i + 1, len(ks)):
                a, b = ks[i], ks[j]                                  # a < b
                assert fval(a + 1) * fval(b) >= fval(a) * fval(b + 1)
    print("PASS: w_r symmetric and nondecreasing toward the center (eq. 2.1)")


# ===========================================================================
# 2.2  Coefficient convolution and its vanishing at u=0
# ===========================================================================
def C_def(m: int, w: dict, u, v):
    """C_{m,f}(u,v), eq. (2.2), with weights w_r = f_r f_{m-r}."""
    total = 0
    for r in range(1, m):
        total += (
            w[r]
            * sp.rf(u, 3 * r)
            * sp.rf(v, 3 * (m - r))
            / (factorial(3 * r - 1) * factorial(3 * (m - r) - 1))
        )
    return sp.nsimplify(total) if not isinstance(total, sp.Expr) else total


def check_C_vanishes() -> None:
    v = sp.symbols("v", positive=True)
    for m in range(2, 7):
        w = {r: sp.Integer(1) for r in range(1, m)}
        val = C_def(m, w, sp.Integer(0), v)
        assert sp.simplify(val) == 0, m            # (0)_{3r}=0 kills every term
    print("PASS: C_{m,f}(0,v) = 0 since (0)_{3r} = 0 (eq. 2.2)")


# ===========================================================================
# 2.3  Pochhammer identity feeding the beta-binomial expectation
# ===========================================================================
def check_pochhammer_identity(n_max: int = 30) -> None:
    r"""(u)_j(v)_{N-j}/((j-1)!(N-j-1)!) = (u+v)_N/N! * j(N-j) * P(J=j),
    with P(J=j)=C(N,j)(u)_j(v)_{N-j}/(u+v)_N.  After cancelling the common
    (u)_j(v)_{N-j}, this is the pure integer identity
        1/((j-1)!(N-j-1)!) = j(N-j) C(N,j) / N!.
    """
    for N in range(2, n_max + 1):
        for j in range(1, N):
            lhs = Fraction(1, factorial(j - 1) * factorial(N - j - 1))
            rhs = Fraction(j * (N - j) * comb(N, j), factorial(N))
            assert lhs == rhs, (N, j)
    print("PASS: Pochhammer/beta-binomial weight identity (eq. 2.3)")


def check_endpoint_identity(n_max: int = 60) -> None:
    """j(N-j)C(N,j) = N(N-1)C(N-2,j-1); endpoints j=0,N give 0."""
    for N in range(2, n_max + 1):
        for j in range(0, N + 1):
            lhs = j * (N - j) * comb(N, j)
            rhs = N * (N - 1) * (comb(N - 2, j - 1) if 1 <= j <= N - 1 else 0)
            assert lhs == rhs, (N, j)
        assert 0 * N * comb(N, 0) == 0 and N * 0 * comb(N, N) == 0
    print("PASS: j(N-j)C(N,j) = N(N-1)C(N-2,j-1), endpoints vanish")


# ===========================================================================
# 2.4-2.5  Mixture identity  C = (u+v)_N/N! * N(N-1) * E G_{m,w}(P)
# ===========================================================================
def G_weighted(m: int, w: dict, p):
    """G_{m,w}(p), eq. (2.5)."""
    return sum(
        w[r] * comb(3 * m - 2, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
        for r in range(1, m)
    )


def check_mixture_identity() -> None:
    r"""For P ~ Beta(u,v), E[P^a (1-P)^b] = (u)_a (v)_b / (u+v)_{a+b}.  Substituting
    a=3r, b=3(m-r) turns the right side of eq. (2.4) into eq. (2.2) exactly.
    Verified as a symbolic identity in (u,v) with symbolic weights.
    """
    u, v = sp.symbols("u v", positive=True)
    for m in range(2, 7):
        N = 3 * m
        wsyms = sp.symbols(f"w1:{m}")                     # w_1,...,w_{m-1}
        w = {r: wsyms[r - 1] for r in range(1, m)}
        prefactor = sp.rf(u + v, N) / factorial(N) * N * (N - 1)
        # E G_{m,w}(P) via E[P^{3r}(1-P)^{3(m-r)}] = (u)_{3r}(v)_{3(m-r)}/(u+v)_N
        EG = sum(
            w[r]
            * comb(3 * m - 2, 3 * r - 1)
            * sp.rf(u, 3 * r)
            * sp.rf(v, 3 * (m - r))
            / sp.rf(u + v, N)
            for r in range(1, m)
        )
        rhs = prefactor * EG
        lhs = C_def(m, w, u, v)
        assert sp.simplify(lhs - rhs) == 0, m
    print("PASS: C = (u+v)_N/N! * N(N-1) * E G_{m,w}(P) (eqs. 2.4-2.5)")


def check_G_symmetry() -> None:
    """G_{m,w}(p) = G_{m,w}(1-p) for symmetric weights w_r = w_{m-r}."""
    p = sp.symbols("p")
    for m in range(2, 8):
        base = sp.symbols(f"a0:{m // 2 + 1}")
        w = {r: base[min(r, m - r)] for r in range(1, m)}     # symmetric weights
        for r in range(1, m):
            assert w[r] == w[m - r]
        diff = sp.expand(G_weighted(m, w, p) - G_weighted(m, w, 1 - p))
        assert diff == 0, m
        # the index reflection underlying it: C(3m-2,3r-1)=C(3m-2,3(m-r)-1)
        for r in range(1, m):
            assert comb(3 * m - 2, 3 * r - 1) == comb(3 * m - 2, 3 * (m - r) - 1)
    print("PASS: G_{m,w}(p) = G_{m,w}(1-p) for symmetric weights (eq. 2.5)")


def check_congruence(n_max: int = 60) -> None:
    """j = 0 (mod 3)  <=>  j-1 = 2 (mod 3)."""
    for j in range(1, n_max + 1):
        assert (j % 3 == 0) == ((j - 1) % 3 == 2)
    print("PASS: j = 0 (mod 3) <=> j-1 = 2 (mod 3)")


def main() -> None:
    check_weight_structure()
    check_C_vanishes()
    check_pochhammer_identity()
    check_endpoint_identity()
    check_mixture_identity()
    check_G_symmetry()
    check_congruence()
    print("ALL PASS: verify_beta_binomial")


if __name__ == "__main__":
    main()
