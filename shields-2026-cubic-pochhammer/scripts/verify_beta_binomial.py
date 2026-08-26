#!/usr/bin/env python3
r"""Paper section `sec:reduction` (Exact reduction to a residue kernel).

Re-derives the reduction of the degree-m coefficient convolution to a
beta-binomial expectation, pinning every step to the definitions rather than
transcribing.  With N = 3m and P ~ Beta(u,v), J | P ~ Bin(N,P):

  * the paired weights w_k = f_k f_{m-k}, `lem:central-products`, are symmetric and, under
    log-concavity with no internal zeros, nondecreasing toward the center;
  * the coefficient convolution C_{m,w}(u,v), `eq:C-def`, at arbitrary
    nonnegative weights, with C_{m,w}(0,v)=0; `eq:C-beta-binomial`-`eq:G-weighted` are stated at
    that same general-weight form;
  * the Pochhammer identity
        (u)_j (v)_{N-j} / ((j-1)!(N-j-1)!) = (u+v)_N/N! * j(N-j) P(J=j),
    which turns `eq:C-def` into the beta-binomial expectation `eq:C-beta-binomial`;
  * the endpoint-killing binomial identity j(N-j)C(N,j)=N(N-1)C(N-2,j-1);
  * the mixture identity `eq:C-beta`
        C_{m,w}(u,v) = (u+v)_N/N! * N(N-1) * E G_{m,w}(P),
    with the kernel G_{m,w}, `eq:G-weighted`, verified as a single symbolic identity
    against `eq:C-def`;
  * the p <-> 1-p symmetry of G_{m,w}, `eq:G-weighted`, for symmetric weights;
  * the residue bookkeeping  j = 0 (mod 3)  <=>  j-1 = 2 (mod 3).

Symbolic work uses SymPy; the log-concavity checks use exact Fractions.
"""
from __future__ import annotations

import random
from fractions import Fraction
from math import comb, factorial

import sympy as sp


# ===========================================================================
# 1.  `eq:w-from-f` paired weights w_k = f_k f_{m-k}: symmetry and center-monotonicity
# ===========================================================================
def _poch(u: Fraction, j: int) -> Fraction:
    """(u)_j = u(u+1)...(u+j-1), exact."""
    out = Fraction(1)
    for i in range(j):
        out *= (u + i)
    return out


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
        # symmetry w_k = w_{m-k}
        for r in range(1, m):
            assert w[r] == w[m - r]
        # nondecreasing toward the center: w_{k+1} >= w_k for 1 <= k < floor(m/2)
        for r in range(1, m // 2):
            assert w[r + 1] >= w[r]
        # the underlying cross-product consequence f_{a+1}f_b >= f_a f_{b+1}, a<b
        ks = sorted(f)
        for i in range(len(ks)):
            for j in range(i + 1, len(ks)):
                a, b = ks[i], ks[j]                                  # a < b
                assert fval(a + 1) * fval(b) >= fval(a) * fval(b + 1)
    print("PASS: w_k symmetric and nondecreasing toward the center (`lem:central-products`)")


def check_central_products_converse(L: int = 5) -> None:
    r"""`lem:central-products` (2) => (1), by the paper's own route and exhaustively.

    The converse says that the anti-diagonal inequality `eq:central-products` at EVERY m
    forces log-concavity and interval support.  Two specializations do it:

      * m = 2j, k = j-1 reads f_{j-1}f_{j+1} <= f_j^2, which is log-concavity;
      * m = a+b, k = a with f_a, f_b > 0 and b >= a+2 reads
        f_{a+1}f_{b-1} >= f_af_b > 0, so both inward neighbors are positive, and
        iterating fills every gap between two positive terms.

    Both are asserted below on every nonzero sequence over {0,...,3} supported in
    1..L, and the equivalence itself -- `eq:central-products` at every m if and only if
    log-concave with interval support -- is then checked over that whole family,
    which contains sequences failing each side.
    """
    import itertools

    def central(f):
        """`eq:central-products` at every m; beyond m = 2L every product is 0 <= 0."""
        for m in range(2, 2 * L + 1):
            for k in range(1, (m - 1) // 2 + 1):
                if k >= m // 2:
                    continue
                if f.get(k, 0) * f.get(m - k, 0) > f.get(k + 1, 0) * f.get(m - k - 1, 0):
                    return False
        return True

    def logconcave(f):
        return all(f.get(n, 0) ** 2 >= f.get(n - 1, 0) * f.get(n + 1, 0)
                   for n in range(2, L + 2))

    def interval_support(f):
        pos = [n for n in range(1, L + 1) if f.get(n, 0) > 0]
        return pos == list(range(pos[0], pos[-1] + 1))

    seen = {True: 0, False: 0}
    for tup in itertools.product(range(4), repeat=L):
        if not any(tup):
            continue                       # the lemma hypothesizes a nonzero sequence
        f = {i + 1: v for i, v in enumerate(tup)}
        hyp = central(f)
        seen[hyp] += 1
        if hyp:
            # (2) => log-concave, through m = 2j, k = j-1 specifically
            for j in range(2, L + 1):
                m, k = 2 * j, j - 1
                assert 1 <= k < m // 2, (j, m, k)
                assert f.get(k, 0) * f.get(m - k, 0) <= f.get(k + 1, 0) * f.get(m - k - 1, 0)
                assert f.get(j, 0) ** 2 >= f.get(j - 1, 0) * f.get(j + 1, 0), (tup, j)
            # (2) => no internal zeros, through m = a+b, k = a
            for a in range(1, L + 1):
                for b in range(a + 2, L + 1):
                    if f.get(a, 0) > 0 and f.get(b, 0) > 0:
                        m, k = a + b, a
                        assert 1 <= k < m // 2, (a, b)
                        assert f.get(a + 1, 0) * f.get(b - 1, 0) >= f.get(a, 0) * f.get(b, 0) > 0, tup
        assert hyp == (logconcave(f) and interval_support(f)), tup
    assert seen[True] > 0 and seen[False] > 0, seen
    # `rem:internal-zeros`' own witness: `eq:central-products` fails at exactly one m, and the
    # conclusion fails with it
    f = {1: 1, 4: 1}
    assert logconcave(f) and not interval_support(f)
    fails = [m for m in range(2, 2 * L + 1)
             if any(f.get(k, 0) * f.get(m - k, 0) > f.get(k + 1, 0) * f.get(m - k - 1, 0)
                    for k in range(1, m // 2))]
    assert fails == [5], fails
    print(f"PASS: `lem:central-products` (2) => (1) by the m=2j and m=a+b routes, and "
          f"the equivalence over all {seen[True] + seen[False]} nonzero sequences in "
          f"{{0..3}}^{L} ({seen[True]} satisfying `eq:central-products`, {seen[False]} not)")


# ===========================================================================
# 2.  `eq:C-def`: the coefficient convolution and its vanishing at u=0
# ===========================================================================
def C_def(m: int, w: dict, u, v):
    """C_{m,w}(u,v), `eq:C-def`, at arbitrary weights."""
    total = 0
    for r in range(1, m):
        total += (
            w[r]
            * sp.rf(u, 3 * r)
            * sp.rf(v, 3 * (m - r))
            / (factorial(3 * r - 1) * factorial(3 * (m - r) - 1))
        )
    return total


def check_C_vanishes() -> None:
    """`eq:C-def`: both C_{m,w}(0,v) and C_{m,w}(u,0) vanish."""
    u, v = sp.symbols("u v", positive=True)
    for m in range(2, 7):
        wsyms = sp.symbols(f"w1:{m}")
        w = {r: wsyms[r - 1] for r in range(1, m)}
        # (0)_{3r} = 0 kills every term on the left, (0)_{3(m-r)} = 0 on the right
        assert sp.simplify(C_def(m, w, sp.Integer(0), v)) == 0, m
        assert sp.simplify(C_def(m, w, u, sp.Integer(0))) == 0, m
        # and it is the vanishing Pochhammer that does it, not the weights: at
        # u, v > 0 the same expression is nonzero for w = 1
        one = {r: sp.Integer(1) for r in range(1, m)}
        assert C_def(m, one, sp.Rational(1, 2), sp.Rational(3, 2)) > 0, m
    print("PASS: C_{m,w}(0,v) = C_{m,w}(u,0) = 0 at symbolic weights, and "
          "nonzero away from the two axes (`eq:C-def`)")


# ===========================================================================
# 3.  The Pochhammer identity feeding `eq:C-beta-binomial`
# ===========================================================================
def check_pochhammer_identity(n_max: int = 30) -> None:
    r"""(u)_j(v)_{N-j}/((j-1)!(N-j-1)!) = (u+v)_N/N! * j(N-j) * P(J=j),
    with P(J=j)=C(N,j)(u)_j(v)_{N-j}/(u+v)_N.  After canceling the common
    (u)_j(v)_{N-j}, this is the pure integer identity
        1/((j-1)!(N-j-1)!) = j(N-j) C(N,j) / N!.
    """
    for N in range(2, n_max + 1):
        for j in range(1, N):
            lhs = Fraction(1, factorial(j - 1) * factorial(N - j - 1))
            rhs = Fraction(j * (N - j) * comb(N, j), factorial(N))
            assert lhs == rhs, (N, j)
    print("PASS: Pochhammer/beta-binomial weight identity (`eq:C-beta-binomial`)")


def check_endpoint_identity(n_max: int = 60) -> None:
    """j(N-j)C(N,j) = N(N-1)C(N-2,j-1); endpoints j=0,N give 0."""
    for N in range(2, n_max + 1):
        for j in range(0, N + 1):
            lhs = j * (N - j) * comb(N, j)
            rhs = N * (N - 1) * (comb(N - 2, j - 1) if 1 <= j <= N - 1 else 0)
            assert lhs == rhs, (N, j)
        # the endpoints are inside the sweep above (j = 0 and j = N), where the
        # factor j(N-j) is what vanishes -- C(N,0) and C(N,N) are both 1
        assert comb(N, 0) == comb(N, N) == 1, N
    print("PASS: j(N-j)C(N,j) = N(N-1)C(N-2,j-1), endpoints vanish")


def check_beta_binomial_is_a_law() -> None:
    r"""P(J=j) = C(N,j)(u)_j(v)_{N-j}/(u+v)_N is a probability distribution.

    Everything downstream reads this as a law -- `eq:C-beta-binomial` is an expectation
    against it -- so its total mass must be one and its terms nonnegative.  This
    is the Chu-Vandermonde identity sum_j C(N,j)(u)_j(v)_{N-j} = (u+v)_N; checked
    symbolically in (u,v) so it is the identity rather than sampled instances.
    """
    u, v = sp.symbols("u v", positive=True)
    for m in range(2, 7):
        N = 3 * m
        mass = sum(comb(N, j) * sp.rf(u, j) * sp.rf(v, N - j) for j in range(N + 1))
        assert sp.simplify(sp.expand(mass - sp.rf(u + v, N))) == 0, m
        # and nonnegativity of each term for u, v > 0, on concrete rationals
        for uu, vv in [(Fraction(1, 2), Fraction(3)), (Fraction(7, 3), Fraction(1, 5))]:
            terms = [Fraction(comb(N, j)) * _poch(uu, j) * _poch(vv, N - j)
                     / _poch(uu + vv, N) for j in range(N + 1)]
            assert all(x >= 0 for x in terms), (m, uu, vv)
            assert sum(terms) == 1, (m, uu, vv, sum(terms))
    print("PASS: the beta-binomial pmf is a law (Chu-Vandermonde: unit mass, "
          "nonnegative terms)")


def check_C_beta_binomial_as_an_equation() -> None:
    r"""`eq:C-beta-binomial` itself: C_{m,w}(u,v) = (u+v)_N/N! * E[J(N-J) wtilde_J].

    check_pochhammer_identity verifies the termwise identity that PRODUCES eq.
    `eq:C-beta-binomial`, and check_mixture_identity verifies `eq:C-beta` downstream of it, but the
    assembled equation -- with wtilde_j supported on 0 < j < N, 3 | j, and zero
    elsewhere -- is asserted here, symbolically in (u,v) with symbolic weights.
    """
    u, v = sp.symbols("u v", positive=True)
    for m in range(2, 7):
        N = 3 * m
        wsyms = sp.symbols(f"w1:{m}")
        w = {r: wsyms[r - 1] for r in range(1, m)}
        # wtilde_j = w_{j/3} when 0 < j < N and 3 | j, else 0
        def wtilde(j):
            return w[j // 3] if (0 < j < N and j % 3 == 0) else 0
        pmf = [comb(N, j) * sp.rf(u, j) * sp.rf(v, N - j) / sp.rf(u + v, N)
               for j in range(N + 1)]
        E = sum(wtilde(j) * j * (N - j) * pmf[j] for j in range(N + 1))
        rhs = sp.rf(u + v, N) / factorial(N) * E
        assert sp.simplify(C_def(m, w, u, v) - rhs) == 0, m
        # the J(N-J) factor is what kills the endpoints, so wtilde's value there
        # cannot matter: perturbing it leaves the expectation unchanged
        E_perturbed = sum((wtilde(j) + (5 if j in (0, N) else 0)) * j * (N - j) * pmf[j]
                          for j in range(N + 1))
        assert sp.simplify(E - E_perturbed) == 0, m
    print("PASS: `eq:C-beta-binomial` as an assembled equation, and J(N-J) makes the endpoint "
          "weights irrelevant")


# ===========================================================================
# 4.  `eq:C-beta`-`eq:G-weighted` mixture identity  C = (u+v)_N/N! * N(N-1) * E G_{m,w}(P)
# ===========================================================================
def G_weighted(m: int, w: dict, p):
    """G_{m,w}(p), `eq:G-weighted`."""
    return sum(
        w[r] * comb(3 * m - 2, 3 * r - 1) * p ** (3 * r) * (1 - p) ** (3 * (m - r))
        for r in range(1, m)
    )


def check_mixture_identity() -> None:
    r"""For P ~ Beta(u,v), E[P^a (1-P)^b] = (u)_a (v)_b / (u+v)_{a+b}.  Substituting
    a=3r, b=3(m-r) turns the right side of `eq:C-beta` into `eq:C-def` exactly.
    Verified as a symbolic identity in (u,v) with symbolic weights.
    """
    u, v = sp.symbols("u v", positive=True)
    for m in range(2, 7):
        N = 3 * m
        wsyms = sp.symbols(f"w1:{m}")                     # w_1,...,w_{m-1}
        w = {r: wsyms[r - 1] for r in range(1, m)}
        prefactor = sp.rf(u + v, N) / factorial(N) * N * (N - 1)
        # E G_{m,w}(P) via E[P^{3r}(1-P)^{3(m-r)}] = (u)_{3r}(v)_{3(m-r)}/(u+v)_N.
        # The coefficient of each monomial is READ OFF G_weighted with a one-hot
        # weight rather than retyped, so a wrong binomial there breaks this
        # identity instead of surviving until the symmetry test.
        p = sp.Symbol("p")
        EG = 0
        for r in range(1, m):
            onehot = {q: sp.Integer(1 if q == r else 0) for q in range(1, m)}
            c_r = sp.cancel(G_weighted(m, onehot, p)
                            / (p ** (3 * r) * (1 - p) ** (3 * (m - r))))
            assert c_r.is_Integer and c_r > 0, (m, r, c_r)
            EG += w[r] * c_r * sp.rf(u, 3 * r) * sp.rf(v, 3 * (m - r)) / sp.rf(u + v, N)
        rhs = prefactor * EG
        lhs = C_def(m, w, u, v)
        assert sp.simplify(lhs - rhs) == 0, m
    print("PASS: C = (u+v)_N/N! * N(N-1) * E G_{m,w}(P) (`eq:C-beta`-`eq:G-weighted`)")


def check_fixed_total_conditional_law() -> None:
    """`rem:fixed-total`: the microcanonical law the remark displays.

    With `N_u`, `N_v` independent and `P(N_par = n)` proportional to
    `f_n (par)_{3n} x^n / (3n-1)!`, conditioning on the total `N_u + N_v = m`
    gives

      `P(N_u = k | N_u + N_v = m)
         = f_k f_{m-k} (u)_{3k}(v)_{3(m-k)}
           / ((3k-1)! (3(m-k)-1)! C_{m,w}(u,v))`,

    which is `eq:C-def`'s summand over `eq:C-def` itself.  Checked symbolically
    in `u`, `v`, `x` and the `f_n`, so that the power of `x` cancels under
    conditioning and that the family is a law are settled rather than sampled.
    """
    u, v, x = sp.symbols('u v x', positive=True)
    for m in range(2, 7):
        f = {n: sp.Symbol(f'f{n}', positive=True) for n in range(1, m)}
        w = {k: f[k] * f[m - k] for k in range(1, m)}
        C = C_def(m, w, u, v)

        def weight(par, n):
            return f[n] * sp.rf(par, 3 * n) * x ** n / factorial(3 * n - 1)

        joint = [weight(u, k) * weight(v, m - k) for k in range(1, m)]
        total = sum(joint)
        for k in range(1, m):
            cond = joint[k - 1] / total
            shown = (f[k] * f[m - k] * sp.rf(u, 3 * k) * sp.rf(v, 3 * (m - k))
                     / (factorial(3 * k - 1) * factorial(3 * (m - k) - 1) * C))
            assert sp.simplify(cond - shown) == 0, (m, k)      # `rem:fixed-total`
            assert sp.simplify(sp.diff(cond, x)) == 0, (m, k)  # the power of x cancels
        assert sp.simplify(sum(joint) / total - 1) == 0, m
    print("PASS: `rem:fixed-total`'s conditional law is the displayed ratio of "
          "`eq:C-def`'s summand to `eq:C-def`, is free of x, and sums to 1 "
          "(m = 2..6, symbolic in u, v, x and the f_n)")


def check_G_symmetry() -> None:
    """G_{m,w}(p) = G_{m,w}(1-p) for symmetric weights w_k = w_{m-k}."""
    p = sp.symbols("p")
    for m in range(2, 8):
        base = sp.symbols(f"a0:{m // 2 + 1}")
        w = {r: base[min(r, m - r)] for r in range(1, m)}     # symmetric weights
        for r in range(1, m):
            assert w[r] == w[m - r]
        diff = sp.expand(G_weighted(m, w, p) - G_weighted(m, w, 1 - p))
        assert diff == 0, m
        # the index reflection underlying it: C(3m-2,3k-1)=C(3m-2,3(m-k)-1)
        for r in range(1, m):
            assert comb(3 * m - 2, 3 * r - 1) == comb(3 * m - 2, 3 * (m - r) - 1)
    print("PASS: G_{m,w}(p) = G_{m,w}(1-p) for symmetric weights (`eq:G-weighted`)")


def check_congruence(n_max: int = 60) -> None:
    """j = 0 (mod 3)  <=>  j-1 = 2 (mod 3)."""
    for j in range(1, n_max + 1):
        assert (j % 3 == 0) == ((j - 1) % 3 == 2)
    print("PASS: j = 0 (mod 3) <=> j-1 = 2 (mod 3)")


def main() -> None:
    check_weight_structure()
    check_central_products_converse()
    check_C_vanishes()
    check_pochhammer_identity()
    check_endpoint_identity()
    check_beta_binomial_is_a_law()
    check_C_beta_binomial_as_an_equation()
    check_mixture_identity()
    check_fixed_total_conditional_law()
    check_G_symmetry()
    check_congruence()
    print("ALL PASS: verify_beta_binomial")


if __name__ == "__main__":
    main()
