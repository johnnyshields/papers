#!/usr/bin/env python3
r"""Paper section `sec:conclusion` (Concluding remarks): the degreewise scope of the
multiplicity-four failure, and section `sec:threshold`'s kernel at `r = 3`.

`prop:multiplicity-threshold` settles DEGREE THREE at every multiplicity: the central
slope carries the factor `r(3-r)`, so `G^{(r)}_3` rises to its centre at `r = 2`,
arrives tangentially at `r = 3`, and turns over for every `r >= 4`.
`subsec:first-supercritical-case` then shows the failure is not uniform in the degree --
the Bernstein certificate fails from `m >= 3`, yet `J^{(4)}_4 > 0`, so degree four's
kernel is monotone after all.

That leaves exactly one question, and this script is its evidence: at `r = 4`, is degree
three the ONLY degree at which the constant-weight kernel fails to be monotone?  The
conclusion conjectures that it is, over the range checked here.

The kernel is the residue-class form from the proof of `prop:multiplicity-threshold`,

    G^{(r)}_m(p) = p(1-p) * P{ Bin(rm-2, p) = r-1  (mod r) }.

Monotonicity is read in the CENTRALITY COORDINATE, not in `p`.  `G^{(r)}_m` is symmetric
about `p = 1/2`, so with `u = p - 1/2` it is even in `u` and equals `H(u^2)`; since
`q = p(1-p) = 1/4 - u^2`, the paper's `\widehat G` is `H(1/4 - q)`.  Hence

    G nondecreasing toward p = 1/2   <=>   \widehat G increasing in q   <=>   H' <= 0 on [0,1/4],

and the whole test is an exact real-root count of `H'` on that interval -- Sturm over
rationals, no sampling and no floating point, so a missed root is not a possible failure
mode.  Evenness in `u` is asserted rather than assumed.
"""
import os
from concurrent.futures import ProcessPoolExecutor

from sympy import Poly, Rational, binomial, diff, expand, symbols

p, u, v = symbols("p u v")

R4_EXCEPTIONAL_DEGREE = 3
M_MAX = 50
MULTIPLICITIES = (3, 4)

# The named checks below run over this short prefix rather than the committed
# range.  `check_mutation_bite.py` runs ONE check per mutation, so a target that
# swept to M_MAX would make the harness's last step cost minutes per mutation;
# every assertion these make is the same one the full sweep makes, at a degree
# where the Sturm count is cheap.
SMALL_MAX = 8


def kernel(r, m):
    """G^{(r)}_m(p) as an exact polynomial."""
    n = r * m - 2
    tail = sum(binomial(n, j) * p**j * (1 - p) ** (n - j)
               for j in range(n + 1) if j % r == (r - 1) % r)
    return expand(p * (1 - p) * tail)


def centrality_derivative(r, m):
    """H'(v), where G^{(r)}_m = H(u^2) with u = p - 1/2 and v = u^2 = 1/4 - q."""
    g = Poly(expand(kernel(r, m).subs(p, Rational(1, 2) + u)), u)
    coeffs = g.all_coeffs()[::-1]                      # index = power of u
    for k, c in enumerate(coeffs):
        assert not (k % 2 and c), f"r={r} m={m}: G is not even in u -- odd term u^{k}"
    h = sum(c * v ** (k // 2) for k, c in enumerate(coeffs) if k % 2 == 0)
    return Poly(expand(diff(h, v)), v)


def is_monotone(r, m):
    """Is G^{(r)}_m nondecreasing on [0,1/2]?  Exact; returns (verdict, interior roots)."""
    hp = centrality_derivative(r, m)
    if hp.is_zero:
        return True, 0
    interior = hp.count_roots(Rational(1, 10**12), Rational(1, 4) - Rational(1, 10**12))
    mid = hp.eval(Rational(1, 8))
    return (interior == 0 and mid <= 0), interior


def _sweep_one(task):
    """One (multiplicity, degree) cell.  Top-level so a process pool can pickle it."""
    r, m = task
    ok, roots = is_monotone(r, m)
    return r, m, ok, roots


def sweep():
    """Every cell, across processes.

    The cells are independent and the work is CPU-bound inside SymPy, so THREADS
    would buy nothing -- the GIL serialises exactly the part that is slow.
    Processes do help, and the cost is dominated by the largest degree, which no
    amount of fan-out shortens.  Results are collected into a dict and read back
    in a fixed order, so the output does not depend on completion order.
    """
    tasks = [(r, m) for r in MULTIPLICITIES for m in range(2, M_MAX + 1)]
    workers = max(1, min(os.cpu_count() or 1, len(tasks)))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        done = list(pool.map(_sweep_one, tasks, chunksize=1))
    return workers, {(r, m): (ok, roots) for r, m, ok, roots in done}


def check_cubic_kernel_is_monotone():
    """`thm:kernel`'s direction, cheaply: r = 3 is monotone in every degree."""
    for m in range(2, SMALL_MAX + 1):
        ok, roots = is_monotone(3, m)
        assert ok, (f"r=3 m={m}: kernel NOT monotone ({roots} interior roots) "
                    "-- contradicts thm:kernel")


def check_exceptional_degree_is_three():
    """r = 4 fails at degree three and nowhere else, with one interior turning point."""
    failures = [m for m in range(2, SMALL_MAX + 1) if not is_monotone(4, m)[0]]
    assert failures == [R4_EXCEPTIONAL_DEGREE], (
        f"r=4: expected degree {R4_EXCEPTIONAL_DEGREE} to be the only non-monotone "
        f"degree over 2..{SMALL_MAX}, got {failures}")
    roots = is_monotone(4, R4_EXCEPTIONAL_DEGREE)[1]
    assert roots == 1, f"r=4 m=3: expected one interior turning point, got {roots}"
    assert is_monotone(4, 4)[0], "r=4 m=4: contradicts subsec:first-supercritical-case"


def main():
    check_cubic_kernel_is_monotone()
    check_exceptional_degree_is_three()

    workers, res = sweep()

    # r = 3 is the paper's theorem: monotone in every degree.  Included so the
    # instrument is shown to fire in the direction the paper already proves.
    for m in range(2, M_MAX + 1):
        ok, roots = res[(3, m)]
        assert ok, f"r=3 m={m}: kernel NOT monotone ({roots} interior roots) -- contradicts thm:kernel"

    failures = [m for m in range(2, M_MAX + 1) if not res[(4, m)][0]]
    assert failures == [R4_EXCEPTIONAL_DEGREE], (
        f"r=4: expected degree {R4_EXCEPTIONAL_DEGREE} to be the only non-monotone "
        f"degree over 2..{M_MAX}, got {failures}")

    # The exceptional degree is exceptional for the reason prop:multiplicity-threshold
    # gives: an interior maximum, i.e. a genuine sign change of H'.
    roots3 = res[(4, 3)][1]
    assert roots3 == 1, f"r=4 m=3: expected one interior turning point, got {roots3}"

    # And degree four is the case the paper proves by hand (J^{(4)}_4 > 0).
    assert res[(4, 4)][0], "r=4 m=4: contradicts subsec:first-supercritical-case"

    print(f"PASS  r=3: G^(3)_m nondecreasing on [0,1/2] for m = 2..{M_MAX} (exact root count, "
          f"{workers} processes)")
    print(f"PASS  r=4: degree {R4_EXCEPTIONAL_DEGREE} is the ONLY non-monotone degree over "
          f"m = 2..{M_MAX}; it has exactly one interior turning point")
    print("PASS  r=4 m=4 is monotone, as `subsec:first-supercritical-case` proves directly")
    print("ALL PASS: check_r4_kernel_monotone")


if __name__ == "__main__":
    main()
