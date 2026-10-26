r"""The domino readout of a ribbon outer (rt:domino-probe).

Paper section `sec:reduction` (Factor readout and the two-copy reduction), rt:domino-probe.

Reading: the statement is a reduction, so only the finite steps its proof displays are tested.
Let Q be a ribbon Schur function of a composition with m >= 3 parts-sum and l rows, written in the
h-basis by interval coarsening, and let delta_k, V_k be the derivations defined before
rt:ordinary-readout.  With p >= 1 and a symbolic theta (the proof's |theta| < p):

* the degree-two element (p V_{m-2} + theta delta_{m-2}) Q equals gamma p_2 + lambda p_1^2, with
  gamma = p chi_Q(m) + (theta/2) chi_Q(m-2, 2) read off the h-coefficients, chi_Q(lambda) being the
  inner product with p_lambda computed independently by counting block assignments of the parts
  of lambda;
* chi_Q(m) = (-1)^{l-1} and chi_Q(m-2, 2) = (-1)^{l-1} (1 - [2 is a proper partial sum]
  - [m-2 is a proper partial sum]), with the two occurrences counted separately at m = 4;
* hence |chi_Q(m-2,2)| <= 1 and gamma != 0 on |theta| < p, every theta of a rational grid.  The
  control: gamma vanishes at theta = -2p chi(m) / chi(m-2,2) whenever that coefficient is nonzero,
  so the bound |theta| < p has slack but is not an artifact of the grid;
* m = 2 domino areas (ordinary): on every connected E up to CELLS cells and every legal case (a)
  mark, Row_2 o_omega E has area 2|E| - |W|.

Uncovered: the scalar normalization S, the composite Phi, the mixed positive-phase convention and
the hatted-corner area 2|E| - |W-hat| (no builder for the hatted mark is in this directory).
"""
from fractions import Fraction
from itertools import combinations

from _gluing_common import compose
from check_two_copy_flags import diagrams, marks

CELLS = 7
MMAX = 9


def compositions(n):
    if n == 0:
        yield ()
        return
    for k in range(1, n + 1):
        for rest in compositions(n - k):
            yield (k,) + rest


def partial_sums(alpha):
    s, out = 0, []
    for a in alpha[:-1]:
        s += a
        out.append(s)
    return out


def ribbon_h(alpha):
    """Ribbon Schur function as {sorted tuple of h-indices: coefficient}."""
    sums = partial_sums(alpha)
    out = {}
    for k in range(len(sums) + 1):
        for keep in combinations(sums, k):
            cuts = [0, *keep, sum(alpha)]
            parts = tuple(sorted(b - a for a, b in zip(cuts, cuts[1:])))
            out[parts] = out.get(parts, 0) + (-1) ** (len(sums) - k)
    return out


def delta(poly, k):
    out = {}
    for mon, c in poly.items():
        for i, part in enumerate(mon):
            if part >= k:
                rest = mon[:i] + mon[i + 1:]
                new = tuple(sorted(rest + ((part - k,) if part > k else ())))
                out[new] = out.get(new, 0) + c
    return out


def vop(poly, k):
    out = {}
    for mon, c in poly.items():
        for i, part in enumerate(mon):
            j = part - k
            if j >= 1:
                rest = mon[:i] + mon[i + 1:]
                new = tuple(sorted(rest + (j,)))
                out[new] = out.get(new, 0) + j * c
    return out


def pairing_with_p(poly, lam):
    """<poly, p_lam>: <h_beta, p_lam> counts assignments of the parts of lam to blocks of sum beta."""
    total = 0
    for beta, c in poly.items():
        count = 0

        def assign(i, left):
            nonlocal count
            if i == len(lam):
                count += all(x == 0 for x in left)
                return
            for b in range(len(left)):
                if left[b] >= lam[i]:
                    left[b] -= lam[i]
                    assign(i + 1, left)
                    left[b] += lam[i]

        assign(0, list(beta))
        total += c * count
    return total


def main():
    checked = 0
    for m in range(3, MMAX + 1):
        for alpha in compositions(m):
            l = len(alpha)
            Q = ribbon_h(alpha)
            chi_m = pairing_with_p(Q, (m,))
            chi_2 = pairing_with_p(Q, (m - 2, 2))
            sign = (-1) ** (l - 1)
            sums = partial_sums(alpha)
            assert chi_m == sign
            assert chi_2 == sign * (1 - sums.count(2) - sums.count(m - 2)), (alpha, chi_2)
            assert abs(chi_2) <= 1
            for p in (1, 2, 5):
                for th in (Fraction(a, 4) * p for a in range(-3, 4)):
                    low = delta(Q, m - 2)
                    high = vop(Q, m - 2)
                    comb = {}
                    for mon, c in high.items():
                        comb[mon] = comb.get(mon, 0) + p * c
                    for mon, c in low.items():
                        comb[mon] = comb.get(mon, 0) + th * c
                    c_h2 = comb.get((2,), 0)
                    c_h11 = comb.get((1, 1), 0)
                    assert set(comb) <= {(2,), (1, 1)}
                    gamma = Fraction(c_h2) / 2
                    assert gamma == p * chi_m + th / 2 * chi_2, (alpha, p, th)
                    assert abs(th) < p and gamma != 0, (alpha, p, th)
            if chi_2:
                p = 3
                th = Fraction(-2 * p * chi_m, chi_2)
                assert p * chi_m + th / 2 * chi_2 == 0 and abs(th) >= p
            checked += 1
    print(f'ribbon compositions of m = 3..{MMAX}: {checked}; gamma != 0 on |theta| < p')

    row2 = frozenset({(0, 0), (0, 1)})
    n = 0
    for E in diagrams(CELLS):
        for mk in marks(E):
            if mk.case != 'a':
                continue
            F = compose(row2, mk)
            assert len(F) == 2 * len(E) - len(mk.lower), (sorted(E), sorted(mk.lower))
            n += 1
    assert n > 100
    print(f'ordinary row-two probe area 2|E| - |W|: {n} legal case (a) marks')
    print('ALL PASS')


if __name__ == '__main__':
    main()
