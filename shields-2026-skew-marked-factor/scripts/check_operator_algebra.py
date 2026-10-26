r"""Paper section `sec:action` (Marked composition and the power-sum action).

Operator and character algebra under the sweeps, derived from the defining
formulas rather than read off the decoder.  Targets: `eq:delta` (the three forms
of the Hall adjoint of multiplication by a power sum), the involution and its
transport through the two operators (`eq:physical-operator-transport` of
`sec:weighted-action`), the weighted operator of `eq:weighted-operator`, the
character expansion `eq:character` of `sec:extraction`, and the operator
identities that `sec:mixed-extraction` states about \(\mathcal B_k=pV_k+\rho\delta_k\):
the terminal evaluation `eq:mixed-terminal-evaluation` for every homogeneous
function, the action on power sums, the triangular structure behind
`rt:outer-triangle`, and the nonvanishing of ribbon specializations on the open
interval used by `rt:mixed-readout`.

Everything is exact (SymPy integers and rationals).  The power-sum route builds
\(h_j\) from the exponential generating series, so no step reads an operator off
the `h`-form it is asked to confirm.  Where the claim is polynomial in \((p,\rho)\)
of degree at most the weight, it is checked on a grid larger than the degree in each
variable, which proves it for that weight.
"""

from collections import Counter
from fractions import Fraction
from itertools import product

import sympy as sp

from schur_tools import (apply, delta, from_profile, h, normalize, partitions,
                         power_sum, rotate, schur, shapes, standard_tableaux,
                         transpose, antitranspose, z_value)
from _weighted_readout import (alphabet_value, elementary, involution,
                               power_product, weighted, word)

P = {k: sp.Symbol(f'P{k}') for k in range(1, 13)}


def hp(j):
    """Complete function in power sums, from sum_nu p_nu / z_nu."""
    if j == 0:
        return sp.Integer(1)
    return sp.expand(sum(sp.prod(P[k] for k in nu) / z_value(nu) for nu in partitions(j)))


def to_p(poly):
    poly = sp.sympify(poly)
    return sp.expand(poly.xreplace({x: hp(int(x.name[1:])) for x in poly.free_symbols
                                    if x.name.startswith('h')}))


def hall(f, g, n):
    """Hall inner product of two degree-n power-sum polynomials, <p_nu, p_mu> = z_nu delta."""
    gens = [P[k] for k in range(1, n + 1)]
    cf = dict(sp.Poly(f, *gens).terms()) if f != 0 else {}
    cg = dict(sp.Poly(g, *gens).terms()) if g != 0 else {}
    total = 0
    for mon, a in cf.items():
        nu = tuple(k for k, e in zip(range(1, n + 1), mon) for _ in range(e))
        total += a * cg.get(mon, 0) * z_value(tuple(sorted(nu, reverse=True)))
    return sp.nsimplify(total)


def omega_p(f):
    return sp.expand(f.xreplace({P[k]: (-1) ** (k - 1) * P[k] for k in P}))


def check_generating_series():
    for j in range(1, 10):
        # the derivative of sum h_j t^j = exp(sum p_k t^k / k) gives the Newton recurrence
        assert sp.expand(j * hp(j) - sum(P[i] * hp(j - i) for i in range(1, j + 1))) == 0
    print('PASS: complete functions from the exponential series satisfy the Newton recurrence (eq:delta)')


def check_adjoint_forms():
    """The three forms of delta_k, and its adjointness for the Hall form."""
    # The Hall form is pinned by orthonormality of the straight Schur functions.
    pairs = 0
    for n in range(1, 7):
        lams = list(partitions(n))
        straight = [schur(normalize(frozenset((i, j) for i, r in enumerate(lam)
                                              for j in range(r)))) for lam in lams]
        for a, fa in enumerate(straight):
            for b, fb in enumerate(straight):
                assert hall(to_p(fa), to_p(fb), n) == (1 if a == b else 0)
                pairs += 1
    forms = adjoint = 0
    for n in range(1, 7):
        for D in shapes(n):
            f = schur(D)
            fp = to_p(f)
            for k in range(1, n + 1):
                # eq:delta, first and last forms: k d/dp_k against the h-form
                assert to_p(delta(f, k)) == sp.expand(k * sp.diff(fp, P[k])), (D, k)
                forms += 1
                # eq:delta, first equality: the adjoint of multiplication by p_k
                for mu in partitions(n - k):
                    g = sp.expand(sp.prod(P[j] for j in mu) * P[k])
                    left = hall(g, fp, n)
                    base = sp.prod(P[j] for j in mu) if mu else sp.Integer(1)
                    dk = to_p(delta(f, k))
                    right = hall(base, dk, n - k) if n > k else dk
                    assert left == right, (D, k, mu)
                    adjoint += 1
    print(f'PASS: Hall form orthonormal on straight shapes ({pairs} pairs); '
          f'delta_k = k d/dp_k on {forms} (shape, k) pairs; adjointness on {adjoint} (shape, k, mu) triples')


def check_involution():
    for j in range(1, 8):
        assert to_p(involution(h(j))) == omega_p(to_p(h(j))) == to_p(elementary(j))
        # the stated action on power sums: omega(p_j) = (-1)^(j-1) p_j
        assert sp.expand(to_p(involution(power_sum(j))) - (-1) ** (j - 1) * to_p(power_sum(j))) == 0
        assert to_p(power_sum(j)) == P[j]
    shapes_seen = 0
    for n in range(1, 8):
        for D in shapes(n):
            f = schur(D)
            assert schur(rotate(D)) == f                            # s_{D^*} = s_D
            assert schur(antitranspose(D)) == involution(f)         # s_{AT(D)} = omega(s_D)
            assert schur(transpose(D)) == involution(f)
            shapes_seen += 1
            if n <= 6:
                assert to_p(involution(f)) == omega_p(to_p(f))
    print(f'PASS: omega(p_j) = (-1)^(j-1) p_j, s_(D*) = s_D and s_AT(D) = omega(s_D) on {shapes_seen} diagrams')


def check_operator_transport():
    count = 0
    for n in range(1, 7):
        for D in shapes(n):
            f = schur(D)
            for j in range(1, n + 2):
                assert delta(involution(f), j) == sp.expand((-1) ** (j - 1) * involution(delta(f, j)))
                assert weighted(involution(f), j) == sp.expand((-1) ** j * involution(weighted(f, j)))
                count += 1
    print(f'PASS: delta_j omega = (-1)^(j-1) omega delta_j and V_j omega = (-1)^j omega V_j '
          f'on {count} (shape, j) pairs')


def check_weighted_operator():
    """eq:weighted-operator against its literal definition, and its basic properties."""
    def literal(f, k):
        f = sp.sympify(f)
        top = max([int(x.name[1:]) for x in f.free_symbols] + [0])
        return sp.expand(sum(j * h(j) * sp.diff(f, h(j + k)) for j in range(1, top + 1)))

    for k in range(1, 9):
        for m in range(0, 11):
            expect = (m - k) * h(m - k) if m > k else 0
            assert literal(h(m), k) == expect == weighted(h(m), k)
    # the operator kills the terminal generator, unlike delta_k
    for k in range(1, 9):
        assert weighted(h(k), k) == 0 and delta(h(k), k) == 1
    # derivation property on products
    mons = [h(1) * h(3), h(2) ** 2, h(1) * h(2) * h(4), h(5) * h(3) ** 2]
    for f, g in product(mons, repeat=2):
        for k in range(1, 6):
            assert weighted(f * g, k) == sp.expand(weighted(f, k) * g + f * weighted(g, k))
            assert delta(f * g, k) == sp.expand(delta(f, k) * g + f * delta(g, k))
    # the weighted operators do not commute, so the order of a readout is part of it
    assert weighted(weighted(h(5), 1), 2) != weighted(weighted(h(5), 2), 1)
    print('PASS: V_k = sum j h_j d/dh_(j+k) literally, V_k h_k = 0, derivation, noncommuting')


def character_by_route(D, nu):
    return apply(schur(D), nu)


def check_character_expansion():
    count = 0
    for n in range(1, 7):
        for D in shapes(n):
            fp = to_p(schur(D))
            gens = [P[k] for k in range(1, n + 1)]
            terms = dict(sp.Poly(fp, *gens).terms()) if fp != 0 else {}
            total = 0
            for nu in partitions(n):
                mon = tuple(Counter(nu)[k] for k in range(1, n + 1))
                chi = terms.get(mon, 0) * z_value(nu)
                # the coefficient route and the iterated adjoint (character = <p_nu, s_D>) agree
                assert chi == character_by_route(D, nu), (D, nu)
                total += chi / z_value(nu) * sp.prod(P[k] for k in nu)
                count += 1
            assert sp.expand(total - fp) == 0
            ones = tuple(Counter((1,) * n)[k] for k in range(1, n + 1))
            assert terms.get(ones, 0) * z_value((1,) * n) == standard_tableaux(D) > 0
    print(f'PASS: s_D = sum chi(nu)/z_nu p_nu, f^D = chi(1^n) > 0, two routes to chi: {count} values')


def grid():
    return [(p, rho) for p in range(1, 9) for rho in range(0, 10)]


def Bop(f, k, p, rho):
    return sp.expand(p * weighted(f, k) + rho * delta(f, k))


def check_generator_formulas():
    """The displayed generator formulas for pV_k + rho delta_k on h_j and e_j."""
    count = 0
    for p, rho in [(2, 1), (3, 2), (5, 1), (7, 4)]:
        for k in range(1, 9):
            for j in range(1, 9):
                if j >= k:
                    assert Bop(h(j), k, p, rho) == sp.expand((p * (j - k) + rho) * h(j - k))
                    assert Bop(elementary(j), k, p, rho) == sp.expand(
                        (-1) ** (k - 1) * (rho - p * (j - k)) * elementary(j - k))
                else:
                    assert Bop(h(j), k, p, rho) == 0 and Bop(elementary(j), k, p, rho) == 0
                count += 1
    print(f'PASS: (pV_k + rho delta_k) on h_j and e_j, including j < k and j = k: {count} cases')


def check_terminal_evaluation(maxm=7):
    """eq:mixed-terminal-evaluation for every homogeneous function, as a polynomial identity."""
    count = 0
    for m in range(1, maxm + 1):
        for lam in partitions(m):
            Q = sp.prod(h(j) for j in lam)
            for p, rho in grid():
                x = sp.Rational(rho, p)
                value = Q
                for _ in range(m):
                    value = Bop(value, 1, p, rho)
                # constant term of exp(zB_1) h_j is p^j (rho/p)_j z^j / j!
                assert value == sp.factorial(m) * p ** m * alphabet_value(Q, x), (lam, p, rho)
            count += 1
        for p, rho in [(3, 2), (4, 1)]:
            f = h(m)
            for step in range(m):
                f = Bop(f, 1, p, rho)
            assert f == sp.prod(rho + i * p for i in range(m))
    print(f'PASS: B_1^m Q = m! p^m Q(1^(rho/p)) on {count} h-monomials of weight up to {maxm}, '
          f'on a {len(grid())}-point grid exceeding its degree (a proof for each weight)')


def refines(nu, lam):
    """Brute force: can the parts of nu be grouped into sums equal to the parts of lam?"""
    if sum(nu) != sum(lam):
        return False

    def go(i, bins):
        if i == len(nu):
            return all(b == 0 for b in bins)
        for b in range(len(bins)):
            if bins[b] >= nu[i]:
                bins[b] -= nu[i]
                if go(i + 1, bins):
                    bins[b] += nu[i]
                    return True
                bins[b] += nu[i]
        return False
    return go(0, list(lam))


def check_triangularity(maxm=7):
    count = 0
    for p, rho in [(3, 2), (5, 1)]:
        for k in range(1, 9):
            for j in range(1, 9):
                got = Bop(power_sum(j), k, p, rho)
                if j > k:
                    assert got == sp.expand(p * j * power_sum(j - k))
                elif j == k:
                    assert got == rho * k
                else:
                    assert got == 0
        for m in range(1, maxm + 1):
            parts = list(partitions(m))
            for nu in parts:
                for lam in parts:
                    value = word(power_product(lam), nu, lambda f, k: Bop(f, k, p, rho))
                    assert not value.free_symbols
                    if not refines(nu, lam):
                        assert value == 0, (nu, lam)
                    if len(nu) < len(lam):
                        assert value == 0
                    if len(nu) == len(lam) and nu != lam:
                        assert value == 0
                    if nu == lam:
                        assert value == rho ** len(lam) * z_value(lam)
                    count += 1
    print(f'PASS: B_k on power sums; B_nu p_lam zero unless nu refines lam, and rho^l z_lam on the '
          f'diagonal, for all pairs of partitions through weight {maxm}: {count} pairs')


def coarsenings(alpha):
    cuts = len(alpha) - 1
    for mask in range(1 << cuts):
        parts, run = [], alpha[0]
        for i in range(cuts):
            if mask >> i & 1:
                parts.append(run)
                run = alpha[i + 1]
            else:
                run += alpha[i + 1]
        parts.append(run)
        yield tuple(parts)


def compositions(n):
    if n == 0:
        yield ()
    else:
        for k in range(1, n + 1):
            for rest in compositions(n - k):
                yield (k,) + rest


def check_ribbon_specialization(maxm=9):
    """s_D(1^x) != 0 for every ribbon and every 0 < x < 1; the interval is load-bearing."""
    xs = [Fraction(a, b) for b in (2, 3, 4, 5, 7, 9, 11) for a in range(1, b)]
    xs = sorted(set(xs))
    at_one = at_two = 0
    count = 0
    for m in range(1, maxm + 1):
        for alpha in compositions(m):
            D = from_profile(alpha, (0,) * (len(alpha) - 1))
            f = schur(D)
            # independent expansion by interval coarsening of the composition
            expansion = sp.expand(sum((-1) ** (len(alpha) - len(beta)) * sp.prod(h(b) for b in beta)
                                      for beta in coarsenings(alpha)))
            assert expansion == f
            Dt = transpose(D)
            rows_t = len({i for i, j in Dt})
            for x in xs:
                x = sp.Rational(x.numerator, x.denominator)
                value = alphabet_value(f, x)
                assert value != 0, (alpha, x)
                assert value == (-1) ** m * alphabet_value(schur(Dt), -x)
                for j in range(1, m + 1):
                    assert alphabet_value(h(j), -x) < 0
                count += 1
            # every term of the transposed expansion has the same sign at -x
            tr_alpha = tuple(Counter(i for i, j in Dt)[i] for i in sorted({i for i, j in Dt}))
            assert sp.expand(sum((-1) ** (rows_t - len(beta)) * sp.prod(h(b) for b in beta)
                                 for beta in coarsenings(tr_alpha))) == schur(Dt)
            for beta in coarsenings(tr_alpha):
                term = (-1) ** (rows_t - len(beta)) * sp.prod(
                    alphabet_value(h(b), -sp.Rational(2, 7)) for b in beta)
                assert term * (-1) ** rows_t > 0
            at_one += alphabet_value(f, sp.Integer(1)) == 0
            at_two += alphabet_value(f, sp.Integer(2)) == 0
    assert at_one > 0 and at_two > 0
    print(f'PASS: s_D(1^x) != 0 on {count} (ribbon, x) pairs, 0 < x < 1; '
          f'the same specialization vanishes at x = 1 on {at_one} ribbons and at x = 2 on {at_two}')


def main():
    check_generating_series()
    check_adjoint_forms()
    check_involution()
    check_operator_transport()
    check_weighted_operator()
    check_character_expansion()
    check_generator_formulas()
    check_terminal_evaluation()
    check_triangularity()
    check_ribbon_specialization()
    print('ALL PASS')


if __name__ == '__main__':
    main()
