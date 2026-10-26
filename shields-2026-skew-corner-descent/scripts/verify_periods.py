"""Check parent-only period obstructions by independent symbolic factorization."""
from collections import Counter
from functools import lru_cache
from sympy import factor_list, symbols
from diagram_tools import (columns, components, compose, corner_cofactor, interior,
                           legal_marks, normalization, polynomial_span, profile,
                           profile_shape, rows, schur, shapes_of_area, span)

H = symbols('h0:100')


@lru_cache(maxsize=4096)
def factors(key):
    expression = 0
    for mon, coefficient in key:
        term = coefficient
        for j in mon:
            term *= H[j]
        expression += term
    _, fs = factor_list(expression)
    return tuple((max((int(str(h)[1:]) for h in f.free_symbols), default=0), m, str(f))
                 for f, m in fs)


def gate(N, q, fs):
    M, u = divmod(N, q)
    if M < 2:
        return False
    L, exposed = 0, 0
    for ell, multiplicity, _ in fs:
        if ell >= q:
            if ell < q+u or (ell-u) % q:
                return False
            L += multiplicity*((ell-u)//q)
            exposed += ell == q+u
    if exposed > 1 or M-L < 2:
        return False
    return all(not (u < ell < q) or (ell <= q-u-2 and multiplicity % (M-L) == 0)
               for ell, multiplicity, _ in fs)


def extracted_component(E, R, U, W, v, case, component_reader=components):
    """Return an actual interior component, never an invented prime realization."""
    matches = [V for V in component_reader(interior(R))
               if schur(compose(V, U, W, v, case)) == schur(E)]
    assert matches, 'no actual candidate component supplies the inherited function'
    return matches[0]


def alpha_constraints(D, R, inner_corner, candidate_factors):
    """Conclusions checked after the actual span/corner hypotheses are checked."""
    t = len(interior(D))
    assert t >= 1
    assert all(len(V) == 1 for V in components(interior(R)))
    assert len(interior(R)) == t
    assert rows(R) == t+1 and all(g == 1 for g in profile(R)[1])
    A, B, _, _ = candidate_factors
    u = polynomial_span(A)
    assert polynomial_span(inner_corner) < u
    assert polynomial_span(B) < u
    assert span(R) > span(D) >= 2*t+1
    assert columns(R)-1-t == span(R)-2*t-1 > 0


def must_fail(test):
    try:
        test()
    except AssertionError:
        return
    raise AssertionError('a deliberately false residual formula passed')


def check_discrete_residual():
    """Legal fixtures, exact minors, and the positive hat-valuation coefficient.

    The alpha fixtures have equal spans and corners, not assumed equal full
    parent functions. The beta fixture has equal literal parents but is not
    an unequal-source-minimum example. No all-size minimum claim is computed.
    """
    counts = Counter()
    for n in range(2, 10):
        for D in shapes_of_area(n):
            cc = components(interior(D))
            if any(len(V) > 1 for V in cc):
                continue
            t = len(cc)
            gaps = profile(D)[1]
            assert span(D) >= 2*t+1
            assert all(g <= 1 for g in gaps) and sum(gaps) == t
            assert (rows(D) == t+1) == all(g == 1 for g in gaps)
            counts['discrete geometry cases'] += 1
    U = profile_shape((2, 1), (0,))
    omega = (frozenset(), (-1, 2), 'a')
    eta = (frozenset({(0, 0)}), (-1, 1), 'd')
    assert omega in list(legal_marks(U)) and eta in list(legal_marks(U))
    for lengths, gaps, candidate_lengths in [((2, 2), (1,), (3, 2)),
                                             ((2, 3, 2), (1, 1), (3, 3, 3))]:
        D = profile_shape(lengths, gaps)
        R = profile_shape(candidate_lengths, gaps)
        F, G = compose(D, U, *omega), compose(R, U, *eta)
        assert span(F) == span(G) and corner_cofactor(F) == corner_cofactor(G)
        factors_eta = normalization(U, eta[0], eta[1])
        alpha_constraints(D, R, corner_cofactor(U), factors_eta)
        # A wrong full hatted mark, or a missing strict inner-corner bound,
        # must fail even though the input parent span and corner still agree.
        A, B, C, theta = factors_eta
        u = polynomial_span(A)
        wrong = {(u,): 1}
        must_fail(lambda: alpha_constraints(D, R, corner_cofactor(U), (A, wrong, C, theta)))
        must_fail(lambda: alpha_constraints(D, R, wrong, factors_eta))
        counts['residual mutations caught'] += 2
        counts['alpha actual span/corner fixtures'] += 1
    V, D = profile_shape((2,), ()), profile_shape((2, 2), (1,))
    E = compose(V, U, *omega)
    R = compose(D, V, frozenset(), (0, 2), 'a')
    F = compose(D, E, frozenset(), (-2, 4), 'a')
    G = compose(R, U, *omega)
    assert F == G and corner_cofactor(F) == schur(E)
    child = extracted_component(E, R, U, *omega)
    assert span(child) == 2 and span(E) == 3*span(child)
    assert len(compose(child, U, *omega)) == len(E) < len(F)
    must_fail(lambda: extracted_component(E, R, U, *omega, component_reader=lambda _: []))
    counts['beta actual-component fixtures'] += 1
    counts['residual mutations caught'] += 1
    print(dict(counts))


def main():
    counts = Counter()
    outers = [D for n in range(2, 5) for D in shapes_of_area(n)]
    for n in range(2, 6):
        for E in shapes_of_area(n):
            for W, v, case in legal_marks(E):
                p = v[1]-v[0]
                for D in outers:
                    F = compose(D, E, W, v, case)
                    fs = factors(tuple(sorted(corner_cofactor(F).items())))
                    assert gate(span(F), p, fs)
                    counts['actual chart periods accepted'] += 1
                    for q in range(2, span(F)//2+1):
                        if q != p and not gate(span(F), q, fs):
                            counts['other candidate periods excluded'] += 1
    assert counts['other candidate periods excluded'] > 0
    assert gate(6, 3, ((1, 2, 'h1'),))
    assert not gate(6, 3, ((1, 3, 'h1'),))
    assert not gate(13, 3, ((5, 1, 'f'),))  # 5 is not 1 modulo 3
    for p in range(2, 40):
        for q in range(p+1, 40):
            assert 2*q > p+(p-1)  # even the smallest large child beats a one-cell child
    best = lambda N: min(range(2, N//2+1), key=lambda p: (N % p, p+N % p))
    assert best(9) == 3 and best(12) == 2
    F, G = profile_shape((3, 3), (1,)), profile_shape((2, 4), (1,))
    assert corner_cofactor(F) == corner_cofactor(G) == {(1,): 1}
    assert schur(F) != schur(G)
    print(dict(counts))
    print('multiplicity, congruence, nonline, and same-corner controls fired')
    check_discrete_residual()
    print('verify_periods: PASS')


if __name__ == '__main__':
    main()
