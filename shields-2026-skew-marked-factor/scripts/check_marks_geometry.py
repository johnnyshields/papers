r"""Paper section `sec:action` (Marked composition and the power-sum action).

The geometry under the sweeps, checked against the paper's own definitions and
against the independent composition engine (`_composition_engine.py`).  Targets:
`eq:period`, `eq:ordinary-offsets` and the mixed copy rule, `eq:span`,
`eq:hats`, the key ribbons and `eq:normalizers` of `subsec:ribbon-action`, the
deletion table and the remainder formula `eq:ribbon-remainder` of
`lem:ribbon-deletion`, `eq:modified`, the ordinary-case reduction of
`lem:action` by transposition, the local geometry of a positive mark used in
`sec:weighted-action`, the boundary periodicity `eq:mixed-boundary` of
`lem:mixed-vanishing`, the sign `eq:full-normalization` through its two boundary
decompositions, and the physical transport of marks under rotation, transpose
and antitranspose used in `lem:covariance`.

Every object is rebuilt from its cells.  The ordinary decoder is not used.
SymPy arithmetic is exact.  The boxes are printed with each result.
"""

from collections import Counter

import sympy as sp

from schur_tools import (antitranspose, compose, connected, delta, dimensions, hats,
                         legal_marks, normalize, removals, rotate, schur, shapes,
                         span, transpose, translate)
from _weighted_readout import integer_content, involution, mixed_sign, weighted
import _hopf_shapes_lib as shapes_lib

eng = shapes_lib.eng
E_STEP = (1, 1)


def components(X):
    X = set(X)
    out = []
    while X:
        stack = [X.pop()]
        comp = {stack[0]}
        while stack:
            i, j = stack.pop()
            for y in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1)):
                if y in X:
                    X.remove(y)
                    comp.add(y)
                    stack.append(y)
        out.append(frozenset(comp))
    return out


def offset(d, v):
    """eq:ordinary-offsets, case (a): (j - i) v + i e."""
    i, j = d
    return ((j - i) * v[0] + i, (j - i) * v[1] + i)


def raw_ordinary(D, E, v):
    out = set()
    for d in D:
        out |= translate(E, offset(d, v))
    return frozenset(out)


def check_diagram_counts():
    count = 0
    for n in range(1, 9):
        for D in shapes(n):
            r, c, N = dimensions(D)
            contents = sorted({j - i for i, j in D})
            assert contents == list(range(contents[0], contents[0] + N))   # N_D contents, consecutive
            assert len(D) >= r and len(D) >= c and len(D) >= N                # exponents of eq:modified
            assert connected(D)
            count += 1
    print(f'PASS: connected diagrams occupy N_D consecutive contents and |D| >= r, c, N_D (eq:modified): {count} diagrams')


def check_marks(maxarea=7):
    """Marks against the engine, eq:period, hats, and the local geometry."""
    agree = positive = empty = 0
    for n in range(2, maxarea + 1):
        for E in shapes(n):
            marks = list(legal_marks(E))
            theirs = {(b, v, c) for b, t, c, v, v5 in eng.w_candidates(frozenset(E))}
            assert set(marks) == theirs, sorted(E)
            agree += 1
            N = span(E)
            sw = next(x for x in E if x[1] - x[0] == 0)
            ne = next(x for x in E if x[1] - x[0] == N - 1)
            top_empty = {}
            for W, v, case in marks:
                p = v[1] - v[0]
                if not W:
                    empty += 1
                    vH = (ne[0] - sw[0], ne[1] - sw[1] + 1)
                    vV = (vH[0] - E_STEP[0], vH[1] - E_STEP[1])
                    assert v == (vH if case == 'a' else vV)
                    assert p == N                       # w = 0, so p = N_E - w
                    continue
                positive += 1
                w = span(W)
                top = translate(W, v)
                O, What, Ohat = hats(E, W, v)
                assert w == span(top) and p == N - w                    # eq:period
                assert 0 <= w < p and (0, 0) in W and ne in top and not (W & top)
                assert O == E - W - top and connected(O)
                # eq:hats read off the definition
                periodic = frozenset().union(*(translate(E, (k * v[0], k * v[1]))
                                               for k in range(-3, 4)))
                assert What == (frozenset(x for x in periodic if (x[0] + 1, x[1] + 1) in W)
                                | frozenset(x for x in W if (x[0] + 1, x[1] + 1) in periodic))
                assert Ohat == frozenset(x for x in O if (x[0] + 1, x[1] + 1) in O)
                # local geometry of a positive mark
                contents = {j - i for i, j in O}
                s = min(contents)
                t = max(contents) + 1 - p
                assert contents == set(range(s, p + t))              # the middle occupies [s, p + t - 1]
                assert 1 <= s <= w and 0 <= t < w
                if case in ('c', 'd'):
                    assert t < s
                per_content = Counter(j - i for i, j in E)
                assert per_content[w] == 1 and per_content[p - 1] == 1   # singleton private diagonals
                on_marked = Counter(j - i for i, j in O if (j - i) < w or p <= (j - i) < p + w)
                assert all(c <= 1 for c in on_marked.values())          # one middle cell per marked diagonal
                assert max(span(W), span(What), span(Ohat)) < p         # generator span below p
                for piece in (W, What, Ohat):
                    for k in range(1, 4):
                        assert delta(schur(piece), k * p) == 0 == weighted(schur(piece), k * p)
                assert integer_content(sp.expand(schur(W) * schur(What) * schur(Ohat))) == 1
    assert positive and empty
    print(f'PASS: legal marks agree with the independent engine on {agree} inners (areas 2 to {maxarea}); '
          f'{positive} positive and {empty} empty marks satisfy eq:period, eq:hats, the local geometry, '
          f'and the empty-edge displacements')


def check_compose_against_engine():
    agree = Counter()
    for n in range(2, 6):
        for E in shapes(n):
            for W, v, case in legal_marks(E):
                top = translate(W, v) if W else frozenset()
                p = v[1] - v[0]
                w = span(W) if W else 0
                for a in range(1, 5 if n <= 4 else 4):
                    for D in shapes(a):
                        mine = compose(D, E, W, v, case, require_connected=False)
                        theirs = eng.compose(D, E, W, top, case, v)
                        assert theirs is not None and eng.normalize(mine) == theirs, (E, W, v, case, D)
                        # eq:span
                        if a >= 1 and connected(mine):
                            assert span(mine) == p * span(D) + w
                        agree[case] += 1
    assert set(agree) == {'a', 'b', 'c', 'd'}
    print('PASS: eq:ordinary-offsets and the mixed copy rule (with supplemental copies) agree with the engine; '
          f'eq:span holds; compositions per case {dict(sorted(agree.items()))}')


def weights(f):
    """The set of weights of the monomials of f, with h_j of weight j."""
    gens = sorted(f.free_symbols, key=lambda x: int(x.name[1:]))
    if not gens:
        return {0}
    return {sum(e * int(x.name[1:]) for e, x in zip(m, gens)) for m, c in sp.Poly(f, *gens).terms()}


def key_ribbon(E, W, v):
    O, What, Ohat = hats(E, W, v)
    return E - W - Ohat - translate(What, v)


def check_key_ribbons():
    checked = 0
    for n in range(2, 8):
        for E in shapes(n):
            marks = [(W, v) for W, v, c in legal_marks(E) if c == 'a']
            for W, v in marks:
                p = v[1] - v[0]
                O, What, Ohat = hats(E, W, v)
                A, B, C = schur(W), schur(What), schur(Ohat)
                key = key_ribbon(E, W, v)
                assert len(key) == p and connected(key)
                assert all((i + 1, j + 1) not in E for i, j in key)          # on the southeast boundary
                assert len({j - i for i, j in key}) == p                    # one cell per content: a ribbon
                b = len({i for i, j in key}) - 1
                xi = delta(schur(E), p)
                assert xi == sp.expand((-1) ** b * A * B * C) != 0          # Xi = sigma A B C
                # the top key ribbon, by rotating the whole inner, has the same height
                Er = rotate(E)
                partner = [(W2, v2) for W2, v2, c2 in legal_marks(Er) if c2 == 'a' and v2[1] - v2[0] == p]
                assert len(partner) == 1
                W2, v2 = partner[0]
                b2 = len({i for i, j in key_ribbon(Er, W2, v2)}) - 1
                assert b2 == b
                # deg Xi = |E| - p, by weight
                assert weights(xi) == {len(E) - p}
                checked += 1
    assert checked
    print(f'PASS: bottom key ribbon (p cells, on the southeast boundary, complement W + hatted pieces), '
          f'equal heights top and bottom, Xi = (-1)^b ABC != 0 of weight |E| - p: {checked} ordinary case-(a) marks')


def check_deletion_table_and_remainder():
    cells = ribbons = 0
    for n in range(2, 6):
        for E in shapes(n):
            for W, v, case in legal_marks(E):
                if case != 'a':
                    continue
                p = v[1] - v[0]
                O, What, Ohat = hats(E, W, v)
                A, B, C = schur(W), schur(What), schur(Ohat)
                key = key_ribbon(E, W, v)
                for a in range(1, 5):
                    for D in shapes(a):
                        F = raw_ordinary(D, E, v)
                        # deletion table at a southeast-removable cell
                        for d in D:
                            if (d[0] + 1, d[1]) in D or (d[0], d[1] + 1) in D:
                                continue
                            o = offset(d, v)
                            assert translate(key, o) <= F
                            rest = F - translate(key, o)
                            pieces = []
                            if (d[0], d[1] - 1) not in D and W:
                                pieces.append(translate(W, o))
                            if (d[0] - 1, d[1]) not in D and What:
                                pieces.append(translate(What, (o[0] + v[0], o[1] + v[1])))
                            if (d[0] - 1, d[1] - 1) not in D and Ohat:
                                pieces.append(translate(Ohat, o))
                            base = raw_ordinary(D - {d}, E, v) if len(D) > 1 else frozenset()
                            total = set(base)
                            for piece in pieces:
                                assert not (total & piece)
                                assert not any((x + dx, y + dy) in total for x, y in piece
                                               for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)))
                                total |= piece
                            assert frozenset(total) == rest, (E, W, D, d)
                            cells += 1
                        # eq:ribbon-remainder for every southeast-removable k p-ribbon
                        Fn = compose(D, E, W, v, 'a')
                        outer = {}
                        for k in range(1, a + 1):
                            for rem, hook, ht in removals(D, k):
                                lifted = frozenset().union(*(translate(key, offset(c, v)) for c in hook))
                                outer[(k, lifted)] = rem
                        for k in range(1, a + 1):
                            for rem, hook, ht in removals(Fn, k * p):
                                Dp = outer[(k, hook)]
                                r, c, N = dimensions(D)
                                r2, c2, N2 = dimensions(Dp) if Dp else (0, 0, 0)
                                J = (sp.Integer(1) if not Dp else
                                     schur(compose(Dp, E, W, v, 'a', require_connected=False)))
                                assert schur(rem) == sp.expand(A ** (r - r2) * B ** (c - c2)
                                                                * C ** (N - N2) * J), (E, W, D, k)
                                ribbons += 1
    print(f'PASS: the deletion table at {cells} southeast-removable outer cells (cell sets, pieces disjoint '
          f'and unadjacent) and eq:ribbon-remainder on {ribbons} lifted ribbons')


def check_case_b_reduction():
    count = 0
    for n in range(2, 6):
        for E in shapes(n):
            Et = transpose(E)
            for W, v, case in legal_marks(E):
                if case != 'b':
                    continue
                p = v[1] - v[0]
                partner = [(W2, v2) for W2, v2, c2 in legal_marks(Et) if c2 == 'a' and v2[1] - v2[0] == p]
                assert len(partner) == 1
                W2, v2 = partner[0]
                for a in range(2, 5):
                    for D in shapes(a):
                        F = compose(D, E, W, v, 'b')
                        assert transpose(F) == compose(rotate(D), Et, W2, v2, 'a')   # (D o E)^t = D* o E^t
                        count += 1
    print(f'PASS: (D o_b E)^t = D* o_a E^t, with E^t of case (a): {count} compositions')


def check_covariance_transport():
    """Mark data under antitranspose and rotation, for lem:covariance and its mixed clause."""
    from _weighted_readout import composition_map

    def data(E, W, v, case):
        p = v[1] - v[0]
        O, What, Ohat = hats(E, W, v)
        A, B, C = (schur(X) for X in (W, What, Ohat))
        xi = delta(schur(E), p)
        local = (-1) ** (-v[0]) * A * B * C if case in ('c', 'd') else xi
        theta = sp.cancel(weighted(schur(E), p) / local)
        return p, local, theta

    ordinary = mixed = rotated = 0
    for n in range(2, 6):
        for E in shapes(n):
            for W, v, case in legal_marks(E):
                p, local, theta = data(E, W, v, case)
                Ea = antitranspose(E)
                other = {'a': 'b', 'b': 'a', 'c': 'd', 'd': 'c'}[case]
                partner = [(W2, v2) for W2, v2, c2 in legal_marks(Ea) if c2 == other and v2[1] - v2[0] == p]
                assert len(partner) == 1, (E, case)
                W2, v2 = partner[0]
                p2, local2, theta2 = data(Ea, W2, v2, other)
                for j in range(1, 4):
                    left = composition_map(schur(shapes_h(j)), Ea, W2, v2, other, read_outer=False)
                    right = involution(composition_map(schur(shapes_h(j)), E, W, v, case, read_outer=False))
                    assert left == right                           # Psi' = omega Psi on generators
                if case in ('a', 'b'):
                    assert sp.expand(local2 - (-1) ** (p - 1) * involution(local)) == 0   # xi_b = (-1)^(p-1) omega(xi_a)
                    assert theta2 == -theta                                               # theta_b = -theta_a
                    ordinary += 1
                else:
                    assert sp.expand(local2 - (-1) ** p * involution(local)) == 0          # chi_c = (-1)^p omega(chi_d)
                    assert theta2 == theta                                                 # rho unchanged
                    mixed += 1
                # whole rotation: the chart, its inner and its outer rotate together
                Er = rotate(E)
                rot_case = {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'}[case]
                cand = [(W3, v3) for W3, v3, c3 in legal_marks(Er) if c3 == rot_case and v3[1] - v3[0] == p]
                assert len(cand) == 1
                W3, v3 = cand[0]
                for a in range(1, 4):
                    for D in shapes(a):
                        F = compose(D, E, W, v, case)
                        assert any(rotate(F) == compose(Dp, Er, W3, v3, rot_case) for Dp in (D, rotate(D)))
                        rotated += 1
    print(f'PASS: Phi_b = omega Phi_a omega, xi_b = (-1)^(p-1) omega(xi_a), theta_b = -theta_a on {ordinary} ordinary marks; '
          f'Phi_c = omega Phi_d, chi_c = (-1)^p omega(chi_d), rho unchanged on {mixed} mixed marks; '
          f'whole rotation carries a chart to the chart of the rotated mark on {rotated} compositions')


def shapes_h(j):
    from schur_tools import from_profile
    return from_profile((j,), ())


def check_mixed_boundary():
    """eq:mixed-boundary and the beta-set description in the proof of lem:mixed-vanishing."""
    count = 0
    for n in range(3, 7):
        for E in shapes(n):
            for W, v, case in legal_marks(E):
                if case not in ('c', 'd'):
                    continue
                p = v[1] - v[0]
                w = span(W)
                for a in range(1, 4):
                    for D in shapes(a):
                        F = compose(D, E, W, v, case)
                        Fo = F if case == 'd' else rotate(F)
                        N = span(Fo)
                        bottom = {}
                        for i, j in Fo:
                            bottom[j - i] = max(bottom.get(j - i, i), i)
                        B = {t: bottom[t - 1] - bottom[t] for t in range(1, N)}
                        assert N == p * span(D) + w and 0 < w < p
                        assert set(B.values()) <= {0, 1}
                        assert all(B[t + p] == B[t] for t in range(1, N) if t + p < N)
                        assert B[p] == 0 and B[w] == 1
                        lam = [max(j for a_, j in Fo if a_ == i) + 1 for i in sorted({i for i, j in Fo})]
                        nn = len(lam)
                        X = {lam[i] + nn - 1 - i for i in range(nn)}
                        assert X == {t for t in range(1, N) if B[t] == 1} | {N}
                        assert all(x < p or x - p in X for x in X)          # lambda is a p-core
                        count += 1
    print(f'PASS: eq:mixed-boundary (periodicity, B_p = 0, B_w = 1, N_F = p N_D + w), the beta set, and the '
          f'p-core property on {count} mixed charts')


def boundary_decomposition(D, sign):
    total = 0
    pending = components(D)
    while pending:
        X = pending.pop()
        border = frozenset(x for x in X if (x[0] - sign, x[1] - sign) not in X)
        assert connected(border)
        total += len({i for i, j in border}) - 1
        pending += components(X - border)
    return total


def check_mixed_sign():
    count = 0
    for n in range(1, 8):
        for D in shapes(n):
            nw, se = boundary_decomposition(D, 1), boundary_decomposition(D, -1)
            assert nw == se and (-1) ** nw == mixed_sign(D)
            if not any((i + 1, j) in D and (i, j + 1) in D and (i + 1, j + 1) in D for i, j in D):
                assert nw == dimensions(D)[0] - 1                # a ribbon: (-1)^(r(D) - 1)
            count += 1
    print(f'PASS: n(D) from the northwest and southeast boundary decompositions agree, give the sign '
          f'used by the harness, and equal r(D) - 1 on ribbons: {count} diagrams')


def check_northwest_deletion():
    count = 0
    for n in range(1, 8):
        for D in shapes(n):
            f = schur(D)
            for k in range(1, n + 1):
                total = 0
                for Y in shapes_lib.removable_ribbons(D, k, 'L'):
                    height = len({i for i, j in Y}) - 1
                    rest = D - Y
                    total += (-1) ** height * (schur(normalize(rest)) if rest else 1)
                assert sp.expand(total) == delta(f, k), (D, k)
                count += 1
    print(f'PASS: northwest-removable ribbon deletion gives the same function as eq:mn: {count} (diagram, k) pairs')


def check_hypothesis_five():
    """The displayed 53-cell example satisfies Hypothesis V as well as I to IV."""
    from schur_tools import from_profile
    E = from_profile((4, 5), (1,))
    mark = [(W, v, c) for W, v, c in legal_marks(E) if c == 'a' and v[1] - v[0] == 6]
    assert len(mark) == 1
    W, v, c = mark[0]
    assert span(W) == 2 and len(W) == 2
    assert eng.hyp_V(frozenset(E), W, translate(W, v), 'a')
    print('PASS: the mark of the displayed 53-cell example satisfies Hypothesis V')


def main():
    check_diagram_counts()
    check_marks()
    check_compose_against_engine()
    check_key_ribbons()
    check_deletion_table_and_remainder()
    check_case_b_reduction()
    check_covariance_transport()
    check_mixed_boundary()
    check_mixed_sign()
    check_northwest_deletion()
    check_hypothesis_five()
    print('ALL PASS')


if __name__ == '__main__':
    main()
