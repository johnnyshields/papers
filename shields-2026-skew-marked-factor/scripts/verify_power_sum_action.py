"""Compare power-sum differentiation with literal ribbon deletion and composition."""

import sympy as sp

from schur_tools import (compose, connected, delta, dimensions, hats, legal_marks, primitive,
                         removals, schur, shapes, translate)


def modified(D, E, W, v, A, B, C):
    if not D:
        return sp.Integer(1)
    r, c, M = dimensions(D)
    F = compose(D, E, W, v, 'a', require_connected=False)
    return sp.expand(A ** (len(D) - r) * B ** (len(D) - c)
                     * C ** (len(D) - M) * schur(F))


def main():
    mn_count = norm_count = geometry_count = 0
    empty_control = 0
    for n in range(1, 8):
        for D in shapes(n):
            P = schur(D)
            assert primitive(P) == P
            for k in range(1, n + 1):
                mn = sum((-1) ** ht * schur(R) for R, hook, ht in removals(D, k))
                assert delta(P, k) == sp.expand(mn)
                mn_count += 1
    for n in range(2, 6):
        for E in shapes(n):
            for W, v, case in legal_marks(E):
                if case != 'a':
                    continue
                p = v[1] - v[0]
                O, What, Ohat = hats(E, W, v)
                A, B, C = schur(W), schur(What), schur(Ohat)
                Xi = delta(schur(E), p)
                key = E - W - Ohat - translate(What, v)
                assert connected(key) and len(key) == p
                key_height = len({i for i, j in key}) - 1
                for a in range(2, 5):
                    for D in shapes(a):
                        F = compose(D, E, W, v, 'a')
                        MD = modified(D, E, W, v, A, B, C)
                        for k in range(1, a + 1):
                            outer_removals = list(removals(D, k))
                            expected = Xi ** k * sum((-1) ** ht * modified(R, E, W, v, A, B, C)
                                                    for R, hook, ht in outer_removals)
                            assert delta(MD, k * p) == sp.expand(expected), (D, E, W, k)
                            actual_ribbons = {hook: ht for rem, hook, ht in removals(F, k * p)}
                            predicted_ribbons = {}
                            for rem, hook, ht in outer_removals:
                                lifted = frozenset().union(*(translate(key, ((j - i) * v[0] + i,
                                                                           (j - i) * v[1] + i))
                                                             for i, j in hook))
                                predicted_ribbons[lifted] = k * key_height + ht
                            assert actual_ribbons == predicted_ribbons, (D, E, W, k)
                            geometry_count += len(actual_ribbons)
                            norm_count += 1
                if W:
                    assert modified(frozenset(), E, W, v, A, B, C) != schur(W)
                    empty_control += 1
    assert empty_control
    print('Murnaghan--Nakayama comparisons:', mn_count)
    print('Modified-composition action comparisons:', norm_count)
    print('Literal lifted ribbons and heights:', geometry_count)
    print('Geometric-empty/algebraic-unit controls:', empty_control)
    print('ALL PASS')


if __name__ == '__main__':
    main()
