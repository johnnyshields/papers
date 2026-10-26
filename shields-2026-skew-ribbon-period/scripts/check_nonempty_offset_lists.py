r"""Paper section `app:aligned` (prop:noncell-realization, eq:capped-core-quotient).

Offset version of the residue claim for nonempty fine marks, and the reason it is not needed at
total offset u = 0.  For a legal mark eta of period q and width v on a small inner and a connected
J of span R, E = J o_eta U has span R q + v (the `composedSpan` of the chart score).  Asserted on
the census of inners up to 9 cells, outers up to 4 cells:

  * v = 0 exactly for the empty mark; then span E = R q and the residue class 0 mod q of the lists
    of E is q X_J (resp. q Y_J) exactly, the claim behind `ResidueData`;
  * v > 0 forces span E = R q + v != R q, so `ResidueData.spanE` is unavailable and the offset
    reading is a different statement;
  * at a positive coincident mark of case (a) (phases s = t = tau, 0 < tau < v) the offset class
    rho = tau satisfies {(x - tau)/q : x in X_E, x = tau mod q} = X_J and {(y - tau)/q : ...} = Y_J
    exactly in the ordinary-(a) reading.  Other physical readings must carry their prescribed
    rotation or outer involution; no identity with an unchanged outer is inferred from a gauge;
  * for distinct-phase positive marks, the checked configurations do not recover both outer
    lists from any one common residue rho; the coincident hypothesis is load-bearing;
  * supplied three-fold empty chains, allowing half-turns of their inner factors, retain the
    zero-residue list identity.  At total width u=0, the reassociation equation u=v+d*uprime
    forces both lower widths to vanish.

Two actual positive coincident marks, with periods 4 and 5, width 3 and phase 1, test full
rotation.  The transported phase is 2 and the quotient is rotated; both list identities are
asserted there, and keeping the old phase is rejected.  These supplied-composition checks do
not execute the fresh-minimum recursion.  Positive-width literal realization uses the paper's
matched-window induction and private endpoint inverse.
"""
import random
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from _gluing_common import (compose, intersection_mark, is_connected_skew, normalize,
                           rotate, rotated_mark, span)  # noqa: E402
from _mark_builders import betas, diagrams, marks, phases  # noqa: E402
from check_empty_source_lists import compose_empty, random_skew  # noqa: E402
from check_empty_source_lists import betas as cbetas  # noqa: E402
from check_empty_source_lists import is_skew_connected, span as cspan  # noqa: E402
from check_nested_residue_lists import rot  # noqa: E402


def klass(L, q, a):
    return sorted((x - a) // q for x in L if (x - a) % q == 0)


def _check_positive_rotation():
    fixtures = (
        ([7, 6, 5, 3, 2], [6, 4, 2, 1, 0], (-2, 2), 4),
        ([8, 6, 3], [5, 1, 0], (-1, 4), 5),
    )
    J = normalize(frozenset({(0, 0), (0, 1), (-1, 1)}))
    for X, Y, displacement, q in fixtures:
        U = normalize(frozenset((i, c + i) for i, (x, y) in enumerate(zip(X, Y))
                                for c in range(y, x)))
        eta = intersection_mark(U, displacement)
        assert (eta.case, eta.period, eta.width, phases(eta)) == ('a', q, 3, (1, 1))
        transported = rotated_mark(eta)
        assert phases(transported) == (2, 2)
        E = compose(J, eta)
        reflected = rotate(E)
        assert reflected == compose(rotate(J), transported)
        XJ, YJ = betas(J)
        XE, YE = betas(E)
        assert klass(XE, q, 1) == sorted(XJ) and klass(YE, q, 1) == sorted(YJ)
        XJr, YJr = betas(rotate(J))
        XEr, YEr = betas(reflected)
        rho = phases(transported)[0]
        assert rho == eta.width - phases(eta)[0]
        assert klass(XEr, q, rho) == sorted(XJr) and klass(YEr, q, rho) == sorted(YJr)
        assert klass(XEr, q, 1) != sorted(XJr) or klass(YEr, q, 1) != sorted(YJr)
    print('positive coincident phase reflection: both quotient lists recover at the transported phase')


def main():
    _check_positive_rotation()
    outers = list(diagrams(4, 2))
    n_empty = n_pos_a = n_dist = 0
    for E in diagrams(9, 2):
        for mk in marks(E):
            q, v = mk.period, mk.width
            s, t = phases(mk)
            for J in outers:
                try:
                    G = compose(J, mk)
                except AssertionError:
                    continue
                if not is_connected_skew(G):
                    continue
                R = span(J)
                X, Y = betas(G)
                XJ, YJ = betas(J)
                assert span(G) == R * q + v
                if v == 0:
                    assert (s, t) == (0, 0)
                    assert klass(X, q, 0) == sorted(XJ) and klass(Y, q, 0) == sorted(YJ)
                    n_empty += 1
                    continue
                assert span(G) != R * q
                if s == t and mk.case == 'a':
                    assert 0 < s < v
                    assert klass(X, q, s) == sorted(XJ) and klass(Y, q, s) == sorted(YJ)
                    n_pos_a += 1
                elif s != t:
                    ax = {a for a in range(q) if klass(X, q, a) == sorted(XJ)}
                    ay = {a for a in range(q) if klass(Y, q, a) == sorted(YJ)}
                    assert not (ax & ay), (sorted(E), mk.case, J)
                    n_dist += 1
    assert n_empty > 1000 and n_pos_a > 50 and n_dist > 100, (n_empty, n_pos_a, n_dist)

    rng = random.Random(7)
    chains = 0
    for _ in range(12000):
        J = random_skew(rng, rng.randint(1, 3), 3)
        Us = [random_skew(rng, rng.randint(1, 3), 2) for _ in range(3)]
        if any(len(U) < 2 for U in Us):
            continue
        E, q = J, 1
        for U in Us:
            Up = U if rng.random() < 0.5 else rot(U)
            E, qi = compose_empty(E, Up)
            if not is_skew_connected(E):
                break
            q *= qi
        else:
            XJ, YJ = cbetas(J)
            XE, YE = cbetas(E)
            assert cspan(E) == cspan(J) * q
            assert klass(XE, q, 0) == sorted(XJ) and klass(YE, q, 0) == sorted(YJ)
            chains += 1
    assert chains > 100, chains
    print(f"ok: {n_empty} empty, {n_pos_a} coincident (a), {n_dist} distinct-phase, {chains} chains")


if __name__ == "__main__":
    main()
