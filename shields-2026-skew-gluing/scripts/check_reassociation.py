#!/usr/bin/env python3
"""Reassociation through a coarse mark, and the antitransposition gauge.

Checks, on finite ranges, the reassociation identity of lem:gluing-aligned
(eq:gluing-reassociation) and the gauge identity eq:gluing-gauge that its
proof uses.

For every connected inner E, every legal mark omega on E (the empty horizontal
mark included), every connected outer V and every legal mark eta on
U = V o_omega E whose displacement has content a*q, with q the period of omega,
the lemma asserts a legal mark mu on V and gamma in {id, AT} with

    C o_eta U = (gamma(C) o_mu V) o_omega E     for every connected C,

gamma = id unless mu is empty.  Here mu ranges over every legal mark on V and
over the two edge readings of V; the vertical reading is a change of
coordinates rather than a legal mark, so only the offset formula composes
through it.  The identity is tested on every connected C of at most CMAX cells,
composition always by adjacency propagation, and the offset formula is required
to agree wherever the mark is legal.

Controls: leaving C unchanged with the horizontal reading fails on an instance;
rotating C on the left side alone empties a working set; transposition in
place of AT breaks the gauge.
"""
import check_mark_locality as L
import check_gcd_fold_sweep as R
import verify_common_factor_graphs as V

normalize, content, span = V.normalize, V.content, V.span
AT = V.antitranspose


def edge_marks(X):
    """The horizontal and vertical edge readings of X as (mark, is_legal_mark)."""
    horizontal = V.empty_mark(X)
    i, j = horizontal.displacement
    vertical = V.Mark(normalize(X), frozenset(), frozenset(), 'b', (i - 1, j - 1))
    return horizontal, vertical


def through(C, mark):
    """C composed with the mark, by offsets; by adjacency too where the mark is legal."""
    out = V.compose_by_offsets(C, mark)
    if V.legal(mark):
        assert out == V.compose(C, mark)
    return out


def coarse_marks(U):
    return L.legal_marks(U) + [V.empty_mark(U)]


def outers(limit):
    return [normalize(S) for k in range(1, limit + 1) for S in R.shapes(k)]


def instances(emax, vmax, umax):
    Vs = outers(vmax)
    for E in outers(emax):
        if len(E) < 2:
            continue
        for omega in L.legal_marks(E) + [V.empty_mark(E)]:
            q = omega.period
            if q <= 0:
                continue
            for Vo in Vs:
                U = V.compose(Vo, omega)
                if len(U) > umax:
                    continue
                for eta in coarse_marks(U):
                    if eta.period % q:
                        continue
                    a = eta.period // q
                    b = span(Vo) - a
                    assert b >= 0 and a > b, (sorted(E), sorted(Vo), a, b)
                    yield E, omega, Vo, U, eta, b


def working_pairs(E, omega, Vo, U, eta, Cs, twist=lambda C: C):
    lhs = [V.compose(twist(C), eta) for C in Cs]
    h, v = edge_marks(Vo)
    mus = L.legal_marks(Vo) + [h, v]
    pairs = []
    for mu in mus:
        for name, gamma in (('id', lambda C: C), ('AT', AT)):
            if all(through(through(gamma(C), mu), omega) == left
                   for C, left in zip(Cs, lhs)):
                pairs.append((mu, name))
    return pairs, h, v


def check_reassociation(emax, vmax, cmax, umax):
    Cs = outers(cmax)
    count = mixed = zero = alt = 0
    fired_unchanged = fired_twist = 0
    tw = lambda C: normalize(frozenset((-i, -j) for i, j in C))
    for E, omega, Vo, U, eta, b in instances(emax, vmax, umax):
        pairs, h, v = working_pairs(E, omega, Vo, U, eta, Cs)
        assert pairs, ("no (mu, gamma)", sorted(E), sorted(Vo), eta.case, eta.displacement)
        empty = lambda mu: not mu.lower
        assert any(name == 'id' or empty(mu) for mu, name in pairs), \
            ("gamma = AT with a nonempty mu only", sorted(E), sorted(Vo))
        for mu, name in pairs:
            if name == 'AT':
                assert empty(mu)
                # The gauge: AT(C) through the horizontal reading is C through the vertical one.
                for C in Cs:
                    assert through(AT(C), h) == through(C, v)
        count += 1
        mixed += omega.case in 'cd'
        zero += b == 0
        alt += any(name == 'AT' for _, name in pairs)
        # Unchanged outer through the horizontal reading.
        plain = all(through(through(C, h), omega) == V.compose(C, eta) for C in Cs)
        fired_unchanged += not plain
        if not working_pairs(E, omega, Vo, U, eta, Cs, tw)[0]:
            fired_twist += 1
    assert count and fired_unchanged, "unchanged-outer control did not fire"
    assert fired_twist, "left-rotation control did not fire"
    print(f"reassociation: {count} (inner, mark, outer, coarse mark) instances, "
          f"{mixed} on mixed inner marks, {zero} at width zero; a working pair uses gamma = AT on "
          f"{alt} instances; unchanged outer fails on {fired_unchanged}; "
          f"left rotation empties {fired_twist}")


def check_gauge(gmax):
    """eq:gluing-gauge on every pair of ordinary marks of one inner differing by e."""
    doubles = fired = 0
    for E in outers(gmax):
        marks = L.legal_marks(E)
        for ma in marks:
            for mb in marks:
                if ma.case == 'a' and mb.case == 'b' and (ma.displacement[0] - mb.displacement[0],
                             ma.displacement[1] - mb.displacement[1]) == (1, 1):
                    doubles += 1
                    for D in outers(3):
                        assert V.compose(D, ma) == V.compose(AT(D), mb)
                        T = V.transpose(D)
                        fired += V.compose(D, ma) != V.compose(T, mb)
    assert doubles and fired, "gauge control did not fire"
    print(f"gauge: {doubles} case-(a)/(b) doubles; transposition in place of AT fails {fired} times")


def main():
    emax, vmax, cmax, umax, gmax = 6, 3, 4, 20, 9
    print(f"ranges: inner <= {emax} cells, fine outer <= {vmax}, coarse outer <= {cmax}, "
          f"composite <= {umax}; gauge doubles on inners <= {gmax}")
    check_gauge(gmax)
    check_reassociation(emax, vmax, cmax, umax)
    print("ALL PASS")


if __name__ == '__main__':
    main()
