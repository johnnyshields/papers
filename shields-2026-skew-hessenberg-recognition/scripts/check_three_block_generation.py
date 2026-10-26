#!/usr/bin/env python3
"""Legal three-block generation from commuting blocks and one rigid merger.

The inner need not be rotation-rigid.  A five-row nonrigid inner has rigid
selected powers by constant-gap substitution and a coprime ribbon-factor
obstruction.  Literal empty-horizontal charts are built independently of the
composition engine.  Large determinants are consistency checks, not the proof
of their equality, which is a formal three-part coarsening identity.
"""
from functools import reduce
from math import gcd
from random import Random
import sympy as sp
from check_three_block_classes import (
    valid, rotate, near, parent, merger, blocks, betas, zero_free,
    schur, sympy_schur, candidates)
from check_literal_charts import cells_of_profile, profile_of_cells
from check_zero_cut_inventory import evaluate


def cells(profile):
    return cells_of_profile(*profile)


def to_profile(shape):
    return profile_of_cells(shape)


def power(e, n):
    return reduce(near, [e] * n)


def word(p):
    r, g = p
    answer = [None] * sum(r)
    end = 0
    for row, gap in zip(r[:-1], g):
        end += row
        answer[end - 1] = gap
    return tuple(answer)


def unword(w):
    assert w and w[-1] is None
    marks = [(i + 1, a) for i, a in enumerate(w) if a is not None]
    ends = [0] + [i for i, _ in marks] + [len(w)]
    p = tuple(b - a for a, b in zip(ends, ends[1:])), tuple(g for _, g in marks)
    assert valid(p)
    return p


def common_root(bs):
    if any(near(a, b) != near(b, a) for a in bs for b in bs):
        return None
    w = word(bs[0])
    for d in range(1, len(w) + 1):
        if len(w) % d == 0 and w == w[:d] * (len(w) // d):
            base = w[:d]
            break
    e = unword(base)
    alpha = tuple(sum(b[0]) // len(base) for b in bs)
    assert all(word(b) == base * a for b, a in zip(bs, alpha))
    assert all(power(e, a) == b for b, a in zip(bs, alpha))
    assert zero_free(e) and len(e[0]) >= 2
    return e, alpha


def empty_horizontal(alpha, e, shift_error=0):
    n, span = len(e[0]), betas(e)[0][0]
    east = (1 - n, span - n + 1 + shift_error)
    north = (-n, span - n)
    outer = cells((alpha, (0,) * (len(alpha) - 1)))
    out = set()
    for i, j in outer:
        origin = (j * east[0] - i * north[0], j * east[1] - i * north[1])
        out.update((r + origin[0], c + origin[1]) for r, c in cells(e))
    if shift_error:
        dr, dc = min(i for i, _ in out), min(j for _, j in out)
        return {(i - dr, j - dc) for i, j in out}
    return to_profile(out)


def formal_three_part(a, b, c):
    h = sp.symbols('x0:' + str(a + b + c + 1))
    return sp.expand(h[a] * h[b] * h[c] - h[a + b] * h[c]
                     - h[a] * h[b + c] + h[a + b + c])


def selected_power_certificate(e, m):
    p = power(e, m)
    assert e == ((3, 4, 3, 6, 4), (1, 1, 1, 1))
    delta = tuple(r - 1 for r in p[0])
    assert sum(delta) == 16 * m - 1
    assert delta[0] == 2 and delta[-1] == 3
    assert delta.count(6) == m - 1
    assert gcd(sum(delta), delta.count(6)) == gcd(15, m - 1)
    assert gcd(15, m - 1) == 1
    # In a nontrivial multipart-inner composition, the outer cell count
    # divides both the total cell count and the multiplicity of label 6.
    assert not any(sum(delta) % d == 0 and delta.count(6) % d == 0
                   for d in range(2, delta.count(6) + 1))
    return p


def main():
    e = ((3, 4, 3, 6, 4), (1, 1, 1, 1))
    other = ((3, 6, 4, 3, 4), (1, 1, 1, 1))
    assert zero_free(e) and schur(e) == schur(other) == sympy_schur(e) == sympy_schur(other)
    assert other not in {e, rotate(e)}
    print('CONTROL: the common inner is not rotation-rigid, so an all-power or part-power hypothesis is genuinely absent.')
    modulus = 2 ** 61 - 1
    rng = Random(917302)
    values = [1] + [rng.randrange(1, modulus) for _ in range(900)]
    total = 0
    for m in (5, 8, 17, 32):
        alpha = (1, 1, m - 2)
        bs = tuple(power(e, a) for a in alpha)
        root, indices = common_root(bs)
        assert (root, indices) == (e, alpha)
        assert merger(bs) == selected_power_certificate(e, m)
        expected = {parent(bs), rotate(parent(bs)), parent(tuple(reversed(bs))),
                    rotate(parent(tuple(reversed(bs))))}
        assert len(expected) == 4
        assert empty_horizontal(alpha, e) == parent(bs)
        assert empty_horizontal(alpha[::-1], e) == parent(tuple(reversed(bs)))
        assert formal_three_part(*alpha) == formal_three_part(*alpha[::-1])
        # Exact finite-field arithmetic checks the determinant consequence.
        assert len({evaluate(p, values, modulus) for p in expected}) == 1
        assert empty_horizontal(alpha, e, 1) != cells(parent(bs))
        print('PASS: total index', m, 'parent rows', len(parent(bs)[0]),
              'cells', sum(parent(bs)[0]), 'four literal chart members; coprime merger certificate.')
        total += 1
    for e0 in (((2, 3), (1,)), ((9, 6, 6), (4, 4))):
        for alpha in (((1, 1, 2), (1, 2, 3), (2, 1, 2)) if len(e0[0]) == 2 else ((1, 1, 2),)):
            bs = tuple(power(e0, a) for a in alpha)
            assert common_root(bs) == (e0, alpha)
            assert empty_horizontal(alpha, e0) == parent(bs)
            # On these smaller examples the full integer cut classifier agrees.
            recovered, _ = candidates(bs)
            expected = {parent(bs), rotate(parent(bs)), parent(tuple(reversed(bs))),
                        rotate(parent(tuple(reversed(bs))))}
            assert recovered == expected
            total += 1
    print('PASS:', total, 'chart/class controls, including non-Hessenberg inners and palindromic outers.')
    print('CONTROL: perturbing the east displacement rejects all four large chart identities.')
    print('ALL PASS')


if __name__ == '__main__':
    main()
