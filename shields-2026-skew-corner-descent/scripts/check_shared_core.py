#!/usr/bin/env python3
"""Common-core divisibility, as a matrix identity and as a statement on diagrams.

Paper section `sec:corner-data` (Common-core divisibility); target
`lem:shared-core`.

Part 1 expands the four block determinants of the lemma over generic
symbolic blocks, with the zero blocks of the statement, and divides the cross
difference by det C exactly.  The compatible-blocks reading is the one forced by
the lemma's squareness: M11 is the full matrix, M10 keeps the top and middle
block rows and one column of the right block, M01 keeps one top row, and M00
keeps both.  Every row and column choice is tried.  Control: with the zero
blocks replaced by generic entries the divisibility fails.

Part 2 builds actual diagrams.  For connected U and connected L, R joined by
empty horizontal or vertical joins at the two content ends, the exact
polynomial K_U divides s_{ULR} s_U - s_{UL} s_{UR}.  Control: two extensions at
the same end do not divide.
"""
from collections import Counter
from itertools import product
import sympy as sp
from diagram_tools import (canonical, connected_skew, corner_cofactor, schur,
                           shapes_of_area, span, translate)


def block(name, r, c):
    return sp.Matrix(r, c, lambda i, j: sp.Symbol(f'{name}{i}{j}'))


def cross_difference(a, k, b, ri, cj, zeros=True):
    A, R, T = block('A', a, a-1), block('R', a, k), block('T', a, b+1)
    C, S, B = block('C', k, k), block('S', k, b+1), block('B', b, b+1)
    if zeros:
        Z = lambda r, c: sp.zeros(r, c)
        lower_left = (Z(k, a-1), Z(b, a-1), Z(b, k))
    else:
        lower_left = (block('Y', k, a-1), block('Y2', b, a-1), block('Y3', b, k))
    M11 = sp.Matrix(sp.BlockMatrix([[A, R, T], [lower_left[0], C, S], [lower_left[1], lower_left[2], B]]))
    t, s = T[:, cj], S[:, cj]
    M10 = sp.Matrix(sp.BlockMatrix([[A, R, t], [lower_left[0], C, s]]))
    r, q, z = R[ri, :], T[ri, :], T[ri, cj]
    M00 = sp.Matrix(sp.BlockMatrix([[r, sp.Matrix([[z]])], [C, s]]))
    M01 = sp.Matrix(sp.BlockMatrix([[r, q], [C, S], [lower_left[2], B]]))
    difference = sp.expand(M11.det()*M00.det()-M10.det()*M01.det())
    return difference, sp.expand(C.det())


def divisible(f, g):
    if f == 0:
        return True
    gens = sorted(f.free_symbols | g.free_symbols, key=str)
    _, remainder = sp.div(sp.Poly(f, *gens, domain='QQ'), sp.Poly(g, *gens, domain='QQ'))
    return remainder.is_zero


def join(first, second, kind):
    """Empty horizontal or vertical join: the southwest cell of the second diagram
    is immediately east (H) or north (V) of the northeast cell of the first."""
    ne = max(first, key=lambda z: z[1]-z[0])
    sw = min(second, key=lambda z: z[1]-z[0])
    target = (ne[0], ne[1]+1) if kind == 'H' else (ne[0]-1, ne[1])
    out = first | translate(second, (target[0]-sw[0], target[1]-sw[1]))
    assert connected_skew(out)
    assert span(out) == span(first)+span(second)
    return canonical(out)


def dict_divisible(f, g):
    if not f:
        return True
    top = max([j for mon in list(f)+list(g) for j in mon], default=0)
    hs = sp.symbols('h1:%d' % (top+2))
    def expression(d):
        e = 0
        for mon, c in d.items():
            term = c
            for j in mon:
                term *= hs[j-1]
            e += term
        return sp.expand(e)
    return divisible(expression(f), expression(g))


def sub(f, g):
    out = dict(f)
    for mon, c in g.items():
        out[mon] = out.get(mon, 0)-c
        if not out[mon]:
            del out[mon]
    return out


def mul(f, g):
    from diagram_tools import multiply
    return multiply(f, g)


def main():
    counts = Counter()
    for a, k, b in [(2, 1, 1), (2, 2, 1), (3, 1, 1), (2, 1, 2)]:
        for ri, cj in product(range(a), range(b+1)):
            difference, dc = cross_difference(a, k, b, ri, cj)
            assert divisible(difference, dc), (a, k, b, ri, cj)
            counts['generic block identities'] += 1
    difference, dc = cross_difference(2, 1, 1, 0, 0, zeros=False)
    assert not divisible(difference, dc)
    counts['nonzero-block control'] += 1

    units = [G for n in range(1, 5) for G in shapes_of_area(n)]
    extensions = [G for n in range(1, 4) for G in shapes_of_area(n)]
    nontrivial = nonzero = 0
    for U in units:
        K = corner_cofactor(U)
        for L, R in product(extensions, repeat=2):
            for jl, jr in product('HV', repeat=2):
                UL, UR = join(L, U, jl), join(U, R, jr)
                ULR = join(L, UR, jl)
                diff = sub(mul(schur(ULR), schur(U)), mul(schur(UL), schur(UR)))
                assert dict_divisible(diff, K), (U, L, R, jl, jr)
                counts['diagram divisibilities'] += 1
                nontrivial += K != {(): 1}
                nonzero += bool(diff)
    assert nontrivial and nonzero
    counts['nontrivial divisor'] = nontrivial
    counts['nonzero cross difference'] = nonzero
    # Control: two extensions at the same content end are not covered by the lemma.
    failures = 0
    for U in units:
        K = corner_cofactor(U)
        if K == {(): 1}:
            continue
        for R1, R2 in product(extensions, repeat=2):
            for j1, j2 in product('HV', repeat=2):
                UR1, UR2 = join(U, R1, j1), join(U, R2, j2)
                UR12 = join(UR1, R2, j2)
                diff = sub(mul(schur(UR12), schur(U)), mul(schur(UR1), schur(UR2)))
                failures += not dict_divisible(diff, K)
    assert failures
    counts['same-end control failures'] = failures
    print(dict(counts))
    print('check_shared_core: PASS')


if __name__ == '__main__':
    main()
