#!/usr/bin/env python3
"""Check cut/contract extremes, literal split positions, and ribbon substitution."""
from itertools import product
from profile_tools import (add, component, compositions, concat, family,
                           hessenberg, inner, monomial, mul, near, power,
                           rotate, scale, schur)


def coarsen(alpha):
    for sizes in compositions(len(alpha)):
        out, pos = [], 0
        for k in sizes:
            out.append(sum(alpha[pos:pos+k]))
            pos += k
        yield tuple(out)


def ribbon(alpha):
    out = {}
    for beta in coarsen(alpha):
        out = add(out, monomial(beta, (-1)**(len(alpha)-len(beta))))
    return out


def main():
    readings = assembly = equalities = 0
    # Equal endpoints, unequal endpoints, repeated gaps, and a merger row
    # numerically equal to an internal row are all represented.
    inners = [inner(g, 1) for g in ((1,), (1, 2), (1, 1), (1, 2, 3, 1), (1, 3, 2))]
    for E in inners:
        K = len(E[1])
        for M in range(1, 5):
            for beta in compositions(M):
                for flips in product((False, True), repeat=len(beta)):
                    blocks = [rotate(power(E, b)) if f else power(E, b)
                              for b, f in zip(beta, flips)]
                    H = C = blocks[0]
                    product_poly = hessenberg(blocks[0])
                    for block in blocks[1:]:
                        H = concat(H, block)
                        C = near(C, block)
                        product_poly = mul(product_poly, hessenberg(block))
                    # This is the exact ordered split test, not recognition
                    # of seam rows from their numerical length.
                    starts = [1+K*sum(beta[:j]) for j in range(1, len(beta))]
                    assert starts == [sum(len(b[0])-1 for b in blocks[:j])+1
                                      for j in range(1, len(blocks))]
                    if C == power(E, M):
                        assert H == family(E, beta)
                        assembly += 1
                    if C == rotate(power(E, M)):
                        assert rotate(H) == family(E, beta[::-1])
                        assembly += 1
                    if len(H[0]) <= 9:
                        f = schur(H)
                        n, cuts = len(H[0]), len(beta)-1
                        assert component(f, n) == product_poly
                        assert component(f, n-cuts) == scale(hessenberg(C), (-1)**cuts)
                        readings += 1
    for E in inners[:3]:
        for M in range(1, 5):
            words = list(compositions(M))
            fs = {a: schur(family(E, a)) for a in words}
            rs = {a: ribbon(a) for a in words}
            for a in words:
                substituted = {}
                for b in coarsen(a):
                    term = {(): (-1)**(len(a)-len(b))}
                    for size in b:
                        term = mul(term, hessenberg(power(E, size)))
                    substituted = add(substituted, term)
                assert substituted == fs[a]
                for b in words:
                    assert (fs[a] == fs[b]) == (rs[a] == rs[b])
                    equalities += 1
    print(f"Cut/contract determinant extremes: {readings} PASS")
    print(f"Compatible literal assemblies: {assembly} PASS")
    print(f"Ribbon substitution equality comparisons: {equalities} PASS")
    print("ALL PASS")


if __name__ == '__main__':
    main()
