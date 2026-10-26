#!/usr/bin/env python3
"""Check balanced terminal gaps and second-subdiagonal indices of E(g,p)."""
from itertools import product
from profile_tools import betas, board, excesses, inner, power


def main():
    tested = 0
    for K in range(1, 6):
        for g in product(range(1, 5), repeat=K):
            for p in range(1, 5):
                E = inner(g, p)
                rows, gaps = E
                assert all(0 < q < min(rows[i], rows[i+1]) for i, q in enumerate(gaps))
                X, Y = betas(E)
                assert X[0]-X[1] == Y[-2] == p
                assert set(X).isdisjoint(Y)
                assert all(board(E)[i][i-2] == -p for i in range(2, len(rows)))
                for m in (1, 2, 3):
                    D = power(E, m)
                    assert len(D[0]) == m*K+1 and D[1] == g*m
                    assert betas(D)[0][0] == m*X[0]
                    e = excesses(D)
                    expected = tuple(2*p if i and i < m*K and i % K == 0 else p
                                     for i in range(m*K+1))
                    assert e == expected == expected[::-1]
                tested += 1
    E = inner((1, 3, 2), 1)
    assert E == ((2, 5, 6, 3), (1, 3, 2))
    assert betas(E) == ((10, 9, 7, 3), (8, 4, 1, 0))
    print(f"Balanced geometry and power excesses: {tested} legal inners PASS")
    print("ALL PASS")


if __name__ == '__main__':
    main()
