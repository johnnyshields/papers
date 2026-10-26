r"""Paper section `sec:extraction` (Recovering ordinary factors).

The irreducibility input of `thm:extraction` and `rt:mixed-readout`: a connected
skew Schur function is irreducible over \(\Q[h_1,h_2,\ldots]\) (the cited
corrigendum), and a factor of degree below \(|E|\) is therefore coprime to it.
The paper consumes this to read the reduced numerator of `eq:ratio` and of
`eq:mixed-readout`, so it is checked here on every connected diagram of up to
`--max-area` cells (default 9), by SymPy's exact factorization over the
rationals, and its consumption is checked on every legal mark: the local
factor \(\Xi\) (ordinary) or \(\rho\chi\) (mixed) has degree \(|E|-p\) and is
coprime to \(s_E\), so \(\gcd(U,T)\) cancels exactly \(\Xi\).  The connectedness
hypothesis is shown load-bearing: a disconnected union of two diagrams is a
product and is reducible.
"""

import argparse

import sympy as sp

from schur_tools import delta, hats, legal_marks, schur, shapes, translate
from _weighted_readout import weighted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-area', type=int, default=9)
    args = parser.parse_args()
    count = 0
    for n in range(1, args.max_area + 1):
        for D in shapes(n):
            content, factors = sp.factor_list(schur(D))
            assert len(factors) == 1 and factors[0][1] == 1, (sorted(D), factors)
            count += 1
        print(f'  area {n}: {count} cumulative', flush=True)
    print(f'PASS: s_D is irreducible over Q[h_1, h_2, ...] for all {count} connected diagrams '
          f'of at most {args.max_area} cells')

    # Connectedness is necessary: a product of two skew functions is reducible.
    for D1 in shapes(2):
        for D2 in shapes(2):
            _, factors = sp.factor_list(sp.expand(schur(D1) * schur(D2)))
            assert sum(m for f, m in factors) == 2
    print('CONTROL: a disconnected union (a product of two connected functions) is reducible')

    # The consumption: the local factor is coprime to s_E, so the reduced numerator is s_E.
    marks = 0
    for n in range(2, 8):
        for E in shapes(n):
            sE = schur(E)
            for W, v, case in legal_marks(E):
                p = v[1] - v[0]
                O, What, Ohat = hats(E, W, v)
                A, B, C = schur(W), schur(What), schur(Ohat)
                if case in ('a', 'b'):
                    local = delta(sE, p)
                else:
                    local = weighted(sE, p)
                    rho = abs(sp.Poly(local, *sorted(local.free_symbols,
                                                     key=lambda x: int(x.name[1:])), domain=sp.ZZ).content())
                    local = sp.expand(local / rho)           # chi, with rho split off
                    assert rho * local == weighted(sE, p)
                weights = {sum(e * int(x.name[1:]) for e, x in zip(m, sorted(
                    local.free_symbols, key=lambda y: int(y.name[1:]))))
                    for m, c in sp.Poly(local, *sorted(local.free_symbols,
                                                       key=lambda y: int(y.name[1:]))).terms()} \
                    if local.free_symbols else {0}
                assert weights == {n - p}
                assert sp.gcd(sE, local) == 1
                marks += 1
    print(f'PASS: gcd(s_E, local factor) = 1, local factor of weight |E| - p, on {marks} legal marks '
          f'of inners of 2 to 7 cells')
    print('ALL PASS')


if __name__ == '__main__':
    main()
