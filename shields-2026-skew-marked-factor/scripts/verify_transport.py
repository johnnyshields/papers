"""Check ordinary mark uniqueness, the literal gauge, and mixed annihilation."""

from collections import defaultdict

from schur_tools import (antitranspose, compose, decode, delta, lambda_mu, legal_marks,
                         rotate, schur, shapes)


def main():
    atlas = mixed = derivatives = gauges = 0
    ordinary_records = defaultdict(list)
    outers = [D for a in range(2, 5) for D in shapes(a)]
    for a in range(2, 7):
        for E in shapes(a):
            marks = list(legal_marks(E))
            by_period = defaultdict(list)
            for W, v, case in marks:
                p = v[1] - v[0]
                by_period[p].append((W, v, case))
                if case not in ('c', 'd'):
                    continue
                for D in outers:
                    F = compose(D, E, W, v, case)
                    oriented = F if case == 'd' else rotate(F)
                    lam, mu = lambda_mu(oriented)
                    n = len(lam)
                    beta = {lam[i] + n - 1 - i for i in range(n)}
                    assert all(x < p or x - p in beta for x in beta)
                    P = schur(F)
                    for k in range(p, len(F) + 1, p):
                        assert delta(P, k) == 0
                        derivatives += 1
                    try:
                        decode(P, p)
                    except ValueError:
                        pass
                    else:
                        raise AssertionError('Mixed chart passed the ordinary decoder')
                    mixed += 1
            for p, entries in by_period.items():
                atlas += 1
                assert len(entries) <= 2
                if len(entries) == 2:
                    assert {case for W, v, case in entries} == {'a', 'b'}
                    wa, va, _ = next(t for t in entries if t[2] == 'a')
                    wb, vb, _ = next(t for t in entries if t[2] == 'b')
                    assert va == (vb[0] + 1, vb[1] + 1)
                    for D in outers:
                        assert compose(D, E, wa, va, 'a') == compose(antitranspose(D), E, wb, vb, 'b')
                        gauges += 1
                # Within this box, the inner/period/type data in the theorem
                # are compared to the reconstructed polynomial, not to a key engine.
                if len({i for i, j in E}) == 2:
                    for W, v, case in entries:
                        if case in ('a', 'b'):
                            for D in outers:
                                F = compose(D, E, W, v, case)
                                ordinary_records[(p, schur(F))].append((E, D, case))
    equal_pairs = 0
    for group in ordinary_records.values():
        E0, D0, c0 = group[0]
        Q0 = schur(D0 if c0 == 'a' else antitranspose(D0))
        for E, D, case in group[1:]:
            assert E == E0 or E == rotate(E0)
            assert schur(D if case == 'a' else antitranspose(D)) == Q0
            equal_pairs += 1
    assert atlas and mixed and gauges and equal_pairs
    print('Inner-period mark atlases:', atlas)
    print('Literal ordinary gauge pairs:', gauges)
    print('Mixed charts:', mixed, '; vanishing derivatives:', derivatives)
    print('Equal-polynomial two-row comparisons:', equal_pairs)
    print('CONTROL: all mixed charts rejected by ordinary decoder')
    print('ALL PASS')


if __name__ == '__main__':
    main()
