r"""Paper section `app:aligned` (`lem:conormal-caps`, `eq:capped-core-quotient`): the transported inner.

Two geometric mechanisms used by the matched-window argument.

For the supplied nested empty-composite model, let C_Z(D) denote composition of the outer D
through the horizontal empty mark on Z.  Check both-end list inclusions for
E1 = C_Z(C_W(J)) against U = C_Z(W), and for E2 = C_Z(rot(C_W(J))) against
Ustar = C_Z(rot(W)).  The original U and its whole rotation need not work in the latter
model.  These examples do not test the original source-minimal aligned gate and therefore
do not enlarge the transport class in lem:conormal-caps.

Independently, use the full legal-mark composition model for ordinary cases (a) and (b),
including the canonical horizontal empty reading.  Compare every actual private diagonal
interval with the copy-origin formula and recover both quotient endpoints.  Reconstruct
the first and last quotient qprime windows from the corresponding d*qprime source windows.
The checks retain common betas; they do not construct fresh minima or discharge the full
recursive comparison.  The exact box is inner sizes 2..8, outer sizes 2..4, every private
residue, and every quotient end-window length 1..outer span.
"""
import random

from check_end_window_lists import compose
from check_row_probe_caps import betas, connected, is_skew, legal_marks, normalize, random_skew
import _gluing_common as charts
from _mark_builders import diagrams as all_diagrams, marks as all_marks


def rot(S):
    return normalize({(-a, -b) for (a, b) in S})


def win(E, U):
    xE, zE = betas(E)
    xU, zU = betas(U)
    q = xU[0]
    return all(x in set(xU) for x in xE if 0 < x < q) and set(zU) <= set(zE)


def bw(E, U):
    return win(E, U) and win(rot(E), rot(U))


def empty_v(Z):
    for w, v, ph in legal_marks(Z):
        if w == 0:
            return v
    return None


def comp(Z, V):
    v = empty_v(Z)
    return None if v is None else compose(V, Z, v)


def _intervals(D):
    result = {}
    for i, j in D:
        c = charts.content((i, j))
        if c in result:
            lo, hi = result[c]
            result[c] = min(lo, i), max(hi, i)
        else:
            result[c] = i, i
    return result


def _recover_private(case, a, native, j, actual):
    lo, hi = actual
    lam, mu = native
    if case == 'a':
        return lo - j * a - lam, hi - j * a - mu
    assert case == 'b'
    return j * a + mu - hi, j * a + lam - lo


def _check_private_windows():
    outers = [(D, _intervals(D)) for D in all_diagrams(4)]
    identities = positive = vertical = windows = 0
    for U in all_diagrams(8):
        native = _intervals(U)
        for mark in all_marks(U):
            if mark.case not in 'ab':
                continue
            assert charts.legal(mark)
            d, v = mark.period, mark.width
            a = mark.displacement[0]
            assert native[v][0] == native[v][1]
            for D, coarse in outers:
                source = charts.compose(D, mark)
                actual = _intervals(source)
                M = charts.span(D)
                N = charts.span(source)
                assert N == d * M + v
                for c in range(v, d):
                    lam, mu = native[c]
                    for j in range(M):
                        ell, h = coarse[j]
                        expected = ((j * a + lam + ell, j * a + mu + h) if mark.case == 'a'
                                    else (j * a + lam - h, j * a + mu - ell))
                        interval = actual[d * j + c]
                        assert interval == expected
                        assert _recover_private(mark.case, a, native[c], j, interval) == (ell, h)
                        identities += 1
                        positive += v > 0
                        vertical += mark.case == 'b'
                for qprime in range(1, M + 1):
                    q = d * qprime
                    last_start = d * (M - qprime) + v
                    assert last_start == N - q
                    first, last = set(), set()
                    for j in range(M):
                        sample = d * j + v
                        assert (sample < q) == (j < qprime)
                        assert (sample >= last_start) == (j >= M - qprime)
                        ell, h = _recover_private(mark.case, a, native[v], j, actual[sample])
                        cells = {(i, i + j) for i in range(ell, h + 1)}
                        if sample < q:
                            first.update(cells)
                        if sample >= last_start:
                            last.update(cells)
                    assert first == {p for p in D if charts.content(p) < qprime}
                    assert last == {p for p in D if charts.content(p) >= M - qprime}
                    windows += 1
    assert identities > 0 and positive > 0 and vertical > 0 and windows > 0
    print(f'exact private endpoint/recovery identities={identities}; positive-width={positive}; '
          f'type(b)={vertical}; complete two-end quotient window checks={windows}')
    print('box: all connected inners2..8, canonical ordinary marks, outers2..4, '
          'every private residue and quotient window length1..outer span')


def main():
    _check_private_windows()
    rng = random.Random(23)
    ok1 = ok2 = fail_plain = fail_rot = 0
    for _ in range(5000):
        Z = random_skew(rng, rng.randint(1, 3))
        W = random_skew(rng, rng.randint(1, 3))
        J = random_skew(rng, rng.randint(1, 3))
        if not all(is_skew(S) and connected(S) for S in (Z, W, J)):
            continue
        if not (2 <= len(Z) <= 6 and 2 <= len(W) <= 6 and 2 <= betas(J)[0][0]):
            continue
        VW = comp(W, J)
        if VW is None or not is_skew(VW) or not connected(VW):
            continue
        U = comp(Z, W)
        Ustar = comp(Z, rot(W))
        if U is None or Ustar is None or not (is_skew(U) and connected(U)):
            continue
        E1 = comp(Z, VW)
        E2 = comp(Z, rot(VW))
        if E1 is None or E2 is None or not (is_skew(E1) and connected(E1)):
            continue
        if not (is_skew(E2) and connected(E2) and is_skew(Ustar) and connected(Ustar)):
            continue
        assert bw(E1, U), ("unrotated", sorted(Z), sorted(W), sorted(J))
        ok1 += 1
        assert bw(E2, Ustar), ("transported", sorted(Z), sorted(W), sorted(J))
        ok2 += 1
        fail_plain += not bw(E2, U)
        fail_rot += not bw(E2, rot(U))
    assert ok1 > 100 and ok2 > 100 and fail_plain > 0 and fail_rot > 0, (ok1, ok2, fail_plain, fail_rot)
    print("both-end windows hold unrotated in", ok1, "and transported in", ok2,
          "; fail against U in", fail_plain, "and against rot U in", fail_rot)


if __name__ == "__main__":
    main()
