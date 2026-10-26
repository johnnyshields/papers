r"""Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), ph:endpoint-splice.

The geometric content of the lemma, for the ordinary finer J = (a) with endpoint contacts s = v,
t = 0 and an ordinary or empty upper of width 0 <= w < v (delta = v - w), on a nonliteral source
E = V o_mu J:

* B and D, the restrictions of the lower copy W with flags
  X_B = {delta} u (X_W n (0, delta)), Y_B = Y_W n [0, delta),
  X_D = (X_W n (w, v]) - w, Y_D = {0} u ((Y_W n (w, v)) - w),
  are connected diagrams of span delta (B = D = W at w = 0);
* the horizontal splices S = D < J and T = J < B, with flags
  X_{A<Z} = (c + X_A) u (X_Z \ c), Y_{A<Z} = (c + (Y_A \ 0)) u Y_Z (c = span Z), are connected
  diagrams, and their words satisfy word_S(x) = word_T(x + delta) = word_J(x) for 0 < x < N, for the
  row and the column word;
* the endpoint area law |J| = r + 2A - v + b with A = |W|, b = sum B_- - sum C_- >= 0, and
  |E| >= 3|J| - 2A + v, |E| - (|J| + A) >= 2r + A - v + 2b > 0 for every connected coarse V of
  span M >= 3 with 2 <= rank V <= M - 1; hence both splices have strictly fewer cells than E.

The equalities s_S = s_T and kappa_B = kappa_D of the lemma rest on the physical endpoint identity of
the whole parents and are not checked here (see the coverage table).

Exhaustive over every connected J of at most CELLS cells with a legal case (a) mark of contacts
s = v, t = 0, every such V of at most COARSE_CELLS cells, and every legal ordinary or empty mark of
E of width w < v.
"""
from _gluing_common import compose, content, is_connected_skew, legal, span
from check_two_copy_flags import betas, diagrams, marks, phases

CELLS = 9
COARSE_CELLS = 6


def from_flags(X, Y):
    """The diagram with row k running over contents Y[k] .. X[k] - 1, rows listed top to bottom."""
    assert len(X) == len(Y)
    return frozenset((k, c + k) for k in range(len(X)) for c in range(Y[k], X[k]))


def checked_diagram(X, Y):
    assert len(X) == len(Y) and X == sorted(X, reverse=True) and Y == sorted(Y, reverse=True)
    cells = from_flags(X, Y)
    assert is_connected_skew(cells), (X, Y)
    assert betas(cells) == (X, Y), (X, Y)
    return cells


def splice(AX, AY, ZX, ZY, c):
    X = sorted({c + x for x in AX} | (set(ZX) - {c}), reverse=True)
    Y = sorted({c + y for y in AY if y != 0} | set(ZY), reverse=True)
    return X, Y


def main():
    coarse = [V for V in diagrams(COARSE_CELLS) if span(V) >= 3]
    nonliteral = []
    for V in coarse:
        X, _ = betas(V)
        if 2 <= len(X) <= X[0] - 1:
            nonliteral.append(V)
    assert nonliteral
    cases = 0
    for J in diagrams(CELLS):
        XJ, YJ = betas(J)
        for mu in marks(J):
            if mu.case != 'a' or not mu.lower:
                continue
            v, r = mu.width, mu.period
            if phases(mu) != (v, 0):
                continue
            XW, YW = betas(mu.lower)
            N = r + v
            assert XW[0] == v and YW[-1] == 0
            assert set(XJ) == {r + x for x in XW} | (set(XJ) & set(range(v + 1, r))) \
                | (set(XW) - {v})
            Bm = [x for x in XJ if v < x < r]
            Cm = [y for y in YJ if v < y < r]
            A = len(mu.lower)
            b = sum(Bm) - sum(Cm)
            assert b >= 0 and len(J) == r + 2 * A - v + b, (sorted(J), A, b)
            for V in nonliteral:
                E = compose(V, mu)
                if not is_connected_skew(E):
                    continue
                assert len(E) >= 3 * len(J) - 2 * A + v
                assert len(E) - (len(J) + A) >= 2 * r + A - v + 2 * b > 0
                widths = {om.width for om in marks(E) if legal(om) and om.width < v}
                for w in widths:
                    delta = v - w
                    if w:
                        XB = sorted({delta} | {x for x in XW if 0 < x < delta}, reverse=True)
                        YB = sorted((y for y in YW if 0 <= y < delta), reverse=True)
                        XD = sorted((x - w for x in XW if w < x <= v), reverse=True)
                        YD = sorted({0} | {y - w for y in YW if w < y < v}, reverse=True)
                        Bd = checked_diagram(XB, YB)
                        Dd = checked_diagram(XD, YD)
                    else:
                        XB, YB, XD, YD = XW, YW, XW, YW
                        Bd = Dd = checked_diagram(XW, YW)
                    assert span(Bd) == span(Dd) == delta
                    XS, YS = splice(XD, YD, XJ, YJ, N)
                    XT, YT = splice(XJ, YJ, XB, YB, delta)
                    S = checked_diagram(XS, YS)
                    T = checked_diagram(XT, YT)
                    assert len(S) < len(E) and len(T) < len(E)
                    for x in range(1, N):
                        assert (x in XS) == (x + delta in XT) == (x in XJ)
                        assert (x in YS) == (x + delta in YT) == (x in YJ)
                    cases += 1
    assert cases > 0
    print(f'ph:endpoint-splice: {cases} (J, mu, V, omega) cases; B, D, S, T connected with the '
          f'stated flags and shared words, area law and strict area drop hold')
    print('ALL PASS')


if __name__ == '__main__':
    main()
