r"""The area law and two-copy lists of the amplified ordinary comparison (ge:ordinary-amplified).

Paper section `sec:boundary` (Boundary comparisons and actual marked factors),
ge:ordinary-amplified; the area identity is the full modified-composition identity of
lem:strict-area, with the hatted sets of eq:full-hats.

Reading: the proposition's conclusion is a descent from a comparison the main theorem excludes, so
the finite steps its proof displays are tested on objects built backwards from the mark.  For
every connected J up to J_CELLS cells, every legal ordinary positive-width mark mu of J (period
r, lower copy W, middle O, hatted sets of eq:full-hats computed on the periodic union of
translates) with alpha = |W|, beta = |W-hat|, gamma = |O-hat|, and every connected outer A up to
A_CELLS cells:

* |J| = r + alpha + beta + gamma and |A o_mu J| = r|A| + alpha rows(A) + beta cols(A) + gamma N_A
  for cases (a) and (b), on every composition;
* with V = A of span M >= 3 and Z = Row_2 o_mu J: |E| - |Z| = r(|V| - 2) + alpha(rows V - 1)
  + beta(cols V - 2) + gamma(M - 2), which is positive whenever V is a nonline connected outer
  (at least two rows and two columns, |V| >= M); the control is that a line V (one row or one
  column) can have a nonpositive value on the same formula;
* at EMPTY, |Z| = 2|J| and |E| = r|V| + (|J| - r) M >= M|J| with r the span of J;
* the two-copy lists of Z for a case (a) mark with phases (s, t): X_Z(x + r) - X_Z(x) = [x = r + s]
  and Y_Z(x + r) - Y_Z(x) = -[x = t] for 0 <= x <= r + v.

Uncovered: the coface supply (cuts and head parameters), the missing row X_Z(p) = 0, the child
words, and every descent after them.
"""
from _gluing_common import compose, empty_mark, intersection_mark, legal, shift, span
from check_two_copy_flags import betas, diagrams, phases

J_CELLS = 7
A_CELLS = 5
E_STEP = (1, 1)


def rows_cols(shape):
    return len({i for i, _ in shape}), len({j for _, j in shape})


def hats(mk):
    v = mk.displacement
    union = set()
    for k in range(-4, 5):
        union |= shift(mk.inner, (k * v[0], k * v[1]))
    W = mk.lower
    O = mk.inner - mk.lower - mk.upper
    plus = lambda x: (x[0] + E_STEP[0], x[1] + E_STEP[1])  # noqa: E731
    What = {x for x in union if plus(x) in W} | {x for x in W if plus(x) in union}
    Ohat = {x for x in O if plus(x) in O}
    return len(What), len(Ohat)


def main():
    row2 = frozenset({(0, 0), (0, 1)})
    outers = list(diagrams(A_CELLS))
    law = diffs = lines = 0
    for J in diagrams(J_CELLS):
        for cell in J:
            try:
                mk = intersection_mark(J, cell)
            except AssertionError:
                continue
            if not legal(mk) or mk.case not in 'ab' or mk.width == 0:
                continue
            r = mk.period
            alpha = len(mk.lower)
            beta, gamma = hats(mk)
            assert len(J) == r + alpha + beta + gamma, (sorted(J), r)
            Z = compose(row2, mk)
            for A in outers:
                try:
                    P = compose(A, mk)
                except AssertionError:
                    continue
                rA, cA = rows_cols(A)
                N = span(A)
                assert len(P) == r * len(A) + alpha * rA + beta * cA + gamma * N, (sorted(J), sorted(A))
                law += 1
                if mk.case != 'a':
                    continue
                rr, cc = rows_cols(A)
                diff = len(P) - len(Z)
                assert diff == r * (len(A) - 2) + alpha * (rr - 1) + beta * (cc - 2) + gamma * (N - 2)
                if rr >= 2 and cc >= 2 and N >= 3:
                    assert diff > 0
                    diffs += 1
                else:
                    lines += diff <= 0
            if mk.case == 'a':
                s, t = phases(mk)
                X, Y = betas(Z)
                v = mk.width
                for x in range(0, r + v + 1):
                    assert (x + r in X) - (x in X) == (x == r + s), (sorted(J), x)
                    assert (x + r in Y) - (x in Y) == -(x == t), (sorted(J), x)
    print(f'area law instances {law}; positive differences for nonline outers {diffs}; '
          f'nonpositive for lines or short outers {lines}')
    assert law > 100 and diffs > 50 and lines > 0

    empties = 0
    for J in diagrams(J_CELLS):
        mk = empty_mark(J)
        r = span(J)
        Z = compose(row2, mk)
        assert len(Z) == 2 * len(J)
        for A in outers:
            rr, cc = rows_cols(A)
            if span(A) < 3 or rr < 2 or cc < 2:
                continue
            P = compose(A, mk)
            M = span(A)
            assert len(P) == r * len(A) + (len(J) - r) * M and len(P) >= M * len(J)
            empties += 1
    print(f'EMPTY compositions: {empties}')
    assert empties > 50
    print('ALL PASS')


if __name__ == '__main__':
    main()
