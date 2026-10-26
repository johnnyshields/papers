r"""The native-set conditions of a zero ordinary first matrix (ph:ordinary-zero).

Paper section `app:cofaces` (Cofaces, two-copy identities, and native residues),
ph:ordinary-zero.

The statement is an implication at the full finite comparison, including the actual upper-mate
identities; this script does not construct that comparison or its response matrix.  It tests the
displayed native-set conclusion as a predicate on real marks.  For every connected J up to
J_CELLS cells and legal ordinary case (a) mark of period r, width v > 0, contacts (s, t), use
B = X_W union (X_J on (v, r)) and C = Y_J on [0, r), retaining the returned row s as a target.
For every upper width 0 <= w < r with w != v and delta = v - w:

    ZERO(delta):  ((B minus s) + delta) mod r in B   and   ((C minus t) - delta) mod r in C.

At an empty finer (v = 0, so delta = -w, 0 < w < r), with X_J = {r} u I, Y_J = C_0 u {0}:

    EMPTY(w):     (I - w) mod r in I u {0}   and   (C_0 + w) mod r in C_0 u {0}.

Asserted: both predicates have instances with nonempty sets (the conclusion is satisfiable, not
vacuous), both have violations (it is not automatic), and for each i in I the step orbit stays
in I until reaching zero or repeating.  An orbit need not reach zero.  A connected empty-finer
example with flags X=[4,3,1], Y=[3,1,0] and w=2 checks the repeating orbit 1 -> 3 -> 1.

Uncovered: the zero-matrix hypothesis itself, the available-input tests in the proof, and the
returns at s and t as response data.
"""
from _gluing_common import intersection_mark, legal, empty_mark
from check_two_copy_flags import betas, diagrams, phases

J_CELLS = 10


def _check_orbit(I, r, w, start):
    x, seen = start, set()
    while x != 0 and x not in seen:
        assert x in I, (sorted(I), r, w, start)
        seen.add(x)
        x = (x - w) % r
    return seen, x


def _check_repeating_orbit():
    J = frozenset({(-2, 1), (-1, 0), (-1, 1), (0, 0)})
    assert legal(empty_mark(J))
    X, Y = betas(J)
    assert (X, Y) == ([4, 3, 1], [3, 1, 0])
    r, w = X[0], 2
    I, C0 = set(X) - {r}, set(Y) - {0}
    assert all((i - w) % r in I | {0} for i in I)
    assert all((c + w) % r in C0 | {0} for c in C0)
    visited, terminal = _check_orbit(I, r, w, 1)
    assert visited == {1, 3} and terminal == 1


def main():
    _check_repeating_orbit()
    sat = viol = nontrivial = 0
    for J in diagrams(J_CELLS):
        X, Y = betas(J)
        for cell in J:
            try:
                mk = intersection_mark(J, cell)
            except AssertionError:
                continue
            if mk.case != 'a' or not legal(mk) or mk.width == 0:
                continue
            r, v = mk.period, mk.width
            s, t = phases(mk)
            XW, _ = betas(mk.lower)
            B = set(XW) | {x for x in X if v < x < r}
            C = {y for y in Y if 0 <= y < r}
            for w in range(0, r):
                if w == v:
                    continue
                d = v - w
                ok = (all((b + d) % r in B for b in B - {s})
                      and all((c - d) % r in C for c in C - {t}))
                if ok:
                    sat += 1
                    nontrivial += bool(B - {s}) and bool(C - {t})
                else:
                    viol += 1
    print(f'ordinary marks x widths: satisfying {sat} (both sets nonempty: {nontrivial}), violating {viol}')
    assert nontrivial > 0 and viol > 0

    esat = eviol = eorbit = 0
    for J in diagrams(J_CELLS):
        X, Y = betas(J)
        r = X[0]
        I = {x for x in X if x != r}
        C0 = {y for y in Y if y != 0}
        for w in range(1, r):
            ok = (all((i - w) % r in I | {0} for i in I)
                  and all((c + w) % r in C0 | {0} for c in C0))
            if ok:
                esat += 1
                if I:
                    eorbit += 1
                    for i in I:
                        _check_orbit(I, r, w, i)
            else:
                eviol += 1
    print(f'empty finers x widths: satisfying {esat} (I nonempty: {eorbit}), violating {eviol}')
    assert eorbit > 0 and eviol > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
