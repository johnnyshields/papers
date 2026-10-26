"""Paper section `sec:composition` (Marked composition and the conjecture); targets `eq:offsets`, `eq:tower`, `conj:mvw`.

The composition code against McNamara-van Willigenburg's own examples, and the marks against a
brute-force reading of Hypotheses I-IV.

(1) Example 3.12, both diagrams: D = 2x2 square, E = (4,4,2)/(3) with W->O->W and E = (3,3,3,2)/(2,2)
    with W->O^W; Example 3.13: 2x2 o_empty 2x2 = (5,5,4,4,2)/(3,1,1); Remark 5.8: (2) o_empty (2) = (4),
    and the eight diagrams (E' o_W E'') o_W E''' from E = (2,1), W = (1), all distinct and Schur-equal.
(2) Lemma 3.19(ii): (D o_W E)* = D* o_{W*} E* on every composition of a connected D of <= 5 cells
    with every legal mark of a connected E of <= 6 cells; and the gauge identity
    D o_{empty, vertical} E = AT(D) o_{empty, horizontal} E.
(3) marks(E) equals a brute-force mark list on every connected E of <= 9 cells: every pair of disjoint
    cell subsets W_sw, W_ne = W_sw + v of E containing the southwest and northeast cells, each a
    connected skew diagram, tested against Hypotheses I-IV as stated, with Hypothesis IV evaluated on
    a longer amalgamation (twelve copies) than the one the library uses.
"""
import itertools
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import skew_core as C      # noqa: E402
import skew_compose as K   # noqa: E402


def lam_mu(lam, mu):
    mu = list(mu) + [0] * (len(lam) - len(mu))
    return K.normalize(frozenset((i, j) for i, (a, b) in enumerate(zip(lam, mu)) for j in range(b, a)))


def rows_of(S):
    ri = K.row_intervals(S)
    return [ri[i][1] - ri[i][0] + 1 for i in sorted(ri)]


def mark_with(E, B, T):
    got = [m for m in K.marks(E) if m[0] == B and m[1] == T]
    assert len(got) == 1
    return got[0]


def brute_marks(E):
    """Marks from the definitions, by subsets."""
    E = frozenset(E)
    ne, sw = K.ne_cell(E), K.sw_cell(E)
    cells = sorted(E)
    lying = []
    for r in range(1, len(cells)):
        for sub in itertools.combinations(cells, r):
            Wb = frozenset(sub)
            if sw not in Wb or not K.is_connected_skew(Wb):
                continue
            nb = K.ne_cell(Wb)
            v = (ne[0] - nb[0], ne[1] - nb[1])
            Wt = K.shift(Wb, v)
            if Wt <= E:
                lying.append((Wb, Wt, v))
    out = set()
    for Wb, Wt, v in lying:
        if Wb & Wt:
            continue
        cb = [j - i for i, j in Wb]
        ct = [j - i for i, j in Wt]
        # (I) maximality
        if any(Wb < W2 and min(cb) == min(j - i for i, j in W2) and max(cb) == max(j - i for i, j in W2)
               for W2, _, _ in lying):
            continue
        # (II) separation by a diagonal meeting neither copy
        if not any(c not in cb and c not in ct for c in range(max(cb) + 1, min(ct))):
            continue
        # (III)
        if not (K.is_connected_skew(E - Wb) and K.is_connected_skew(E - Wt)):
            continue
        O = E - Wb - Wt
        case = K.attachment_case(Wb, Wt, O)
        if case is None:
            continue
        # (IV) on twelve copies, interior copies only
        n = 12
        Ebar = set()
        for t in range(n):
            Ebar |= K.shift(E, (t * v[0], t * v[1]))
        bad = False
        for t in range(3, n - 3):
            Ot = K.shift(O, (t * v[0], t * v[1]))
            Oh = {c for c in Ot if (c[0] + 1, c[1] + 1) in Ot}
            for s in range(2, n - 1):
                Ws = K.shift(Wb, (s * v[0], s * v[1]))
                Wh = {c for c in Ebar if (c[0] + 1, c[1] + 1) in Ws} | {c for c in Ws if (c[0] + 1, c[1] + 1) in Ebar}
                if any((a + da, b + db) in Wh for (a, b) in Oh for da, db in ((0, 0), (1, 0), (-1, 0), (0, 1), (0, -1))):
                    bad = True
        if not bad:
            out.add((Wb, Wt, case))
    return out


def main():
    T0 = time.time()
    D = lam_mu((2, 2), ())
    E = lam_mu((4, 4, 2), (3,))
    B, T, case, v, q = mark_with(E, frozenset({(1, 0), (2, 0)}), frozenset({(0, 3), (1, 3)}))
    assert case == 'a' and rows_of(K.compose(D, E, B, T, case, v)) == [1, 4, 5, 5, 5, 2]
    E2 = lam_mu((3, 3, 3, 2), (2, 2))
    B, T, case, v, q = mark_with(E2, frozenset({(2, 0), (3, 0)}), frozenset({(0, 2), (1, 2)}))
    assert case == 'c' and rows_of(K.compose(D, E2, B, T, case, v)) == [1, 1, 3, 2, 4, 4, 5, 2]
    Sq = lam_mu((2, 2), ())
    m0 = K.marks(Sq)[0]
    assert K.compose(Sq, Sq, *m0[:4]) == lam_mu((5, 5, 4, 4, 2), (3, 1, 1))
    two = lam_mu((2,), ())
    assert K.compose(two, two, *K.marks(two)[0][:4]) == lam_mu((4,), ())
    print('PASS (Ex. 3.12, both cases; Ex. 3.13; Rmk 5.8 (2) o (2) = (4)): row profiles as printed by McNamara-van Willigenburg')
    H = lam_mu((2, 1), ())
    mk = [m for m in K.marks(H) if m[0]]
    assert len(mk) == 1
    Bh, Th, ch, vh, qh = mk[0]
    rH = K.rotate_mark(H, Bh, Th, ch, vh)
    assert (ch, rH[3]) == ('d', 'c')
    got = set()
    for a, b, c in itertools.product((0, 1), repeat=3):
        e1 = H if a == 0 else K.rotate(H)
        f2 = (H, Bh, Th, ch, vh) if b == 0 else rH
        f3 = (H, Bh, Th, ch, vh) if c == 0 else rH
        got.add(K.compose(K.compose(e1, *f2), *f3))
    polys = {C.poly_key(C.jt_poly(C.profile_of_cells(S))) for S in got}
    assert len(got) == 8 and len(polys) == 1
    print('PASS (Rmk 5.8): E = (2,1) with W = (1) is W^O->W, E* is W->O^W; the eight (E\' o E\'\') o E\'\'\' are '
          'distinct and Schur-equal')

    Ds = [C.cells(F) for N in range(2, 6) for F in C.all_profiles(N)]
    Es = [C.cells(F) for N in range(2, 7) for F in C.all_profiles(N)]
    nrot = ngauge = 0
    for Eh in Es:
        for (B, T, case, v, q) in K.marks(Eh):
            Er, Br, Tr, cr, vr = K.rotate_mark(Eh, B, T, case, v)
            for Dd in Ds:
                F = K.compose(Dd, Eh, B, T, case, v)
                assert K.rotate(F) == K.compose(K.rotate(Dd), Er, Br, Tr, cr, vr)
                nrot += 1
                if not B:
                    vv = K.vertical_empty_mark(Eh)
                    assert K.compose(Dd, Eh, B, T, 'b', vv[3]) == K.compose(K.antitranspose(Dd), Eh, B, T, 'a', v)
                    ngauge += 1
    print('PASS (Lemma 3.19(ii) and the empty gauge): %d compositions rotate correctly; %d vertical empty readings '
          'equal the horizontal reading with the outer antitransposed' % (nrot, ngauge))

    nE = nm = 0
    for N in range(2, 10):
        for F in C.all_profiles(N):
            Eh = C.cells(F)
            lib = {(B, T, case) for (B, T, case, v, q) in K.marks(Eh) if B}
            assert lib == brute_marks(Eh), ('marks differ from the brute-force reading', C.fmt(F))
            nE += 1
            nm += len(lib)
    print('PASS (marks): on all %d connected inners of 2..9 cells the library marks equal the brute-force marks '
          '(%d nonempty marks)' % (nE, nm))
    print('ALL PASS (%.0fs)' % (time.time() - T0))


if __name__ == '__main__':
    main()
