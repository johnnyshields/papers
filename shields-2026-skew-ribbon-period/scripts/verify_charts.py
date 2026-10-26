r"""Paper section `sec:charts` (Marked charts, boundary words, and Jacobi--Trudi data).

Targets `eq:intro-bits`, `eq:height-beta`, `lem:core-class`, `prop:local-data`, `eq:coding`,
`eq:caps` and `eq:mixed-height`, and the ordinary-mark endpoint formulas that follow
`eq:mixed-height`; the span and score identities `eq:intro-span`, `eq:intro-score` follow from
`prop:local-data` (item on spans) and are asserted there.

Diagrams are actual skew diagrams (cells `(i, j)`, content `j - i`), every legal mark of every
case is enumerated on them by `check_regroup_mixed`, and the composition `D o_omega E` is built
from the origin formula of the paper.  Beta lists, boundary words, diagonal intervals and
heights are all derived from the cell sets, never from the formulas under test.  The core
lemma is tested by the least ordinary-degree component of the Jacobi--Trudi determinant
(exact `sympy` polynomials in the ordinary-degree variable at a fixed rational alphabet) and on
every Schur-equal pair of small connected diagrams.  Sampled, not exhaustive: diagrams up to the
stated sizes.
"""
import itertools
import sys
from fractions import Fraction

import sympy as sp

from check_regroup_mixed import (Mark, content, is_connected, legal_marks, max_content,
                                 min_content, skew_shapes, span, sw, translate, add, sub, vH)
from _schur_common import alphabet, determinant, jt, row_intervals

T = sp.Symbol("t")
H0 = alphabet(31)


def normalize(S):
    c = min(content(x) for x in S)
    lo = min(x[0] for x in S if content(x) == c)
    return translate((-lo, -(lo + c)), S)


def diag_interval(S, k):
    """Row interval `[l_k, h_k]` of the cells of content `min + k`."""
    c0 = min_content(S)
    rows = [x[0] for x in S if content(x) == c0 + k]
    return min(rows), max(rows)


def beta_lists(S):
    c0 = min_content(S)
    rows = sorted({x[0] for x in S})
    X, Y = [], []
    for i in rows:
        cs = [content(x) - c0 for x in S if x[0] == i]
        Y.append(min(cs))
        X.append(max(cs) + 1)
    return tuple(sorted(X, reverse=True)), tuple(sorted(Y, reverse=True))


def from_betas(X, Y):
    """Diagram with row `i` occupying contents `y_i .. x_i - 1`."""
    return frozenset((i, c + i) for i, (x, y) in enumerate(zip(X, Y)) for c in range(y, x))


def height_word(S):
    N = span(S)
    return [diag_interval(S, k)[1] - diag_interval(S, k)[0] + 1 for k in range(N)]


def words(S):
    X, Y = beta_lists(S)
    N = span(S)
    return {k: int(k in Y) for k in range(1, N)}, {k: int(k in X) for k in range(1, N)}


def check_boundary_words_and_heights(shapes):
    n = 0
    for S in shapes:
        X, Y = beta_lists(S)
        N = span(S)
        assert X[0] == N and Y[-1] == 0 and len(X) == len(Y)
        Hs = height_word(S)
        for k in range(N):                                   # eq:height-beta
            assert Hs[k] == sum(y <= k for y in Y) - sum(x <= k for x in X)
        assert len(S) == sum(Hs)
        A, B = words(S)
        for k in range(1, N):                                # eq:intro-bits
            l0, h0 = diag_interval(S, k - 1)
            l1, h1 = diag_interval(S, k)
            assert (l0 - l1, h0 - h1) in {(a, b) for a in (0, 1) for b in (0, 1)}
            assert Hs[k] - Hs[k - 1] == (h1 - l1) - (h0 - l0)
            assert Hs[k] - Hs[k - 1] == A[k] - B[k], (sorted(S), k)
        # common betas: deletion keeps heights, area, span, connectedness; restoring flips 00 <-> 11
        common = sorted(set(X) & set(Y))
        Xc = tuple(x for x in X if x not in common)
        Yc = tuple(y for y in Y if y not in common)
        core = from_betas(Xc, Yc) if Xc else frozenset()
        if core:
            assert is_connected(core) and span(core) == N
            assert height_word(core) == Hs and len(core) == len(S)
        n += 1
    return n


def ordinary_least_part(S, h):
    """(degree, coefficient) of the least ordinary-degree component of `s_S` at alphabet `h`."""
    a, b = row_intervals(S)
    n = len(a)

    def entry(j):
        return sp.Rational(1) if j == 0 else (sp.Integer(0) if j < 0 else T * sp.Rational(h(j).numerator, h(j).denominator))
    P = sp.Poly(sp.expand(sp.Matrix(n, n, lambda i, j: entry(b[i] - a[j] - i + j)).det()), T)
    low = min(m[0] for m in P.monoms())
    return low, P.coeff_monomial(T ** low)


def check_core_lemma(shapes):
    n = 0
    for S in shapes:
        X, Y = beta_lists(S)
        u = len(set(X) & set(Y))
        r = len(X)
        Xc = tuple(x for x in X if x not in set(Y))
        Yc = tuple(y for y in Y if y not in set(X))
        deg, coef = ordinary_least_part(S, H0)
        assert deg == r - u                                  # least ordinary degree is r - u
        if Xc:
            core = from_betas(Xc, Yc)
            c = jt(core, H0)
            assert abs(sp.Rational(c.numerator, c.denominator)) == abs(coef)   # = core determinant, up to sign
        n += 1
    # equal Schur functions (two alphabets) -> equal cores and equal (r, u)
    pairs = 0
    byval = {}
    for S in shapes:
        key = (jt(S, alphabet(41)), jt(S, alphabet(42)))
        byval.setdefault(key, []).append(S)
    for group in byval.values():
        for S1, S2 in itertools.combinations(group, 2):
            pairs += 1
            X1, Y1 = beta_lists(S1)
            X2, Y2 = beta_lists(S2)
            assert len(X1) == len(X2) and len(set(X1) & set(Y1)) == len(set(X2) & set(Y2))
            c1 = tuple(x for x in X1 if x not in set(Y1)), tuple(y for y in Y1 if y not in set(X1))
            c2 = tuple(x for x in X2 if x not in set(Y2)), tuple(y for y in Y2 if y not in set(X2))
            if c1[0] and c2[0]:
                for s in (41, 42):
                    assert jt(from_betas(*c1), alphabet(s)) == jt(from_betas(*c2), alphabet(s))
    return n, pairs


def window(F, k0, count):
    cells = [x for x in F if k0 <= content(x) - min_content(F) < k0 + count]
    return normalize(frozenset(cells))


def check_local_data(shapes_E, outers):
    n_marks = n_comp = 0
    for E in shapes_E:
        for m in legal_marks(E):
            p, w = m.period(), m.width()
            if w == 0:
                continue
            n_marks += 1
            N = span(E)
            c0 = min_content(E)
            assert N == p + w
            # (1) W_- = E cap (E - v); middle has at most one cell on each marked diagonal;
            #     the private diagonals w and p-1 are singletons
            assert m.W == E & translate((-m.v[0], -m.v[1]), E)
            O = m.middle()
            marked = {content(x) for x in m.W}
            for c in marked:
                assert sum(1 for x in O if content(x) == c) <= 1
            for k in (w, p - 1):
                assert sum(1 for x in E if content(x) - c0 == k) == 1
            # (2) the middle occupies [s, p + t - 1], 1 <= s <= w, 0 <= t < w; t < s for mixed
            cs = sorted(content(x) - c0 for x in O)
            s_, t_ = cs[0], cs[-1] - p + 1
            assert 1 <= s_ <= w and 0 <= t_ < w
            if m.case in 'cd':
                assert t_ < s_
            # (3) windows of D o E
            for D in outers:
                MD = span(D)
                F = m.compose(D)
                assert span(F) == MD * p + w                # eq:intro-span, N_F = p N_D + w
                lo = window(F, 0, p)
                hi = window(F, span(F) - p, p)
                assert lo == window(E, 0, p) and hi == window(E, N - p, p)
                n_comp += 1
    return n_marks, n_comp


def check_coding(shapes_E, outers):
    n = 0
    for E in shapes_E:
        for m in legal_marks(E):
            p, w = m.period(), m.width()
            if w == 0:
                continue
            c0 = min_content(E)
            O = m.middle()
            cs = sorted(content(x) - c0 for x in O)
            s_, t_ = cs[0], cs[-1] - p + 1
            exceptional = {'a': ({t_}, {s_}), 'b': ({s_}, {t_}), 'c': (set(), {t_, s_}), 'd': ({t_, s_}, set())}[m.case]
            for D in outers:
                MD = span(D)
                F = m.compose(D)
                NF = span(F)
                A, B = words(F)
                AD, BD = words(D)
                # eq:coding, interior slots, 1 <= j <= M - 1
                for j in range(1, MD):
                    a, b = AD[j], BD[j]
                    if m.case == 'a':
                        assert A[j * p + t_] == a and B[j * p + s_] == b
                    elif m.case == 'b':
                        assert B[j * p + t_] == 1 - a and A[j * p + s_] == 1 - b
                    elif m.case == 'c':
                        assert B[j * p + t_] == 1 - a and B[j * p + s_] == b
                    else:
                        assert A[j * p + t_] == a and A[j * p + s_] == 1 - b
                # p-periodic away from the exceptional residues
                for word, exc in ((A, exceptional[0]), (B, exceptional[1])):
                    for k in range(1, NF - p):
                        if (k % p) not in exc and (k + p) in word and k in word:
                            assert word[k] == word[k + p], (m.case, sorted(E), sorted(D), k)
                # eq:caps: initial and terminal values (steps at 0 and N are omitted)
                def at(word, k):
                    return word.get(k)
                tail = NF - w
                spec = {
                    'a': [(A, t_, 1), (B, s_, 0), (A, tail + t_, 0), (B, tail + s_, 1)],
                    'b': [(B, t_, 0), (A, s_, 1), (B, tail + t_, 1), (A, tail + s_, 0)],
                    'c': [(B, t_, 0), (B, s_, 0), (B, tail + t_, 1), (B, tail + s_, 1)],
                    'd': [(A, t_, 1), (A, s_, 1), (A, tail + t_, 0), (A, tail + s_, 0)],
                }[m.case]
                for word, k, val in spec:
                    if at(word, k) is not None:
                        assert word[k] == val, (m.case, sorted(E), sorted(D), k)
                # private-interface values
                if m.case == 'd' and 0 < w < NF and p < NF:
                    assert B[w] == 1 and B[p] == 0
                if m.case == 'c' and 0 < w < NF and p < NF:
                    assert A[w] == 0 and A[p] == 1
                n += 1
    return n


def check_mixed_height(shapes_E, outers):
    """`eq:mixed-height` in case (d), and the ordinary endpoint formulas after it."""
    n = n_ord = 0
    for E in shapes_E:
        for m in legal_marks(E):
            p, w = m.period(), m.width()
            if w == 0 or m.case not in 'ad':
                continue
            c0 = min_content(E)
            cs = sorted(content(x) - c0 for x in m.middle())
            s_, t_ = cs[0], cs[-1] - p + 1
            HE = height_word(E)
            # marked height: the cells of the lower marked copy on residue r (the marked line)
            Om = [sum(1 for x in m.W if content(x) - c0 == r) for r in range(w)]
            for D in outers:
                MD = span(D)
                F = m.compose(D)
                HF = height_word(F)
                ivD = [diag_interval(D, j) for j in range(MD)]
                if m.case == 'd':
                    def Mj(j):
                        return 0 if j < 0 or j >= MD else ivD[j][1] - ivD[j][0] + 1

                    def Sj(j):
                        if j == 0 or j == MD:
                            return 1
                        return ivD[j - 1][1] - ivD[j][0] + 1
                    for j in range(0, MD + 1):
                        for r in range(p):
                            k = p * j + r
                            if k >= len(HF) or (r >= w and j >= MD):
                                continue
                            if r >= w:
                                want = HE[r] + Mj(j) - 1                     # nu_r + M_j - 1
                            elif r < t_:
                                want = Om[r] + Mj(j - 1)
                            elif r < s_:
                                want = Om[r] + Sj(j) - 1
                            else:
                                want = Om[r] + Mj(j)
                            assert HF[k] == want, (sorted(E), sorted(m.W), sorted(D), j, r, HF[k], want)
                            n += 1
                else:
                    v1 = m.v[0]
                    Fi = [diag_interval(F, k) for k in range(len(HF))]
                    # [a_r, b_r]: the interval of the marked copy on residue r
                    Ei = [diag_interval(m.W, k) for k in range(span(m.W))]
                    for j in range(1, MD):
                        for r in range(w):
                            lj1 = ivD[j - 1][0]
                            lj = ivD[j][0]
                            hj1 = ivD[j - 1][1]
                            hj = ivD[j][1]
                            lo = j * v1 + Ei[r][0] + (lj1 - 1 if r < t_ else lj)
                            hi = j * v1 + Ei[r][1] + (hj1 if r < s_ else hj + 1)
                            assert Fi[p * j + r] == (lo, hi), (sorted(E), sorted(m.W), sorted(D), j, r)
                            n_ord += 1
    return n, n_ord


def main():
    shapes = list(skew_shapes(8, 4, 5))
    n = check_boundary_words_and_heights(shapes)
    nc, npairs = check_core_lemma(shapes)
    es = [E for E in skew_shapes(6, 3, 4) if len(E) >= 2]
    outers = [D for D in skew_shapes(5, 3, 3) if len(D) >= 2]
    nm, ncomp = check_local_data(es, outers)
    ncod = check_coding(es, outers)
    nh, nord = check_mixed_height(es, outers)
    print(f"diagrams {n}, core lemma {nc} ({npairs} Schur-equal pairs), positive marks {nm}, "
          f"window checks {ncomp}, coding {ncod}, mixed heights {nh}, ordinary endpoints {nord}")
    assert min(n, nc, nm, ncomp, ncod, nh) > 0
    print("PASS")


if __name__ == "__main__":
    main()
