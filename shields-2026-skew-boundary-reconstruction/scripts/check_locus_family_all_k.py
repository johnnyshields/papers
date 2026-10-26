r"""Paper section `sec:full-rigidity`, subsection `subsec:locus-family` (Reversal pairs on the locus).
Target label: `cor:locus-family`, for EVERY k >= 1, together with `eq:virtual-gap-general` on the family.

The other two scripts on this corollary take determinants, so they stop at small k.  This one proves the
closed forms for all k, at all four admissible weights, by a finite computation that does not take the
determinant of any family member.

Notation.  N = 2k+2, d_j = 2j, and the two row-length words are
    A_k = (2^{k+1}, 3^k, 2),        B_k = (2, 3^k, 2^{k+1})          (rho(A_k), rho(B_k) of the corollary),
    A'_k = (2^k, 3^k, 2),           B'_k = (3^k, 2^{k+1})            (the same words with the first letter cut).
D(rho) = det(h_{rho_i + 2(j-i)}) as in `prop:staircase-reversal`.

(1) The composition expansion.  For a word with every letter <= 3 the matrix of D(rho) has zero entries at
    j <= i-2 (the index is at most rho_i - 4 < 0), so it is upper Hessenberg with subdiagonal h_{rho_i - 2}, and
        D(rho) = sum over compositions of the positions into consecutive blocks [s, s+m] of
                 prod_blocks (-1)^m h_{rho_s + 2m} prod_{i=s+1}^{s+m} h_{rho_i - 2}.
    Asserted against the memoized determinant on every word over {2,3} of length <= 8, with a leading letter
    1..5 in front.  The excess of a block, omega(its monomial) - sum omega(rho_i) over its letters, is additive,
    and the all-singleton composition is the diagonal monomial.  Every block of length >= 2 has positive
    excess, bounded below by f(m) = omega(2+2m) - omega(2) - m (omega(3) - omega(1)), which is convex in m;
    so the diagonal is the unique initial monomial of D(rho) with coefficient one, and only blocks of length
    <= m0 + 1 and at most c of them can occur below an excess budget B (c = floor(B / f(1)), f(m0+1) > B).

(2) The truncated expansion, by a transfer recurrence over the word, keeping every monomial whose excess is
    at most B and nothing else; asserted equal to the truncation of the full determinant for k <= KDET.

(3) Per k <= K and per weight, from the truncated expansions and the cofactor factorization of the
    corollary's proof (the cap matrix vanishes below its diagonal since rho_i <= 3; asserted on the zero
    pattern):
      G_0 = D(A_k) - D(B_k): every coefficient of excess < B0 = e(2,3) + e(2,2) cancels and the excess-B0
            part is nonzero, so alpha_0 = diag + B0;
      G_1 = -(D(A'_k) - D(B'_k)): first nonzero excess e(2,3), so alpha_1 = diag' + e(2,3) + omega(2);
      G_j, 2 <= j <= 2k: the two parents' diagonal weights differ, so alpha_j is the smaller plus omega(2j);
      G_{N-1} = G_N = 0.
    Here e(a,b) = omega(a+2) + omega(b-2) - omega(a) - omega(b) is the excess of a two-letter block.  Then
    every printed clause: supp G = {0, 2, ..., 4k}, m = 2k, T_0^+ = {d_1, d_2}, alpha_0 - m_+ =
    omega(4) - 2 omega(2) (which is `eq:virtual-gap-general` at gamma = d_1 = 2, and 8 at square weight),
    alpha_0 = 13k + 20 and wt(G_2) = 13k - 4 at square weight, and the virtual-row tie of
    `thm:ratio-rigidity`.  At k <= KDET the whole action vector is compared with the one computed from the
    full cofactor determinants of the census.

(4) ALL k.  For k >= k0 = (c+1)(m0+1) + 1 every run of the four words is longer than any block configuration
    of excess <= B, and the configurations are placements of at most c blocks into runs whose lengths are
    affine in k; the number of placements of j blocks with fixed letter patterns is a product of binomials
    C(L - l + j, j) in the run lengths, so every coefficient of the truncated expansion, keyed by its monomial
    divided by the diagonal monomial, is a polynomial in k of degree at most c.  The script interpolates each
    coefficient from the c+1 values at k0..k0+c and asserts the interpolant at every k up to K, then reads the
    G_0 and G_1 statements off the interpolating polynomials: identically zero below the budget, and at the
    budget a polynomial with no integer root >= k0.  The closed forms of the alpha_j are then identities in k
    and in the four weight values omega(1..4) (sympy), and the comparisons alpha_j > alpha_2 for j >= 3 reduce
    to three inequalities in omega that strict convexity forces, asserted at each weight.
    Together with the direct values for k < k0 this proves the corollary's printed numbers for every k.

What remains the paper's: the ratio identity itself (`prop:staircase-reversal`, `lem:two-series-reversal`,
covered by their own scripts) and the reading of the clauses of `thm:ratio-rigidity` from the action vector.
"""
import sys
from collections import Counter

import sympy as sp

from _census_common import SQ, WEIGHTS, Pair, admissible, det_dp, padd, sub, wmon
from check_locus_family_census import X

KDET = 4          # full cofactor determinants, for the cross-check against the census objects
K = 30            # the transfer recurrence: every k up to here, at every weight


def word_A(k):
    return (2,) * (k + 1) + (3,) * k + (2,)


def word_B(k):
    return (2,) + (3,) * k + (2,) * (k + 1)


def Dfull(rho):
    n = len(rho)
    return det_dp([[rho[i] + 2 * (j - i) for j in range(n)] for i in range(n)])


def mono(factors):
    return tuple(sorted((f for f in factors if f > 0), reverse=True))


def mono_mul(a, b):
    return tuple(sorted(a + b, reverse=True))


def block(rho, s, m):
    """(monomial, sign) of the composition block [s, s+m], or None if it carries a zero entry."""
    fac = [rho[s] + 2 * m] + [rho[i] - 2 for i in range(s + 1, s + m + 1)]
    if any(f < 0 for f in fac):
        return None
    return mono(fac), (-1) ** m


def D_composition(rho):
    """The composition expansion in full, for the calibration."""
    n = len(rho)
    T = [None] * (n + 1)
    T[n] = {(): 1}
    for s in range(n - 1, -1, -1):
        out = {}
        for m in range(n - s):
            b = block(rho, s, m)
            if b is None:
                continue
            bm, sg = b
            for mo, c in T[s + m + 1].items():
                key = mono_mul(bm, mo)
                out[key] = out.get(key, 0) + sg * c
        T[s] = {a: c for a, c in out.items() if c}
    return T[0]


def D_truncated(rho, om, B):
    """Every monomial of D(rho) of excess <= B over the diagonal, by the transfer recurrence."""
    n = len(rho)
    diag = [0] * (n + 1)
    for s in range(n - 1, -1, -1):
        diag[s] = diag[s + 1] + om(rho[s])
    T = [None] * (n + 1)
    T[n] = {(): 1}
    for s in range(n - 1, -1, -1):
        out = {}
        for m in range(n - s):
            b = block(rho, s, m)
            if b is None:
                continue
            bm, sg = b
            e = wmon(bm, om) - (diag[s] - diag[s + m + 1])
            assert e >= 0 and (m == 0 or e > 0), ("block excess", rho, s, m, e)
            if e > B:
                continue
            for mo, c in T[s + m + 1].items():
                if e + wmon(mo, om) - diag[s + m + 1] <= B:
                    key = mono_mul(bm, mo)
                    out[key] = out.get(key, 0) + sg * c
        T[s] = {a: c for a, c in out.items() if c}
    return T[0], diag[0]


def relative(monomial, diag_counter):
    """The monomial divided by the diagonal monomial, as a hashable exponent difference."""
    d = Counter(monomial)
    d.subtract(diag_counter)
    return tuple(sorted((i, e) for i, e in d.items() if e))


def rat(x):
    return sp.Rational(x.numerator, x.denominator)


def e2(om, a, b):
    return om(a + 2) + om(b - 2) - om(a) - om(b)


def first_excess(poly, om, diag):
    """(least excess over diag among the monomials of poly, the part at that excess)."""
    if not poly:
        return None, {}
    ex = {mo: wmon(mo, om) - diag for mo in poly}
    lo = min(ex.values())
    return lo, {mo: c for mo, c in poly.items() if ex[mo] == lo}


def structure(om, B):
    """(c, m0): at most c blocks of length >= 2, each of length <= m0 + 1, fit under excess B."""
    def f(m):
        return om(2 + 2 * m) - om(2) - m * (om(3) - om(1))
    # f is the least excess of a length-(m+1) block over letters {2,3}: the top factor is cheapest from a 2,
    # since omega(s + 2m) - omega(s) increases with s, and omega(1) - omega(3) <= -omega(2) by convexity
    assert om(1) - om(3) <= -om(2)
    assert f(1) == e2(om, 2, 3) > 0
    m = 1
    while f(m) <= B:
        assert f(m + 1) > f(m)
        m += 1
    m0 = m - 1
    for t in range(m, m + 5):
        assert f(t + 1) - f(t) >= f(t) - f(t - 1) > 0       # convex and increasing past the budget
    c = int(B // f(1))
    return c, m0


def alpha_vector(k, om):
    """The normalized actions alpha_j of the pair (A_k, B_k), from the truncated expansions."""
    N = 2 * k + 2
    rA, rB = word_A(k), word_B(k)
    e23, e22 = e2(om, 2, 3), e2(om, 2, 2)
    B0 = e23 + e22
    al = [None] * (N + 1)
    # G_0
    TA, dA = D_truncated(rA, om, B0)
    TB, dB = D_truncated(rB, om, B0)
    assert dA == dB
    G0 = sub(TA, TB)
    lo, face = first_excess(G0, om, dA)
    assert lo == B0 and face, ("first excess of G_0", k, lo)
    al[0] = dA + B0
    # G_1 = -(D(A') - D(B'))
    TA1, dA1 = D_truncated(rA[1:], om, e23)
    TB1, dB1 = D_truncated(rB[1:], om, e23)
    assert dA1 == dB1
    G1 = sub(TA1, TB1)
    lo1, face1 = first_excess(G1, om, dA1)
    assert lo1 == e23 and face1, ("first excess of G_1", k, lo1)
    al[1] = dA1 + e23 + om(2)
    # G_j, j >= 2: C_j = (-1)^j prod_{1<=i<j} h_{rho_i - 2} D(rho_j, ..., rho_{N-1}), unique diagonal initial
    for j in range(2, N + 1):
        wA = sum(om(rA[i] - 2) for i in range(1, j)) + sum(om(rA[i]) for i in range(j, N))
        wB = sum(om(rB[i] - 2) for i in range(1, j)) + sum(om(rB[i]) for i in range(j, N))
        if j <= 2 * k:
            assert wA != wB, ("diagonal weights coincide", k, j)
            al[j] = min(wA, wB) + om(2 * j)
        else:
            # the last two coordinates agree: equal prefix multisets and equal suffix words
            assert sorted(rA[1:j]) == sorted(rB[1:j]) and rA[j:] == rB[j:], (k, j)
    return al


def clauses(k, om, al):
    N = 2 * k + 2
    supp = [j for j in range(N + 1) if al[j] is not None]
    assert supp == list(range(2 * k + 1)), ("support", k, supp)
    pos = {j: al[j] for j in supp if j > 0}
    m_plus = min(pos.values())
    assert sorted(j for j, v in pos.items() if v == m_plus) == [1, 2], ("T_0^+", k)
    assert al[0] - m_plus == om(4) - 2 * om(2) == om(2 + 2) - om(2) - om(2) + om(0), ("virtual gap", k)
    assert al[0] > m_plus
    Fv = {j: al[j] + om(2 * j + 2) - om(2 * j) for j in supp}
    mn = min(Fv.values())
    assert sorted(j for j, v in Fv.items() if v == mn) == [0, 1], ("virtual-row tie", k)
    return m_plus


def calibrate():
    import itertools
    n_words = 0
    for n in range(1, 9):
        for w in itertools.product((2, 3), repeat=n):
            for lead in ((), (1,), (2,), (3,), (4,), (5,)):
                rho = lead + w
                assert D_composition(rho) == Dfull(rho), rho
                n_words += 1
    # the truncation is exactly the low-excess part of the determinant
    for nm, om in WEIGHTS.items():
        for k in range(1, KDET + 1):
            for rho in (word_A(k), word_B(k), word_A(k)[1:], word_B(k)[1:]):
                full = Dfull(rho)
                diag = sum(om(r) for r in rho)
                for B in (e2(om, 2, 3), e2(om, 2, 3) + e2(om, 2, 2)):
                    T, dg = D_truncated(rho, om, B)
                    assert dg == diag
                    assert T == {mo: c for mo, c in full.items() if wmon(mo, om) - diag <= B}, (nm, rho, B)
                    assert T.get(mono(rho)) == 1 and all(wmon(mo, om) > diag for mo in T if mo != mono(rho))
    print("(1)-(2) composition expansion on %d words; truncated recurrence equals the truncated determinant "
          "for k <= %d at four weights" % (n_words, KDET))


def cap_zero_pattern():
    # M_ij = h_{rho_i + 2(j-i-1)} vanishes for j < i once rho_i <= 3: index <= rho_i - 4
    for r in (2, 3):
        for gap in range(1, 6):
            assert r + 2 * (-gap - 1) < 0
    # the factorization of the corollary's proof, against the census cofactors, for k <= KDET
    for k in range(1, KDET + 1):
        for rho in (word_A(k), word_B(k)):
            P = Pair(X(rho), X(word_B(k) if rho == word_A(k) else word_A(k)))
            vec = P.CX
            N = len(rho)
            for j in range(1, N + 1):
                pre = {(): 1}
                for i in range(1, j):
                    pre = {mono_mul(mo, mono((rho[i] - 2,))): c for mo, c in pre.items()}
                tail = Dfull(rho[j:]) if j < N else {(): 1}
                cj = {mono_mul(a, b): ca * cb for a, ca in pre.items() for b, cb in tail.items()}
                cj = padd({}, cj) if j % 2 == 0 else {a: -c for a, c in cj.items()}
                assert vec[j] == cj, (k, rho, j)


def main():
    calibrate()
    cap_zero_pattern()
    print("    cap matrix zero below the diagonal; cofactor factorization equals the census cofactors, k <= %d"
          % KDET)

    for nm, om in WEIGHTS.items():
        assert admissible(om)
        e23, e22 = e2(om, 2, 3), e2(om, 2, 2)
        B0 = e23 + e22
        c, m0 = structure(om, B0)
        k0 = (c + 1) * (m0 + 1) + 1
        assert K >= k0 + c + 4, (nm, k0, c)
        # (3) every k up to K
        for k in range(1, K + 1):
            al = alpha_vector(k, om)
            m_plus = clauses(k, om, al)
            if om is SQ:
                assert al[0] == 13 * k + 20 and al[0] - m_plus == 8, (k, al[0])
                assert al[2] - 16 == 13 * k - 4, ("wt(G_2)", k)
            if k <= KDET:
                P = Pair(X(word_A(k)), X(word_B(k)))
                assert P.alpha(om) == al, ("action vector against the census", nm, k)
        # (4) the coefficient polynomials in k, for the four truncated expansions
        polys = {}
        ks = sp.Symbol("k")
        for name, wf, B in (("A", word_A, B0), ("B", word_B, B0),
                            ("A'", lambda k: word_A(k)[1:], e23), ("B'", lambda k: word_B(k)[1:], e23)):
            table = {}
            for k in range(k0, K + 1):
                rho = wf(k)
                T, _ = D_truncated(rho, om, B)
                dc = Counter(mono(rho))
                for mo, cf in T.items():
                    key = (relative(mo, dc), wmon(mo, om) - sum(om(r) for r in rho))
                    table.setdefault(key, {})[k] = cf
            fitted = {}
            for key, vals in table.items():
                seq = [vals.get(k, 0) for k in range(k0, K + 1)]
                pts = list(zip(range(k0, k0 + c + 1), seq[:c + 1]))
                p = sp.expand(sp.interpolate(pts, ks)) if c > 0 else sp.Integer(seq[0])
                for k, v in zip(range(k0, K + 1), seq):
                    assert p.subs(ks, k) == v, ("coefficient is not a polynomial of degree <= c", nm, name, key)
                assert sp.Poly(p, ks).degree() <= c
                fitted[key] = p
            polys[name] = fitted
        # control: the cancellation in G_0 below the budget is not vacuous, and the G_1 budget is a genuine level;
        # each parent alone carries coefficients there that grow with k, so the interpolation reads genuine
        # polynomials and not constants
        for P1 in ("A", "B"):
            assert any(0 < key[1] < B0 and sp.Poly(p, ks).degree() >= 1 for key, p in polys[P1].items()), (nm, P1)
        # the e(2,3) block of G_1 sits at the single 2 -> 3 ascent of A'; B' = (3^k, 2^{k+1}) has none
        assert any(key[1] == e23 and p != 0 for key, p in polys["A'"].items()), nm
        assert not any(key[1] == e23 for key in polys["B'"]), nm
        for (P1, P2, B) in (("A", "B", B0), ("A'", "B'", e23)):
            keys = set(polys[P1]) | set(polys[P2])
            diff = {key: sp.expand(polys[P1].get(key, 0) - polys[P2].get(key, 0)) for key in keys}
            for key, p in diff.items():
                if key[1] < B:
                    assert p == 0, ("a coefficient below the budget survives for some k", nm, P1, key, p)
            top = [p for key, p in diff.items() if key[1] == B and p != 0]
            assert top, (nm, P1)
            # a nonzero polynomial at the budget with no integer root >= k0
            def rootless(p):
                return all(not (r.is_integer and r >= k0) for r in sp.Poly(p, ks).all_roots())
            assert any(rootless(p) for p in top), (nm, P1, top)
        # the closed forms of the actions, as identities in k and omega(1..4)
        w1, w2, w3, w4 = sp.symbols("w1 w2 w3 w4")
        E23 = w4 + w1 - w2 - w3
        E22 = w4 - 2 * w2
        a0 = (ks + 2) * w2 + ks * w3 + E23 + E22
        a1 = (ks + 1) * w2 + ks * w3 + E23 + w2
        a2 = w1 + (ks - 1) * w3 + (ks + 1) * w2 + w4
        assert sp.expand(a1 - a2) == 0 and sp.expand(a0 - a1 - (w4 - 2 * w2)) == 0
        sub_w = {w1: rat(om(1)), w2: rat(om(2)), w3: rat(om(3)), w4: rat(om(4))}
        for k in range(1, K + 1):
            al = alpha_vector(k, om)
            assert [rat(al[0]), rat(al[1]), rat(al[2])] == [x.subs(sub_w).subs(ks, k) for x in (a0, a1, a2)], (nm, k)
        # The diagonal weights of C_j for 2 <= j <= 2k in closed form, every k.  With W = omega(2j) symbolic:
        #   j <= k+1:  wA = (k-j+2) w2 + k w3,                 wB = (j-1) w1 + (k-j+1) w3 + (k+1) w2
        #   j >= k+1:  wA = (j-1-k) w1 + (2k+1-j) w3 + w2,     wB = k w1 + (2k+2-j) w2
        js, W = sp.symbols("j W")
        lo_A = (ks - js + 2) * w2 + ks * w3
        lo_B = (js - 1) * w1 + (ks - js + 1) * w3 + (ks + 1) * w2
        hi_A = (js - 1 - ks) * w1 + (2 * ks + 1 - js) * w3 + w2
        hi_B = ks * w1 + (2 * ks + 2 - js) * w2
        sep = w3 - w2 - w1
        assert sp.expand(lo_A - lo_B - (js - 1) * sep) == 0
        assert sp.expand(hi_A - hi_B - (2 * ks + 1 - js) * sep) == 0
        assert sp.expand((lo_A - lo_B).subs(js, ks + 1) - (hi_A - hi_B).subs(js, ks + 1)) == 0
        for k in range(1, K + 1):
            rA, rB = word_A(k), word_B(k)
            N = 2 * k + 2
            for j in range(2, 2 * k + 1):
                wA = sum(om(rA[i] - 2) for i in range(1, j)) + sum(om(rA[i]) for i in range(j, N))
                wB = sum(om(rB[i] - 2) for i in range(1, j)) + sum(om(rB[i]) for i in range(j, N))
                fA, fB = (lo_A, lo_B) if j <= k + 1 else (hi_A, hi_B)
                assert rat(wA) == fA.subs(sub_w).subs({ks: k, js: j}) and rat(wB) == fB.subs(sub_w).subs({ks: k, js: j})
        # the separation factor is positive (superadditivity from convexity and omega(0) = 0), so the minimum is
        # always wB; at square weight the separations are 4(j-1) and 4(2k+1-j), the paper's 4 min(j-1, 2k+1-j)
        assert om(3) - om(2) - om(1) > 0
        if om is SQ:
            assert sep.subs(sub_w) == 4
        # alpha_j - alpha_2 on the two ranges, with W = omega(2j):
        g_lo = sp.expand(lo_B + W - a2)
        g_hi = sp.expand(hi_B + W - a2)
        assert sp.expand(g_lo - (W - w4 - (js - 2) * (w3 - w1))) == 0
        assert sp.expand(g_hi - ((ks - 1) * (w1 - w3) + (ks + 1 - js) * w2 + W - w4)) == 0
        # g_lo is convex in j (omega convex composed with j -> 2j, minus a linear term), zero at j = 2 and positive
        # at j = 3, hence positive for every j >= 3; g_hi agrees with g_lo at j = k+1 and its increment in j is
        # omega(2j+2) - omega(2j) - omega(2) > 0.  The two numerical inputs, for this weight:
        assert om(6) - om(4) - (om(3) - om(1)) > 0
        assert all(om(2 * j + 2) - om(2 * j) - om(2) > 0 for j in range(1, 2 * K + 2))
        assert all((om(2 * j + 2) - om(2 * j)) - (om(2 * j) - om(2 * j - 2)) > 0 for j in range(1, 2 * K + 2))
        # virtual-row tie: F_0 = F_1, and F_j > F_1 for j >= 2 by alpha_j >= alpha_2 and increasing increments
        assert sp.expand((a0 + w2) - (a1 + w4 - w2)) == 0
        assert (om(4) - om(3)) - (om(2) - om(1)) > 0
        if om is SQ:
            a0s = a0.subs(sub_w)
            assert sp.expand(a0s - (13 * ks + 20)) == 0 and sp.expand(a2.subs(sub_w) - 16 - (13 * ks - 4)) == 0
        print("(3)-(4) %-6s k = 1..%d directly; coefficients polynomial of degree <= %d in k from k0 = %d; "
              "budget %s; all clauses for every k" % (nm, K, c, k0, B0))
    print("cor:locus-family: alpha_0 = 13k+20, wt G_2 = 13k-4, supp {0,2,...,4k}, T_0^+ = {d_1,d_2}, gap 8, "
          "for every k >= 1")
    print("ALL PASS")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
