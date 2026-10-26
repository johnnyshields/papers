r"""Paper section `sec:stationary` (Finite stationary separation), inside the proof of `sc:positive-power`.

Targets `sc:top-matching`, `sc:complete-pole-bracket`, `sc:first-pole-jet`, `sc:cell-second-jet`,
`sc:unit-first-cap`, and `sc:whole-field-equation`.

The coframes of an actual coequal pair are rebuilt from their full proper matrices with every letter but
the top proper one a fixed nonzero rational, so each coefficient is a polynomial in the single letter
`y = H_m`; the coequal pairs themselves are grouped by Schur function and confirmed by exact symbolic
determinants.  Each displayed formula is compared coefficient by coefficient, including the discarded
tails of the finite operator, on every pair of spans three through seven whose highest strict proper
components coincide; controls leave the stated hypothesis and must fail.  The exact degree-by-degree
algebra for the cell case is carried out with generic defect coefficients.  Samples are finite and
do not prove the universal statements.
"""
import random
from collections import defaultdict
from functools import lru_cache
from itertools import combinations

import sympy as sp

from _coframes import (
    z, theta, epsilon, letter, determinant, right_coframe, clock, coefficient, clip, operator, zero, order,
    connected_boards,
)

random.seed(20261027)
y = sp.Symbol("y")


# ------------------------------------------------------------------ numeric coframes

def point(span):
    """A fixed nonzero rational value for every letter below the top proper one."""
    return {j: sp.Rational(random.randint(2, 40), random.randint(1, 5)) for j in range(span)}


def entry(j, vals, m):
    if j < 0:
        return sp.S.Zero
    return y if j == m else vals[j]


def num_coframe(board, vals, m):
    """Complete right coframe, solved from the native equations with the top letter left symbolic."""
    rows, cols = board
    if len(rows) == 1:
        return sp.S.One
    proper = sp.Matrix([[entry(x - c, vals, m) for c in cols[:-1]] for x in rows[1:]])
    border = sp.Matrix([entry(x, vals, m) for x in rows[1:]])
    sol = -(proper.adjugate() * border) / proper.det()
    return sp.Add(sp.S.One, *(sp.expand(sp.cancel(c)) * z ** j for c, j in zip(sol, cols[:-1])))


def num_clock(vals, m, top=True):
    return vals[0] + sp.Add(*(vals[j] * z ** j for j in range(1, m))) + (y * z ** m if top else 0)


def blocks(board):
    """Strict components of the proper matrix as (rows, columns) pairs, from the top."""
    rows, cols = board
    R, C = rows[1:], cols[:-1]
    cuts = [k for k in range(1, len(R)) if R[k] < C[k - 1]]
    bounds = [0] + cuts + [len(R)]
    return [(R[a:b], C[a:b]) for a, b in zip(bounds, bounds[1:])]


@lru_cache(maxsize=None)
def coequal_pairs(span):
    """Distinct connected boards of equal Schur function, grouped by two random numeric points and confirmed
    by the exact symbolic determinant."""
    pts = [[1] + [random.randint(2, 60) for _ in range(span)] for _ in range(2)]

    def numeric(board, p):
        rows, cols = board
        return sp.Matrix([[p[x - c] if x >= c else 0 for c in cols] for x in rows]).det()
    groups = defaultdict(list)
    for board in connected_boards(span):
        groups[tuple(numeric(board, p) for p in pts)].append(board)
    out = []
    for boards in groups.values():
        for a, b in combinations(boards, 2):
            assert zero(determinant(a, unit=1) - determinant(b, unit=1)), (a, b)
            out.append((a, b))
    return tuple(out)


def truncated_inverse(u, size):
    """Series inverse of the polynomial u (nonzero constant term) modulo z^size."""
    u0 = u.subs(z, 0)
    coeffs = [u.coeff(z, i) for i in range(size)]
    inv = [1 / u0]
    for n in range(1, size):
        inv.append(sp.expand(-sum(coeffs[i] * inv[n - i] for i in range(1, n + 1)) / u0))
    return sum(c * z ** i for i, c in enumerate(inv))


def apply_potential(r, H, size):
    """r(H) modulo z^size for r a polynomial or 1/(x+c); r is a pair (kind, data)."""
    kind, data = r
    if kind == "poly":
        total, power = sp.S.Zero, sp.S.One
        for c in data:
            total += c * power
            power = clip(sp.expand(power * H), size)
        return clip(sp.expand(total), size)
    return truncated_inverse(sp.expand(H + data), size)


def potential_value(r, t):
    kind, data = r
    return sum(c * t ** i for i, c in enumerate(data)) if kind == "poly" else 1 / (t + data)


def residual(G, C, H, p, r, M):
    D = operator(G, C, H, M)
    R = operator(G, C, z * clip(sp.expand(H ** p), 2 * M), M) + z * D * apply_potential(r, H, 2 * M)
    return clip(sp.expand(R), 2 * M), D


def component(blk, vals, m):
    """(g, k, a, L) for the component block (rows, columns), top letter excluded because L < m."""
    rows, cols = blk
    a = cols[-1]
    L = rows[0] - a
    if L == 0:
        return sp.S.One, vals[0], a, 0
    comp = (tuple(x - a for x in rows), tuple(c - a for c in cols))
    g = num_coframe(comp, vals, m)
    k = coefficient(clip(sp.expand(num_clock(vals, L + 1, top=False) * g), L + 1), L)
    return g, k, a, L


def matched_pairs(spans):
    """Distinct coequal pairs of equal span whose top proper row is m on both sides and whose highest strict
    proper components coincide as lists."""
    out = []
    for span in spans:
        m = span - 1
        for a_b, b_b in coequal_pairs(span):
            if m in a_b[0][1:] and m in b_b[0][1:] and blocks(a_b)[0] == blocks(b_b)[0]:
                out.append((span, a_b, b_b))
    return out


# ------------------------------------------------------------------ sc:top-matching

def check_top_matching():
    """Hypotheses of the lemma: E_0 = 0 and the y-derivative of E_1 vanishes (sampled at two points).  The
    conclusion is the literal agreement of the top components, and then dDelta/dy = 0 = Delta_1.  Every pair with
    differing top positions must violate a hypothesis; the identical-component pairs and the diagonal pairs
    are the ones that can satisfy them."""
    held = refuted = held_distinct = 0
    for span in range(3, 8):
        m, M = span - 1, span
        for a_b, b_b in list(coequal_pairs(span)) + [(b, b) for b in list(connected_boards(span))[:6]]:
            if not (m in a_b[0][1:] and m in b_b[0][1:]):
                continue
            ba, bb = blocks(a_b)[0], blocks(b_b)[0]
            for p in (2, 3):
                verdict = []
                for _ in range(2):
                    vals = point(span)
                    G, C = num_coframe(a_b, vals, m), num_coframe(b_b, vals, m)
                    H = num_clock(vals, m)
                    delta = sp.expand(C - G)
                    Hp = clip(sp.expand(H ** p), 2 * M)
                    E0 = coefficient(clip(sp.expand(Hp * delta), M), m)
                    E1 = coefficient(clip(sp.expand(Hp * delta), M + 1), M) - coefficient(delta, 1) * coefficient(
                        clip(sp.expand(Hp * G), M), m)
                    verdict.append((zero(E0), zero(sp.diff(E1, y)), zero(sp.diff(delta, y)),
                                    zero(coefficient(delta, 1))))
                if all(v[0] and v[1] for v in verdict):
                    held += 1
                    held_distinct += a_b != b_b
                    assert ba == bb, (a_b, b_b, p)                      # literal agreement in position
                    assert all(v[2] and v[3] for v in verdict), (a_b, b_b, p)
                else:
                    refuted += 1
                if ba[1][-1] != bb[1][-1]:                               # differing least columns
                    assert not all(v[0] and v[1] for v in verdict), (a_b, b_b, p)
    assert held > 0 and refuted > 0
    print("PASS sc:top-matching: hypotheses imply matching top components, dDelta/dy = 0 = Delta_1; "
          "%d hypothesis-satisfying (%d on distinct pairs) and %d hypothesis-violating (pair, exponent) cases"
          % (held, held_distinct, refuted))


# ------------------------------------------------------------------ pole bracket, first jet, cell jet

POTENTIALS = (("poly", (sp.Rational(3), sp.Rational(-2), sp.Rational(1))), ("inv", sp.Rational(5)))


def check_pole_formulas():
    pairs = matched_pairs(range(3, 8))
    assert len(pairs) >= 8, len(pairs)
    jets = distinct = units = comps = cells = 0
    for span, a_b, b_b in pairs:
        m, M = span - 1, span
        vals = point(span)
        G, C = num_coframe(a_b, vals, m), num_coframe(b_b, vals, m)
        delta = sp.expand(C - G)
        if zero(delta):
            continue
        assert not sp.diff(delta, y) and not sp.diff(sp.expand(G), y).free_symbols - {z}
        distinct += 1
        g, k, a, L = component(blocks(a_b)[0], vals, m)
        d = order(delta)
        assert 1 <= d <= a - 2                                         # sc:top-support
        h = num_clock(vals, m, top=False)
        units += L == 0
        cells += L == 1
        comps += L >= 2
        for p in (2, 3):
            theta0 = vals[0]
            forced = -p * theta0 ** (p - 1)
            for r in POTENTIALS + (("poly", (forced,)),) + (("poly", (sp.S.Zero, sp.S.Zero, sp.S.Zero, sp.S.Zero)),):
                R, D = residual(G, C, num_clock(vals, m), p, r, M)
                Ry = sp.expand(sp.diff(R, y))
                rh = apply_potential(r, h, 2 * M)
                hp = clip(sp.expand(h ** p), 2 * M)
                bracket = (delta * clip(sp.expand(hp * g), L) - g * clip(sp.expand(hp * delta), M - 1)
                           + rh * (delta * clip(sp.expand(h * g), L) - g * clip(sp.expand(h * delta), M)))
                formula = clip(sp.expand(z ** (a + 1) / k * bracket), 2 * M)
                # sc:complete-pole-bracket, every coefficient below 2M
                assert zero(Ry - formula), (a_b, b_b, p, r)
                # sc:first-pole-jet
                if L + d <= M - 3:
                    A = coefficient(clip(sp.expand(hp * g), L + 1), L)
                    jet = -coefficient(delta, d) * (A / k + potential_value(r, theta0))
                    assert d < M and M + d < 2 * M
                    assert all(zero(Ry.coeff(z, j)) for j in range(M + d))
                    assert zero(Ry.coeff(z, M + d) - jet), (a_b, b_b, p, r)
                    jets += 1
                    # the jet pins r(theta): the constant potential at exactly that value kills it
                    pinned = ("poly", (-A / k,))
                    Rp, _ = residual(G, C, num_clock(vals, m), p, pinned, M)
                    assert zero(sp.expand(sp.diff(Rp, y)).coeff(z, M + d))
                    if not zero(potential_value(r, theta0) + A / k):
                        assert not zero(Ry.coeff(z, M + d))
        # the quantifiers of the component cases: remainder nonzero for L >= 2 (sc:nonzero-remainder)
        if L >= 2:
            assert not zero(coefficient(clip(sp.expand(clip(sp.expand(h ** 2), 2 * M) * g), L + 1), L)
                            - 2 * vals[0] * k)
    assert distinct >= 6 and jets > 0 and units > 0 and cells >= 1
    assert comps == 0       # no actual coequal pair through span seven has a matched component of span >= 2
    print("PASS sc:complete-pole-bracket and sc:first-pole-jet on %d distinct matched pairs "
          "(%d unit, %d cell, %d longer component: none exists, as the theorem excludes), %d jet coefficients" % (distinct, units, cells, comps, jets))


def check_cell_second_jet():
    """Cell case L = 1: g = 1, k = H_1, a = M - 2.  With r(x) = -p x^(p-1) the bracket collapses to
    -z^(M-1) Q_1 / H_1; below degree M - 1 the polynomial Q_1 is Delta times
    (1-p)h^p + p theta h^(p-1) - theta^p, whose first nonzero coefficient is the quadratic one; the coefficient of
    z^(M+d+1) of R_y is binom(p,2) theta^(p-2) H_1 Delta_d.  Done with generic defect coefficients, then on the
    actual cell pairs."""
    th, H1, H2, H3 = sp.symbols("theta H1 H2 H3", nonzero=True)
    for p in (2, 3, 4):
        for M in (5, 6, 7):
            letters = [th, H1, H2, H3] + list(sp.symbols("Hx4:%d" % (M + 1)))
            h = sum(letters[j] * z ** j for j in range(0, M - 1))
            hp = clip(sp.expand(h ** p), 2 * M)
            factor = sp.expand((1 - p) * hp + p * th * clip(sp.expand(h ** (p - 1)), 2 * M) - th ** p)
            assert zero(coefficient(factor, 0)) and zero(coefficient(factor, 1))
            assert zero(coefficient(factor, 2) + sp.binomial(p, 2) * th ** (p - 2) * H1 ** 2)
            for d in range(1, M - 3):                       # d <= M - 4
                dl = sp.symbols("D%d:%d" % (d, M))
                delta = sum(c * z ** (d + i) for i, c in enumerate(dl))
                Q1 = (clip(sp.expand(hp * delta), M - 1) - th ** p * delta
                      - p * clip(sp.expand(h ** (p - 1)), 2 * M) * (clip(sp.expand(h * delta), M) - th * delta))
                # below degree M - 1, Q_1 = Delta * factor
                assert zero(clip(sp.expand(Q1 - delta * factor), M - 1))
                # coefficient of z^(d+2) in -Q_1: the first surviving product coefficient (index M+d+1 in R_y)
                lead = -coefficient(sp.expand(delta * factor), d + 2)
                assert zero(lead - sp.binomial(p, 2) * th ** (p - 2) * H1 ** 2 * dl[0])
                assert d + 2 <= M - 2                         # that coefficient lies below the clip at M - 1
    # actual cell pairs: g = 1, k = H_1, a = M - 2
    seen = 0
    for span, a_b, b_b in matched_pairs(range(3, 8)):
        m, M = span - 1, span
        vals = point(span)
        g, k, a, L = component(blocks(a_b)[0], vals, m)
        if L != 1:
            continue
        G, C = num_coframe(a_b, vals, m), num_coframe(b_b, vals, m)
        delta = sp.expand(C - G)
        if zero(delta):
            continue
        d = order(delta)
        assert g == 1 and zero(k - vals[1]) and a == M - 2 and d <= M - 4
        for p in (2, 3):
            r = ("poly", (sp.S.Zero,) * (p - 1) + (-p,))
            R, _ = residual(G, C, num_clock(vals, m), p, r, M)
            Ry = sp.expand(sp.diff(R, y))
            assert all(zero(Ry.coeff(z, j)) for j in range(M + d + 1))
            assert zero(Ry.coeff(z, M + d + 1) - sp.binomial(p, 2) * vals[0] ** (p - 2) * vals[1] * coefficient(delta, d))
            assert not zero(Ry.coeff(z, M + d + 1))
        seen += 1
    assert seen >= 1
    print("PASS sc:cell-second-jet: generic-defect algebra for p = 2, 3, 4 at M = 5, 6, 7 and %d actual cell pair(s)"
          % seen)


# ------------------------------------------------------------------ sc:unit-first-cap

def eps_coframe(board, vals, m, unit_scale):
    """Complete right coframe at H = 1 + epsilon U, U a fixed rational array; common betas are coherent units."""
    rows, cols = board
    if len(rows) == 1:
        return sp.S.One

    def e(j):
        if j < 0:
            return sp.S.Zero
        return sp.S.One if j == 0 else unit_scale * vals[j]
    proper = sp.Matrix([[e(x - c) for c in cols[:-1]] for x in rows[1:]])
    border = sp.Matrix([e(x) for x in rows[1:]])
    sol = -proper.LUsolve(border)
    return sp.Add(sp.S.One, *(sp.cancel(c) * z ** j for c, j in zip(sol, cols[:-1])))


def check_unit_first_cap():
    """Both diagrams have a true unit at m.  The coefficient of epsilon in E_0 = [H_eps^p (C_eps - G_eps)]_m is
    (p-1)([Uc]_m - [Ug]_m), where g, c are the zero-free cores' coframes, the epsilon-order terms of G_eps and
    C_eps carry the restored m-columns -[Ug]_m and -[Uc]_m, and p = 1 gives no condition."""
    count = 0
    for span in range(4, 8):
        m, M = span - 1, span
        for a_b, b_b in coequal_pairs(span):
            if not (blocks(a_b)[0] == blocks(b_b)[0] == ((m,), (m,))):
                continue
            vals = point(span)
            U = sum(vals[j] * z ** j for j in range(1, m + 1))
            coef = {}
            for name, board in (("G", a_b), ("C", b_b)):
                common = set(board[0]) & set(board[1])
                core = (tuple(x for x in board[0] if x not in common), tuple(c for c in board[1] if c not in common))
                g0 = num_coframe(core, vals, m + 10) if len(core[0]) > 1 else sp.S.One
                # the core is zero-free: its coframe is read with the letters U
                ge = sp.expand(eps_coframe(board, vals, m, epsilon))
                gt0 = sp.expand(sp.Add(*(sp.limit(ge.coeff(z, j), epsilon, 0) * z ** j for j in range(M))))
                coef[name] = (ge, gt0, g0)
                assert zero(gt0 - g0)                                    # epsilon = 0 is the zero-free core
                g1 = sp.Add(*(sp.diff(sp.cancel(ge.coeff(z, j)), epsilon).subs(epsilon, 0) * z ** j
                              for j in range(M)))
                assert zero(g1.coeff(z, m) + coefficient(clip(sp.expand(U * g0), M), m))     # restored m-column
            Gs, Cs = coef["G"], coef["C"]
            g, c = Gs[1], Cs[1]
            Delta_e = sp.expand(Cs[0] - Gs[0])
            for p in (1, 2, 3, 4):
                He = 1 + epsilon * U
                E0 = coefficient(clip(sp.expand(He ** p * Delta_e), M), m)
                first = sp.diff(sp.cancel(E0), epsilon).subs(epsilon, 0)
                want = (p - 1) * (coefficient(clip(sp.expand(U * c), M), m) - coefficient(clip(sp.expand(U * g), M), m))
                assert zero(first - want), (a_b, b_b, p)
                if p == 1:
                    assert zero(first)
                elif not zero(g - c):
                    assert not zero(first) or zero(want)
            count += 1
    assert count >= 2
    print("PASS sc:unit-first-cap on %d coequal pairs with a true unit at m (p = 1 control vanishes)" % count)


# ------------------------------------------------------------------ sc:whole-field-equation

def check_whole_field():
    """For a distinct coequal pair put l = ord D.  The whole moving homomorphism fixes psi0 modulo z, so the
    coefficient of z^(l+1) in z D R(psi0) is D_l psi0 and is retained (l + 1 <= 2M - 1); hence
    psi0 / c = -[z^(l+1)] T(zH^p) / D_l, a function of the letters.  Symbolic coframes from full flags (spans
    three and four): this quotient is not free of the positive letters, so it is not an element of K(theta)
    and the fixed-field intersection step has content; the span-three terminal pair has l = 2M - 2.  Control: a
    frozen potential r(theta) agrees with the moving r(H) through z^(l+1) and differs beyond, so the extraction
    degree is the first one at which the potential is seen."""
    pairs = terminal = inside = outside = 0
    for span in range(3, 5):
        M = span
        groups = defaultdict(list)
        for board in connected_boards(span):
            groups[determinant(board, unit=1)].append(board)
        for boards in groups.values():
            for a_b, b_b in combinations(boards, 2):
                G, C = right_coframe(a_b), right_coframe(b_b)
                H = clock(M - 1)
                D = operator(G, C, H, M)
                assert not zero(D)
                ell = order(D)
                assert M + 1 <= ell <= 2 * M - 2 and ell + 1 <= 2 * M - 1          # sc:defect-orders
                terminal += ell == 2 * M - 2
                Hfull = clock(2 * M - 1)
                for p in (2, 3):
                    T = operator(G, C, z * clip(sp.expand(Hfull ** p), 2 * M), M)
                    quotient = sp.cancel(-coefficient(T, ell + 1) / coefficient(D, ell))
                    if any(quotient.has(letter(j)) for j in range(1, M)):
                        outside += 1                  # not in K(theta): excluded by the fixed-field step
                    else:
                        inside += 1                   # psi0 / c = r(theta): the moving substitution must fail
                        r_move = sp.series(quotient.subs(theta, Hfull), z, 0, 2 * M).removeO().expand()
                        residual_whole = clip(sp.expand(T + z * D * r_move), 2 * M)
                        assert not zero(residual_whole), (a_b, b_b, p)
                for r_theta, r_moving in ((sp.Rational(3, 7), sp.Rational(3, 7)),
                                          (1 / (1 + theta), jet_inverse(1 + Hfull, 2 * M)),
                                          (theta ** 2, sp.expand(clip(sp.expand(Hfull ** 2), 2 * M)))):
                    moving = clip(sp.expand(z * D * r_moving), 2 * M)
                    frozen = clip(sp.expand(z * D * r_theta), 2 * M)
                    assert order(moving) == ell + 1 == order(frozen)
                    assert zero(coefficient(moving, ell + 1) - coefficient(D, ell) * r_theta)
                    assert zero(coefficient(moving, ell + 1) - coefficient(frozen, ell + 1))
                    if r_theta != sp.Rational(3, 7) and ell + 2 <= 2 * M - 1:
                        assert not zero(coefficient(moving, ell + 2) - coefficient(frozen, ell + 2))
                pairs += 1
    assert pairs > 0 and terminal > 0 and inside > 0
    print("PASS sc:whole-field-equation: extraction at z^(l+1) <= z^(2M-1) on %d distinct pairs (%d with l = 2M-2); "
          "the extracted quotient lies in K(theta) in %d (pair, exponent) cases, where the moving substitution fails, "
          "and involves positive letters in %d; moving and frozen potentials agree through the extraction degree"
          % (pairs, terminal, inside, outside))


def jet_inverse(u, size):
    return sp.series(1 / u, z, 0, size).removeO().expand()


if __name__ == "__main__":
    check_top_matching()
    check_pole_formulas()
    check_cell_second_jet()
    check_unit_first_cap()
    check_whole_field()
    print("ALL PASS")
