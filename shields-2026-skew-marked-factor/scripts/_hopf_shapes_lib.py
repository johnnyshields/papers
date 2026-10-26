"""Library for `check_hopf_action.py` and `check_thesis_marks.py` (Olson-Harris thesis, Sec. 5.4 and Sec. 5.6).

Written from the thesis's definitions (refs/OlsonHarris2024HopfApplications.pdf, Sec. 5.1-5.6).
The composition engine (_composition_engine.py) is imported only for
(i) shape enumeration, (ii) its I-IV mark logic (Hypothesis I comparison), and (iii) a cell-for-cell
cross-check of my own composition.  No empty outer is ever composed with the engine.

Conventions: a cell is (i, j), i increasing SOUTH, j EAST, content j - i.  "Removable on the left" = an
order ideal (closed under north/west within the shape); "removable on the right" = an order filter.

The shape Hopf algebra S is modelled exactly: a basis element is the congruence class of a (possibly
disconnected) shape = the sorted multiset of its normalized connected components; an element of S is a
dict key -> integer coefficient.  The product is multiset union.  The actions of p_n are
    [X] <- p_n = sum over ribbons Y removable on the LEFT,  |Y| = n, of (-1)^ht(Y) [X \\ Y]
    p_n -> [X] = sum over ribbons Y removable on the RIGHT, |Y| = n, of (-1)^ht(Y) [X \\ Y]
(thesis (5.11)-(5.12) with Cor. 5.1.15).
"""
import importlib.util
import os
import sys
from collections import defaultdict, Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ENGINE = os.path.join(HERE, '_composition_engine.py')
_spec = importlib.util.spec_from_file_location('eng11', ENGINE)
eng = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(eng)

normalize = eng.normalize
shift = eng.shift


# ----------------------------------------------------------------------------- basic shape tools
def components(X):
    X = set(X)
    out = []
    while X:
        c = X.pop()
        comp = {c}
        st = [c]
        while st:
            i, j = st.pop()
            for nb in ((i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1)):
                if nb in X:
                    X.remove(nb)
                    comp.add(nb)
                    st.append(nb)
        out.append(frozenset(comp))
    return out


def key_of(X):
    """Congruence class of a shape (components translated independently)."""
    return tuple(sorted(tuple(sorted(normalize(c))) for c in components(X)))


def rot(X):
    return normalize(frozenset((-i, -j) for i, j in X))


def tr(X):
    return normalize(frozenset((j, i) for i, j in X))


def nrows(X):
    return len({i for i, _ in X})


def ncols(X):
    return len({j for _, j in X})


def ndia(X):
    return len({j - i for i, j in X})


def is_ribbon(Y):
    return len(components(Y)) == 1 and len(Y) == ndia(Y)


def height(Y):
    return nrows(Y) - 1


def nw_border(X):
    X = set(X)
    return frozenset(c for c in X if (c[0] - 1, c[1] - 1) not in X)


def se_border(X):
    X = set(X)
    return frozenset(c for c in X if (c[0] + 1, c[1] + 1) not in X)


def is_ideal(Y, X):
    """Y removable on the left from X: closed under the cell north and the cell west, inside X."""
    Y = set(Y)
    for (i, j) in Y:
        for nb in ((i - 1, j), (i, j - 1)):
            if nb in X and nb not in Y:
                return False
    return True


def is_filter(Y, X):
    Y = set(Y)
    for (i, j) in Y:
        for nb in ((i + 1, j), (i, j + 1)):
            if nb in X and nb not in Y:
                return False
    return True


def removable_ribbons(X, n, side):
    """Every ribbon of n cells removable on `side` ('L' or 'R') from X.  Such a ribbon lies in NW(X)
    (resp. SE(X)): a cell with its NW (SE) neighbour in the ideal (filter) forces a 2x2 square by
    convexity.  So it is a content-interval of the border of one component.  As a guard, a brute
    force over ALL connected n-subsets is available in removable_ribbons_brute (used by the self-test)."""
    X = frozenset(X)
    out = []
    for C in components(X):
        B = nw_border(C) if side == 'L' else se_border(C)
        byc = {}
        for (i, j) in B:
            byc[j - i] = (i, j)
        cs = sorted(byc)
        for a in range(len(cs) - n + 1):
            seg = [byc[cs[t]] for t in range(a, a + n)]
            if cs[a + n - 1] - cs[a] != n - 1:
                continue
            Y = frozenset(seg)
            if len(components(Y)) != 1:
                continue
            if (is_ideal(Y, X) if side == 'L' else is_filter(Y, X)):
                out.append(Y)
    return out


def removable_ribbons_brute(X, n, side):
    X = frozenset(X)
    out = set()
    cells = sorted(X)
    # grow connected sets of size n
    seen = set()
    stack = [frozenset([c]) for c in cells]
    while stack:
        S = stack.pop()
        if S in seen:
            continue
        seen.add(S)
        if len(S) == n:
            if is_ribbon(S) and (is_ideal(S, X) if side == 'L' else is_filter(S, X)):
                out.add(S)
            continue
        for (i, j) in S:
            for nb in ((i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1)):
                if nb in X and nb not in S:
                    stack.append(S | {nb})
    return sorted(out, key=sorted)


# ----------------------------------------------------------------------------- the algebra S
def s_add(a, b, c=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + c * v
        if out[k] == 0:
            del out[k]
    return out


def s_mul(a, b):
    out = defaultdict(int)
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            out[tuple(sorted(k1 + k2))] += v1 * v2
    return {k: v for k, v in out.items() if v}


def s_pow(a, m):
    out = {(): 1}
    for _ in range(m):
        out = s_mul(out, a)
    return out


def s_basis(X, c=1):
    return {key_of(X): c} if X else {(): c}


def cells_of_key(k):
    """Place the components of a key far apart (an edge-disjoint realization)."""
    out = set()
    off = 0
    for comp in k:
        for (i, j) in comp:
            out.add((i + off, j + off * 3))
        off += 1000
    return frozenset(out)


def act(h, n, side):
    """side 'L': h <- p_n ;  side 'R': p_n -> h.  (p_n is primitive, so it acts as a derivation over
    components; acting on the realized disjoint union is the same thing.)"""
    out = defaultdict(int)
    for k, v in h.items():
        X = cells_of_key(k)
        for Y in removable_ribbons(X, n, side):
            out[key_of(X - Y)] += v * (-1) ** height(Y)
    return {k: v for k, v in out.items() if v}


# ----------------------------------------------------------------------------- marks
def all_marks(E):
    """Every (Wsw, Wne, case, v) with W nonempty satisfying Hypotheses I, II, III and the attachment
    dichotomy (the engine's w_candidates logic, Hypothesis I ON), WITHOUT the Hypothesis IV filter;
    returns dicts with flags iv_eng (engine, infinite strip) and v (Hypothesis V)."""
    E = frozenset(E)
    ne, sw = eng.ne_cell(E), eng.sw_cell(E)
    out = []
    if len(E) < 3:
        return out
    subs = eng.connected_skew_subdiagrams(E)
    tops = [s for s in subs if ne in s]
    bots = [s for s in subs if sw in s]
    bykey = defaultdict(list)
    for B in bots:
        bykey[(len(B), normalize(B))].append(B)
    raw, raw_all = [], []
    for T in tops:
        for B in bykey.get((len(T), normalize(T)), ()):
            raw_all.append(B)
            if T & B:
                continue
            raw.append((B, T))
    bigger = defaultdict(list)
    for B in raw_all:
        cs = (min(j - i for i, j in B), max(j - i for i, j in B))
        bigger[cs].append(B)
    for B, T in raw:
        cs = (min(j - i for i, j in B), max(j - i for i, j in B))
        hypI = not any(B < B2 for B2 in bigger[cs])
        O = E - B - T
        if not O or not eng.is_connected_skew(normalize(O)):
            continue
        if not eng.hyp_II(B, T):
            continue
        h3 = eng.hyp_III(E, B, T)
        case = eng.attachment_case(E, B, T, O)
        if case is None:
            continue
        v = eng.v_of_W(E, B, T)
        if v is None:
            continue
        out.append(dict(Wsw=B, Wne=T, case=case, v=v, hypI=hypI, hypIII=h3,
                        iv_eng=eng.hyp_IV(E, B, T, v), V=eng.hyp_V(E, B, T, case)))
    return out


def thesis_attachment(E, Wsw, Wne):
    """Thesis Sec. 5.3: b = NE box of Wsw has an O box east (horizontal) or north (vertical);
    the SW box of Wne has an O box west or south.  The thesis's text says 'west or south ... respectively
    vertically or horizontally' (p. 89); read literally, a one-row E = (3) with one-cell W would be a
    corner shape.  That is a wording slip: west = horizontal, south = vertical (MvW's convention, and
    the one every later argument of the thesis uses).  Implemented in the corrected reading."""
    O = E - Wsw - Wne
    b = eng.ne_cell(Wsw)
    e1 = (b[0], b[1] + 1) in O
    n1 = (b[0] - 1, b[1]) in O
    c = eng.sw_cell(Wne)
    w2 = (c[0], c[1] - 1) in O
    s2 = (c[0] + 1, c[1]) in O
    if e1 == n1 or w2 == s2:
        return None
    first = 'H' if e1 else 'V'
    second = 'H' if w2 else 'V'
    return {('H', 'H'): 'a', ('V', 'V'): 'b', ('H', 'V'): 'c', ('V', 'H'): 'd'}[(first, second)]


def thesis_bars(E, Wsw, Wne, v):
    """W-bar, W-underbar (from E u_W E, Sec. 5.3.1), O-bar, O-underbar and the thesis's properness."""
    E1 = frozenset(E)
    E2 = shift(E1, v)
    U = E1 | E2
    Wmid = frozenset(Wne)
    Wbar = frozenset(c for c in Wmid if (c[0] + 1, c[1] + 1) in U) | \
        frozenset(c for c in U if (c[0] + 1, c[1] + 1) in Wmid)
    Wund = frozenset(c for c in Wmid if (c[0] - 1, c[1] - 1) in U) | \
        frozenset(c for c in U if (c[0] - 1, c[1] - 1) in Wmid)
    O1 = E1 - frozenset(Wsw) - frozenset(Wne)
    Obar1 = frozenset(c for c in O1 if (c[0] + 1, c[1] + 1) in O1)
    Ound1 = frozenset(c for c in O1 if (c[0] - 1, c[1] - 1) in O1)
    Obar2, Ound2 = shift(Obar1, v), shift(Ound1, v)

    def touches(A, B):
        for (i, j) in A:
            for nb in ((i, j), (i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1)):
                if nb in B:
                    return True
        return False
    proper = not touches(Wbar, Obar1 | Obar2)
    proper_und = not touches(Wund, Ound1 | Ound2)
    return dict(Wbar=Wbar, Wund=Wund, Obar=Obar1, Ound=Ound1, O=O1, proper=proper,
                proper_und=proper_und, E1=E1, E2=E2)


# ----------------------------------------------------------------------------- composition (own)
def my_compose(D, E, Wsw, Wne, case, v):
    """D o_W E from the thesis's definition (Sec. 5.3.1).  Edge cases: one copy per box, east step =
    amalgamation (offset v), north step = near-amalgamation (offset v - (1,1) for W->O->W, v + (1,1) for
    W^O^W; for W empty, v = v_H and the W->O->W rule).  Corner cases: within a ribbon of the NW (case c)
    resp. SE (case d) decomposition both steps are amalgamations, each north step adds an extra copy of
    W one unit SE (c) / NW (d) of the overlapping W; a box SE of another is offset by (1,1)."""
    D = frozenset(D)
    off = {}
    stack = []
    if case in ('a', 'b'):
        un = (v[0] - 1, v[1] - 1) if case == 'a' else (v[0] + 1, v[1] + 1)
        steps = [((0, 1), v), ((0, -1), (-v[0], -v[1])), ((-1, 0), un), ((1, 0), (-un[0], -un[1]))]
        # whole D may be disconnected: seed every component
        for t, comp in enumerate(components(D)):
            s = min(comp)
            # components are placed independently (congruence); keep them far apart
            off[s] = (10 ** 4 * t, 10 ** 4 * t)
            stack.append(s)
        while stack:
            d = stack.pop()
            for (di, dj), (oi, oj) in steps:
                nb = (d[0] + di, d[1] + dj)
                if nb in D:
                    want = (off[d][0] + oi, off[d][1] + oj)
                    if nb in off:
                        assert off[nb] == want, 'composition not well defined'
                    else:
                        off[nb] = want
                        stack.append(nb)
        out = set()
        for d, o in off.items():
            out |= shift(E, o)
        return frozenset(out)
    # corner cases
    if case == 'c':
        layer = eng.diag_index(D, -1)     # NW ribbon index: 1 = NW border
        extra = (1, 1)
    else:
        layer = eng.diag_index(D, +1)
        extra = (-1, -1)
    # offsets: within a ribbon (same layer, edge-adjacent) east/north steps add v;
    # a box one unit SE of another (layer differs by one) is offset by (1,1).
    steps = [((0, 1), v), ((0, -1), (-v[0], -v[1])), ((-1, 0), v), ((1, 0), (-v[0], -v[1])),
             ((1, 1), (1, 1)), ((-1, -1), (-1, -1))]
    for t, comp in enumerate(components(D)):
        s = min(comp)
        off[s] = (10 ** 4 * t, 10 ** 4 * t)
        stack.append(s)
    while stack:
        d = stack.pop()
        for (di, dj), (oi, oj) in steps:
            nb = (d[0] + di, d[1] + dj)
            if nb not in D:
                continue
            if (di, dj) in ((0, 1), (0, -1), (-1, 0), (1, 0)) and layer[nb] != layer[d]:
                continue
            want = (off[d][0] + oi, off[d][1] + oj)
            if nb in off:
                assert off[nb] == want, 'corner composition not well defined'
            else:
                off[nb] = want
                stack.append(nb)
    out = set()
    for d, o in off.items():
        out |= shift(E, o)
    for d in D:
        nb = (d[0] - 1, d[1])            # north neighbour in the same ribbon -> extra W
        if nb in D and layer[nb] == layer[d]:
            o = off[d]                    # lower copy E_d; its Wne overlaps the upper copy's Wsw
            out |= shift(Wne, (o[0] + extra[0], o[1] + extra[1]))
    return frozenset(out)


def compose_checked(D, E, mk):
    """Own composition, asserted equal to the engine's (connected D only, never empty)."""
    F = my_compose(D, E, mk['Wsw'], mk['Wne'], mk['case'], mk['v'])
    if len(components(D)) == 1:
        G = eng.compose(D, E, mk['Wsw'], mk['Wne'], mk['case'], mk['v'])
        assert normalize(F) == G, ('compose mismatch', sorted(D), sorted(E), mk['case'])
    return F


# ----------------------------------------------------------------------------- key ribbons
def key_ribbons_edge_a(E, mk, bars):
    """Thesis Sec. 5.3.3 for W->O->W: K_down = E \\ (Wsw u Obar u Wbar_ne), K_up = E \\ (Wund_sw u Ound u Wne),
    with Wbar_ne computed in the pair (E, E+v) and Wund_sw in the pair (E-v, E)."""
    E = frozenset(E)
    v = mk['v']
    Wsw, Wne = frozenset(mk['Wsw']), frozenset(mk['Wne'])
    b_next = thesis_bars(E, Wsw, Wne, v)            # pair (E, E+v): Wmid = Wne of E
    b_prev = thesis_bars(shift(E, (-v[0], -v[1])), shift(Wsw, (-v[0], -v[1])), Wsw, v)  # Wmid = Wsw of E
    Wbar_ne = b_next['Wbar']
    Wund_sw = b_prev['Wund']
    Kd = E - Wsw - bars['Obar'] - Wbar_ne
    Ku = E - Wund_sw - bars['Ound'] - Wne
    return Ku, Kd, dict(Wbar_ne_in_E=Wbar_ne <= E, Wund_sw_in_E=Wund_sw <= E)


def nw_decomp_northbound(D):
    """xi(D): boxes with a box to the north in the same ribbon of the NW decomposition."""
    layer = eng.diag_index(D, -1)
    return sum(1 for d in D if (d[0] - 1, d[1]) in D and layer[(d[0] - 1, d[1])] == layer[d])


# ----------------------------------------------------------------------------- Jacobi-Trudi (exact)
_CTX = {}


def _ctx(n):
    import flint
    if n not in _CTX:
        _CTX[n] = flint.fmpz_mpoly_ctx.get(('h', n + 1), 'degrevlex')
    return _CTX[n]


def jt_poly(X, N=None):
    """Exact s_X in the free h-alphabet (h_0 = 1) as an fmpz_mpoly over gens h0..hN (h0 unused),
    by fraction-free Bareiss on the Jacobi-Trudi matrix of each component (leading principal minors
    are skew Schur functions of the top rows, hence nonzero; asserted).  Disconnected X: product."""
    X = frozenset(X)
    if N is None:
        N = max(1, len(X))
    ctx = _ctx(N)
    g = ctx.gens()
    one = ctx.from_dict({(0,) * (N + 1): 1})
    res = one
    for C in components(X):
        x, y = eng.beta_from_cells(normalize(C))
        r = len(x)

        def h(k):
            if k < 0:
                return ctx.from_dict({})
            if k == 0:
                return one
            return g[k]
        M = [[h(x[i] - y[j]) for j in range(r)] for i in range(r)]
        prev = one
        for k in range(r - 1):
            assert not M[k][k].is_zero()
            for i in range(k + 1, r):
                for j in range(k + 1, r):
                    num = M[i][j] * M[k][k] - M[i][k] * M[k][j]
                    q, rem = divmod(num, prev)
                    assert rem.is_zero()
                    M[i][j] = q
            prev = M[k][k]
        res = res * M[r - 1][r - 1]
    return res


def jt_equal(A, B):
    """Exact s_A == s_B, computed in the orientation with fewer rows (s_{X^t} = omega s_X)."""
    A, B = frozenset(A), frozenset(B)
    if len(A) != len(B):
        return False
    if sorted(Counter(len(c) for c in components(A)).items()) != \
            sorted(Counter(len(c) for c in components(B)).items()):
        pass
    if (nrows(A), ncols(A), ndia(A)) != (nrows(B), ncols(B), ndia(B)):
        return False
    if ncols(A) < nrows(A):
        A, B = frozenset((j, i) for i, j in A), frozenset((j, i) for i, j in B)
    N = len(A)
    return _jt_cached(normalize(A), N) == _jt_cached(normalize(B), N)


_JTC = {}


def _jt_cached(X, N):
    key = (X, N)
    if key not in _JTC:
        if len(_JTC) > 400:
            _JTC.clear()
        _JTC[key] = jt_poly(X, N)
    return _JTC[key]


# modular evaluation (may only REJECT)
P61 = (1 << 61) - 1


def jt_mod(X, pt):
    val = 1
    for C in components(frozenset(X)):
        x, y = eng.beta_from_cells(normalize(C))
        r = len(x)

        def h(k):
            if k < 0:
                return 0
            if k == 0:
                return 1
            return pt[k - 1]
        M = [[h(x[i] - y[j]) for j in range(r)] for i in range(r)]
        det = 1
        for c in range(r):
            piv = next((rr for rr in range(c, r) if M[rr][c] % P61), None)
            if piv is None:
                det = 0
                break
            if piv != c:
                M[c], M[piv] = M[piv], M[c]
                det = -det
            det = det * M[c][c] % P61
            inv = pow(M[c][c], P61 - 2, P61)
            for rr in range(c + 1, r):
                f = M[rr][c] * inv % P61
                if f:
                    for cc in range(c, r):
                        M[rr][cc] = (M[rr][cc] - f * M[c][cc]) % P61
        val = val * det % P61
    return val % P61


def connected_shapes(lo, hi):
    out = []
    for r, a in eng.enum_rho_a(hi, minsize=lo):
        out.append(eng.cells_from_rho_a(r, a))
    return out


def profile_cells(rows, gaps):
    """Census profile (row lengths top to bottom, gaps = overlap - 1) -> cells."""
    return eng.cells_from_rho_a(tuple(rows), tuple(g + 1 for g in gaps))
