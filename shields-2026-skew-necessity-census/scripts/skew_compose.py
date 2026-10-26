"""Marked composition of skew diagrams (McNamara-van Willigenburg, Def. 3.11), Hypotheses I-IV,
and two complete searches for proper charts F = D o_W E.

Cells are (i, j), i increasing to the south and j to the east; content c(i, j) = j - i; e = (1, 1).
A diagram is a frozenset of cells, normalized to minimal row 0 and minimal column 0.

A MARK on a connected diagram E is (W_sw, W_ne, case, v): two disjoint translates W_ne = W_sw + v of a
connected skew diagram W, W_sw containing the southwesternmost cell of E and W_ne its northeasternmost
cell, satisfying Hypotheses I-IV, with attachment case (a) W->O->W, (b) W^O^W, (c) W->O^W, (d) W^O->W.
The empty W uses the horizontal edge reading of Example 3.7 (case (a), v = ne(E) - sw(E) + (0, 1)).
The PERIOD of the mark is q = c(v) = N_E - N_W.

COMPOSITION (cell form of Def. 3.11).  For d = (i, i + t) in D, with the rows of the content-t diagonal
of D forming [l_t, h_t], the copy E_d is E + L(d) with
    (a) L = t v + i e,  (b) L = t v - i e,  (c) L = t v + (i - l_t) e,  (d) L = t v - (h_t - i) e,
and in case (c) (resp. (d)) every vertical pair of D on one northwest (resp. southeast) boundary ribbon,
with lower cell d, adds the supplemental copy W_ne + L(d) + e (resp. W_ne + L(d) - e).

A CHART (proper root) of F is (D, mark on E) with D, E connected, |D|, |E| >= 2 and D o E = F.
"""
from collections import Counter, defaultdict

E1 = (1, 1)


# ------------------------------------------------------------------------------------------ cell sets
def normalize(S):
    if not S:
        return frozenset()
    i0 = min(i for i, _ in S)
    j0 = min(j for _, j in S)
    return frozenset((i - i0, j - j0) for i, j in S)


def shift(S, v):
    return frozenset((i + v[0], j + v[1]) for i, j in S)


def row_intervals(S):
    rows = defaultdict(list)
    for i, j in S:
        rows[i].append(j)
    out = {}
    for i, js in rows.items():
        lo, hi = min(js), max(js)
        if hi - lo + 1 != len(js):
            return None
        out[i] = (lo, hi)
    return out


def is_connected_skew(S):
    """Nonempty, rows are intervals in consecutive rows, both ends weakly decreasing downward, and
    consecutive rows share at least one column."""
    if not S:
        return False
    ri = row_intervals(S)
    if ri is None:
        return False
    ks = sorted(ri)
    if ks != list(range(ks[0], ks[0] + len(ks))):
        return False
    for a, b in zip(ks, ks[1:]):
        (la, ha), (lb, hb) = ri[a], ri[b]
        if lb > la or hb > ha or hb < la:
            return False
    return True


def sw_cell(S):
    i = max(i for i, _ in S)
    return i, min(j for a, j in S if a == i)


def ne_cell(S):
    i = min(i for i, _ in S)
    return i, max(j for a, j in S if a == i)


def rotate(S):
    return normalize(frozenset((-i, -j) for i, j in S))


def transpose(S):
    return normalize(frozenset((j, i) for i, j in S))


def antitranspose(S):
    return normalize(frozenset((-j, -i) for i, j in S))


def contents(S):
    return Counter(j - i for i, j in S)


def nd(S):
    """Number of occupied diagonals."""
    c = [j - i for i, j in S]
    return max(c) - min(c) + 1 if c else 0


def height_seq(S):
    H = contents(S)
    c0 = min(H)
    return tuple(H[c] for c in range(c0, max(H) + 1))


# ------------------------------------------------------------------------------------------ subdiagrams
def connected_subdiagrams(F):
    """Every connected skew subdiagram of F, in place: consecutive rows of F, each an interval inside the
    row of F, every lower interval weakly left of the upper one at both ends and sharing a column."""
    ri = row_intervals(F)
    R = sorted(ri)
    out = []
    for a in range(len(R)):
        stack = [(a, None, ())]
        while stack:
            idx, prev, acc = stack.pop()
            if acc:
                out.append(frozenset(acc))
            if idx == len(R):
                continue
            i = R[idx]
            lo, hi = ri[i]
            for l in range(lo, hi + 1):
                for r in range(l, hi + 1):
                    if prev is not None:
                        pl, pr = prev
                        if l > pl or r > pr or r < pl:
                            continue
                    stack.append((idx + 1, (l, r), acc + tuple((i, c) for c in range(l, r + 1))))
    return out


# ------------------------------------------------------------------------------------------ marks
def attachment_case(B, T, O):
    oi, oj = sw_cell(O)
    lo_h, lo_v = (oi, oj - 1) in B, (oi + 1, oj) in B
    ni, nj = ne_cell(O)
    up_h, up_v = (ni, nj + 1) in T, (ni - 1, nj) in T
    if lo_h == lo_v or up_h == up_v:
        return None
    if lo_h and up_h:
        return 'a'
    if lo_v and up_v:
        return 'b'
    return 'c' if lo_h else 'd'


def hyp_IV(E, B, T, v, K=8):
    """No copy of O-hat is adjacent to a copy of W-hat in the infinite amalgamation (Def. 3.20 and
    Hypothesis 3.22).  Copies E + kv and E + k'v share a diagonal only when |k - k'| <= 1 (because
    2q > N_E), so the interior copies 2..K-3 of a K-fold amalgamation see exactly their infinite
    neighborhood."""
    O = E - B - T
    Ebar = set()
    for t in range(K):
        Ebar |= shift(E, (t * v[0], t * v[1]))
    Oh = []
    for t in range(2, K - 2):
        Ot = shift(O, (t * v[0], t * v[1]))
        Oh.append(frozenset(c for c in Ot if (c[0] + 1, c[1] + 1) in Ot))
    Wh = []
    for t in range(1, K):
        Wt = shift(B, (t * v[0], t * v[1]))
        w = {c for c in Ebar if (c[0] + 1, c[1] + 1) in Wt}
        w |= {c for c in Wt if (c[0] + 1, c[1] + 1) in Ebar}
        Wh.append(w)
    for o in Oh:
        for w in Wh:
            if o & w:
                return False
            for (i, j) in o:
                if (i + 1, j) in w or (i - 1, j) in w or (i, j + 1) in w or (i, j - 1) in w:
                    return False
    return True


_MARKS = {}


def marks(E):
    """Every legal mark of the normalized connected diagram E, as tuples (B, T, case, v, q):
    the empty mark (horizontal reading) and every nonempty W satisfying Hypotheses I-IV."""
    got = _MARKS.get(E)
    if got is not None:
        return got
    ne, sw = ne_cell(E), sw_cell(E)
    NE = nd(E)
    vH = (ne[0] - sw[0], ne[1] - sw[1] + 1)
    out = [(frozenset(), frozenset(), 'a', vH, NE)]
    if len(E) >= 3:
        subs = connected_subdiagrams(E)
        tops = {}
        for s in subs:
            if ne in s:
                tops[normalize(s)] = s
        pairs, lying = [], []
        for s in subs:
            if sw in s:
                t = tops.get(normalize(s))
                if t is not None:
                    lying.append(s)              # W = s lies in the top and the bottom of E
                    if not (s & t):
                        pairs.append((s, t))
        rng = defaultdict(list)
        for s in lying:
            c = [j - i for i, j in s]
            rng[(min(c), max(c))].append(s)
        for B, T in pairs:
            cB = [j - i for i, j in B]
            # Hypothesis I: no strictly larger W' on the same diagonals lies in the top and bottom.
            if any(B < B2 for B2 in rng[(min(cB), max(cB))]):
                continue
            # Hypothesis II: a diagonal strictly between the copies meets neither.
            if min(j - i for i, j in T) <= max(cB) + 1:
                continue
            O = E - B - T
            if not is_connected_skew(O):
                continue
            # Hypothesis III: removing either copy leaves a connected skew diagram.
            if not (is_connected_skew(E - T) and is_connected_skew(E - B)):
                continue
            case = attachment_case(B, T, O)
            if case is None:
                continue
            b0, t0 = min(B), min(T)
            v = (t0[0] - b0[0], t0[1] - b0[1])
            assert shift(B, v) == T
            if not hyp_IV(E, B, T, v):
                continue
            out.append((B, T, case, v, v[1] - v[0]))
    for (B, T, case, v, q) in out:
        assert 2 * q > NE and q <= NE, 'every legal mark has N_E < 2q'
    _MARKS[E] = out
    return out


def find_mark(E, B, T, case):
    """The legal mark (B, T, case, v, q) of E with the given copies and case."""
    got = [m for m in marks(E) if m[0] == B and m[1] == T and m[2] == case]
    assert len(got) == 1, 'not a legal mark'
    return got[0]


def vertical_empty_mark(E):
    """The vertical edge reading of the empty W (displacement v_H - e); used only for the gauge identity."""
    ne, sw = ne_cell(E), sw_cell(E)
    return (frozenset(), frozenset(), 'b', (ne[0] - sw[0] - 1, ne[1] - sw[1]), nd(E))


def rotate_mark(E, B, T, case, v):
    """(E*, W*_sw, W*_ne, case*, v*): rotation exchanges the copies and the cases (c), (d)."""
    rE = [(-i, -j) for i, j in E]
    di = -min(i for i, _ in rE)
    dj = -min(j for _, j in rE)
    Er = frozenset((i + di, j + dj) for i, j in rE)
    if not B:
        if case == 'a':
            return Er, frozenset(), frozenset(), 'a', marks(Er)[0][3]
        m = vertical_empty_mark(Er)
        return Er, frozenset(), frozenset(), 'b', m[3]
    Br = frozenset((-i + di, -j + dj) for i, j in T)
    Tr = frozenset((-i + di, -j + dj) for i, j in B)
    cr = {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'}[case]
    b0, t0 = min(Br), min(Tr)
    return Er, Br, Tr, cr, (t0[0] - b0[0], t0[1] - b0[1])


# ------------------------------------------------------------------------------------------ composition
def offsets(D, v, case):
    """L(d) for every d in D, and the boundary-ribbon data needed for the supplemental copies."""
    rows_on = defaultdict(list)
    for (i, j) in D:
        rows_on[j - i].append(i)
    lo = {t: min(r) for t, r in rows_on.items()}
    hi = {t: max(r) for t, r in rows_on.items()}
    L = {}
    for (i, j) in D:
        t = j - i
        if case == 'a':
            k = i
        elif case == 'b':
            k = -i
        elif case == 'c':
            k = i - lo[t]
        else:
            k = -(hi[t] - i)
        L[(i, j)] = (t * v[0] + k, t * v[1] + k)
    return L, lo, hi


def compose(D, E, B, T, case, v):
    """D o_W E as a normalized cell set."""
    L, lo, hi = offsets(D, v, case)
    out = set()
    for d, o in L.items():
        out |= shift(E, o)
    if case in ('c', 'd'):
        for (i, j) in D:
            if (i - 1, j) not in D:
                continue
            t = j - i
            # (i-1, j) lies on diagonal t + 1; same boundary ribbon iff the ribbon ranks agree
            if case == 'c' and (i - lo[t]) == (i - 1 - lo[t + 1]):
                o = L[(i, j)]
                out |= shift(T, (o[0] + 1, o[1] + 1))
            if case == 'd' and (hi[t] - i) == (hi[t + 1] - (i - 1)):
                o = L[(i, j)]
                out |= shift(T, (o[0] - 1, o[1] - 1))
    return normalize(frozenset(out))


def composes_to(D, E, B, T, case, v, F):
    """Is D o_W E equal to the normalized diagram F?  Each copy is tested for containment in F as it is
    placed (early rejection), and the union is compared with F at the end."""
    L, lo, hi = offsets(D, v, case)
    sup = []
    if case in ('c', 'd'):
        for (i, j) in D:
            if (i - 1, j) not in D:
                continue
            t = j - i
            o = L[(i, j)]
            if case == 'c' and (i - lo[t]) == (i - 1 - lo[t + 1]):
                sup.append((o[0] + 1, o[1] + 1))
            if case == 'd' and (hi[t] - i) == (hi[t + 1] - (i - 1)):
                sup.append((o[0] - 1, o[1] - 1))
    mrT = min(i for i, _ in T) if T else 0
    mcT = min(j for _, j in T) if T else 0
    r0 = min([o[0] for o in L.values()] + [s[0] + mrT for s in sup])
    c0 = min([o[1] for o in L.values()] + [s[1] + mcT for s in sup])
    union = set()
    for o in L.values():
        cs = {(i + o[0] - r0, j + o[1] - c0) for (i, j) in E}
        if not cs <= F:
            return False
        union |= cs
    for s in sup:
        cs = {(i + s[0] - r0, j + s[1] - c0) for (i, j) in T}
        if not cs <= F:
            return False
        union |= cs
    return len(union) == len(F)


def outer_from_rows(hs, da, v, case):
    """Cases (a), (b): the outer is determined by its diagonal heights hs and the lowest-row shifts
    da_t = a_F(tq + w') - a_F(w') of the private diagonals (copy origins t v + i e, resp. t v - i e)."""
    out = set()
    for t, h in enumerate(hs):
        if case == 'a':
            lo = da[t] - t * v[0]
        else:
            lo = -(da[t] - t * v[0]) - h + 1
        out |= {(i, i + t) for i in range(lo, lo + h)}
    S = normalize(frozenset(out))
    return S if is_connected_skew(S) else None


# ------------------------------------------------------------------------------------------ outers from heights
_SWH = {}


def shapes_with_heights(hs):
    """Every connected skew diagram whose consecutive diagonals have heights hs.  In lambda/mu, row i
    meets diagonal c iff mu_i - i <= c <= lambda_i - i - 1 and both bounds strictly decrease in i, so
    the rows on diagonal c form an interval [a_c, b_c] with a_{c+1} in {a_c - 1, a_c} and
    b_{c+1} in {b_c - 1, b_c}; every diagram is among the candidates and is_connected_skew filters."""
    hs = tuple(hs)
    got = _SWH.get(hs)
    if got is not None:
        return got
    r = len(hs)
    out = set()
    if r >= 1 and hs[0] == 1 and hs[-1] == 1 and min(hs) >= 1:
        def rec(t, a, acc):
            if t == r:
                S = normalize(frozenset(acc))
                if is_connected_skew(S):
                    out.add(S)
                return
            b_prev = a + hs[t - 1] - 1
            for na in (a - 1, a):
                nb = na + hs[t] - 1
                if nb != b_prev and nb != b_prev - 1:
                    continue
                rec(t + 1, na, acc + [(i, i + t) for i in range(na, nb + 1)])
        rec(1, 0, [(0, 0)])
    got = sorted(out, key=sorted)
    _SWH[hs] = got
    return got


def outer_heights(HF, HE, q, w, ND):
    """Private-diagonal reading: h_D(t) = h_F(tq + w') - h_E(w') + 1 for every w' in [w, q-1], where
    w = N_E - q.  Returns the heights, or None when the private diagonals disagree."""
    hs = None
    for wp in range(w, q):
        h = tuple(HF[t * q + wp] - HE[wp] + 1 for t in range(ND))
        if hs is None:
            hs = h
        elif h != hs:
            return None
    if hs is None or hs[0] != 1 or hs[-1] != 1 or min(hs) < 1:
        return None
    if any(abs(a - b) > 1 for a, b in zip(hs, hs[1:])):
        return None
    return hs


# ------------------------------------------------------------------------------------------ finders
def chart_key(D, E, B, T, case):
    return (D, E, B, T, case)


def finder_subdiagram(F):
    """Search S: every connected subdiagram of F as inner, every legal mark, outer heights from the
    private diagonals, every outer with those heights.  Returns {chart: period}."""
    F = normalize(F)
    HF = height_seq(F)
    NF = len(HF)
    found = {}
    seen = set()
    for S in connected_subdiagrams(F):
        if len(S) < 2:
            continue
        E = normalize(S)
        if E in seen:
            continue
        seen.add(E)
        HE = height_seq(E)
        NE = len(HE)
        plan = {}
        for q in range(NE // 2 + 1, NE + 1):
            m, rem = divmod(NF - NE, q)
            if rem or m < 1:
                continue
            hs = outer_heights(HF, HE, q, NE - q, m + 1)
            if hs is not None:
                plan[q] = hs
        if not plan:
            continue
        for (B, T, case, v, q) in marks(E):
            hs = plan.get(q)
            if hs is None:
                continue
            for D in shapes_with_heights(hs):
                if len(D) >= 2 and compose(D, E, B, T, case, v) == F:
                    found[chart_key(D, E, B, T, case)] = q
    return found


def finder_band(F):
    """Search B: for each period q (then w = N_F mod q and N_D = N_F div q >= 2), the inner is read off F
    directly -- its first q diagonals are F's first q diagonals and its last q diagonals are F's last
    q diagonals, aligned on the private diagonals [w, q-1].  Before any cell set is built, two
    consequences of the private-diagonal lemma are tested: on each block t the differences
    h_F(tq + w') - h_F(w') and a_F(tq + w') - a_F(w') (a = lowest row on a diagonal) do not depend
    on w' in [w, q-1].  Returns {chart: period}."""
    F = normalize(F)
    HF = height_seq(F)
    NF = len(HF)
    c0 = min(j - i for i, j in F)
    rows_on = defaultdict(list)
    for (i, j) in F:
        rows_on[j - i - c0].append(i)
    aF = [min(rows_on[c]) for c in range(NF)]
    Fset = set(F)
    found = {}
    for q in range(2, NF // 2 + 1):
        w = NF % q
        ND = NF // q
        ok = True
        for t in range(1, ND):
            dh = HF[t * q + w] - HF[w]
            da = aF[t * q + w] - aF[w]
            for wp in range(w + 1, q):
                if HF[t * q + wp] - HF[wp] != dh or aF[t * q + wp] - aF[wp] != da:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue
        sh = (ND - 1) * q
        a = aF[w + sh] - aF[w]
        A = {(i, j) for (i, j) in F if j - i - c0 < q}
        Bt = {(i - a, j - a - sh) for (i, j) in F if j - i - c0 >= NF - q}
        if {x for x in A if x[1] - x[0] - c0 >= w} != {x for x in Bt if x[1] - x[0] - c0 <= q - 1}:
            continue
        E0 = frozenset(A | Bt)
        if not is_connected_skew(E0):
            continue
        E = normalize(E0)
        s0 = (min(i for i, _ in E0), min(j for _, j in E0))
        HE = height_seq(E)
        hs = outer_heights(HF, HE, q, w, ND)
        if hs is None:
            continue
        da = [aF[t * q + w] - aF[w] for t in range(ND)]
        for (B, T, case, v, qq) in marks(E):
            if qq != q:
                continue
            if case in ('a', 'b'):
                D = outer_from_rows(hs, da, v, case)
                cand = [D] if D is not None else []
            else:
                # In the mixed cases the copies on diagonal t sit at s0 + t v +- k e, k < h_D(t),
                # whatever the shape of D; they must all lie in F.
                sg = 1 if case == 'c' else -1
                if not all((i + s0[0] + t * v[0] + sg * k, j + s0[1] + t * v[1] + sg * k) in Fset
                           for t in range(ND) for k in range(hs[t]) for (i, j) in E):
                    continue
                cand = shapes_with_heights(hs)
            for D in cand:
                if len(D) >= 2 and composes_to(D, E, B, T, case, v, F):
                    assert compose(D, E, B, T, case, v) == F
                    found[chart_key(D, E, B, T, case)] = q
    return found


def size_bound_holds(F, D, E, q):
    """|F| >= q|D| + N_E - q for every chart of period q."""
    return len(F) >= q * len(D) + nd(E) - q


def private_heights_hold(F, D, E, q):
    HF, HE, HD = height_seq(F), height_seq(E), height_seq(D)
    if len(HF) != (len(HD) - 1) * q + len(HE):
        return False
    return all(HF[t * q + wp] == HD[t] + HE[wp] - 1
               for t in range(len(HD)) for wp in range(len(HE) - q, q))


# ------------------------------------------------------------------------------------------ marked inners up to rotation
def marked_tuple(E, B, T, case):
    return (tuple(sorted(E)), tuple(sorted(B)), tuple(sorted(T)), case)


def canon_marked(E, B, T, case, v):
    Er, Br, Tr, cr, vr = rotate_mark(E, B, T, case, v)
    return min(marked_tuple(E, B, T, case), marked_tuple(Er, Br, Tr, cr))


def is_symmetric_marked(E, B, T, case, v):
    Er, Br, Tr, cr, vr = rotate_mark(E, B, T, case, v)
    return marked_tuple(E, B, T, case) == marked_tuple(Er, Br, Tr, cr)


_CHARTS = {}


def charts(F):
    """Every proper chart of F (search B), as a sorted list of (D, E, B, T, case, v, q)."""
    F = normalize(F)
    got = _CHARTS.get(F)
    if got is None:
        got = []
        for (D, E, B, T, case), q in finder_band(F).items():
            got.append((D, E, B, T, case, find_mark(E, B, T, case)[3], q))
        got.sort(key=lambda c: (c[6], len(c[0]), sorted(c[1]), sorted(c[2]), c[4], sorted(c[0])))
        _CHARTS[F] = got
    return got


def cost(F, q):
    """(N_W, N_E) of a chart of period q: N_W = N_F mod q and N_E = q + N_W."""
    w = nd(F) % q
    return (w, q + w)


def minimal_charts(F):
    cs = charts(F)
    if not cs:
        return []
    best = min(cost(F, c[6]) for c in cs)
    return [c for c in cs if cost(F, c[6]) == best]
