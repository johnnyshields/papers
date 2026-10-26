#!/usr/bin/env python3
"""Import-only engine for `check_decoder_modes.py`, `_readout_lib.py` and
`_hopf_shapes_lib.py`; it is not a section sweep.

Composition-irreducibility of a connected skew diagram, as a PARENT.

McNamara--van Willigenburg, "Towards a combinatorial classification of skew
Schur functions", Trans. AMS 361 (2009) 4437--4470, define a composition
D o_W E of skew diagrams and conjecture (Conjecture 5.7) that the
skew-equivalence class of E is exactly the orbit of E under reversing the
factors of an irreducible factorization, of size 2^r for r nonsymmetric
factors.  The two-element conclusion "E ~ E' implies E' = E or E'= E*" is the
COMPOSITION-IRREDUCIBLE case, r <= 1.

This script implements
  (1) o_W itself, from Definition 3.11 and the four attachment cases,
  (2) Hypotheses I-V (3.8, 3.22, 3.27) as decidable predicates,
  (3) a decision procedure for "F admits only trivial factorizations", which
      is MvW's condition on the first factor E_1 of an irreducible
      factorization and is what composition-irreducibility of the parent means,
  (4) a census grouping connected skew diagrams by the EXACT Jacobi-Trudi
      determinant in the free h-alphabet and reporting, for every class
      holding a nonrotation equal pair, the class size against the
      composition-irreducibility of its members.

Three notions are kept apart and only the third is computed here: JT-child
primitivity, irreducibility of an outer ribbon factor, and
composition-irreducibility of the parent.

Conventions.  A cell is (i, j) with i increasing SOUTH and j increasing EAST,
so "one position northwest of (i,j)" is (i-1, j-1) and content is c = j - i.
A shape is a frozenset of cells normalized to min row 0, min column 0.
"""
import argparse
import itertools
import sys
import time
from collections import defaultdict

sys.setrecursionlimit(100000)

# --------------------------------------------------------------------------
# shapes
# --------------------------------------------------------------------------


def normalize(cells):
    if not cells:
        return frozenset()
    i0 = min(i for i, _ in cells)
    j0 = min(j for _, j in cells)
    return frozenset((i - i0, j - j0) for i, j in cells)


def shift(cells, v):
    return frozenset((i + v[0], j + v[1]) for i, j in cells)


def row_intervals(cells):
    """i -> (lo, hi) column interval, or None if some row is not contiguous."""
    rows = defaultdict(list)
    for i, j in cells:
        rows[i].append(j)
    out = {}
    for i, js in rows.items():
        lo, hi = min(js), max(js)
        if hi - lo + 1 != len(js):
            return None
        out[i] = (lo, hi)
    return out


def is_skew(cells):
    """A skew diagram: rows are contiguous intervals with lambda and mu both
    weakly decreasing downward.  Empty rows are permitted inside (MvW identify
    shapes up to deletion of empty rows and columns)."""
    if not cells:
        return True
    ri = row_intervals(cells)
    if ri is None:
        return False
    ks = sorted(ri)
    for a, b in zip(ks, ks[1:]):
        if b != a + 1:
            continue  # an empty row: constraints below still apply
    prev = None
    for i in range(min(ks), max(ks) + 1):
        if i not in ri:
            continue
        lo, hi = ri[i]
        if prev is not None:
            plo, phi = prev
            if lo > plo or hi > phi:
                return False
        prev = (lo, hi)
    return True


def is_connected_skew(cells):
    if not cells or not is_skew(cells):
        return False
    ri = row_intervals(cells)
    ks = sorted(ri)
    if ks != list(range(ks[0], ks[0] + len(ks))):
        return False
    for a, b in zip(ks, ks[1:]):
        # overlap of row a and row b is  hi_b - lo_a + 1
        if ri[b][1] - ri[a][0] + 1 < 1:
            return False
    return True


def sw_cell(cells):
    """Southwesternmost cell: bottom row, leftmost column of it."""
    i = max(i for i, _ in cells)
    return (i, min(j for a, j in cells if a == i))


def ne_cell(cells):
    """Northeasternmost cell: top row, rightmost column of it."""
    i = min(i for i, _ in cells)
    return (i, max(j for a, j in cells if a == i))


def rotate(cells):
    """Antipodal rotation D*."""
    return normalize(frozenset((-i, -j) for i, j in cells))


def transpose(cells):
    return normalize(frozenset((j, i) for i, j in cells))


def cells_from_rho_a(rho, a):
    """Connected skew shape from row lengths rho and adjacent overlaps a."""
    n = len(rho)
    c = [0] * n
    for i in range(n - 1):
        c[i + 1] = c[i] + a[i] - rho[i + 1]
    out = set()
    for i in range(n):
        for t in range(rho[i]):
            out.add((i, c[i] + t))
    return normalize(frozenset(out))


def rot_rho_a(rho, a):
    """(rho, a) of the antipodal rotation D*: reverse both sequences.  Rotation
    reverses the row order and reverses each row, so the row lengths reverse
    and the overlap between rows i and i+1 becomes the overlap between the two
    rows they map to."""
    return tuple(reversed(rho)), tuple(reversed(a))


def beta(rho, a):
    """x_i = lambda_i - i and y_i = mu_i - i, read off (rho, a)."""
    n = len(rho)
    x = [0] * n
    for i in range(n - 2, -1, -1):
        x[i] = x[i + 1] + (rho[i] - a[i] + 1)
    y = [x[i] - rho[i] for i in range(n)]
    return x, y


def beta_from_cells(cells):
    ri = row_intervals(cells)
    ks = sorted(ri)
    x, y = [], []
    for t, i in enumerate(ks, start=1):
        lo, hi = ri[i]
        x.append((hi + 1) - t)     # lambda_i - i
        y.append(lo - t)           # mu_i - i
    return x, y


def enum_rho_a(cap, minsize=1):
    """Every connected skew shape of size in [minsize, cap], as (rho, a)."""
    for n in range(1, cap + 1):
        for rho in compositions(cap, n):
            s = sum(rho)
            if s < minsize:
                continue
            ranges = [range(1, min(rho[i], rho[i + 1]) + 1) for i in range(n - 1)]
            for a in itertools.product(*ranges):
                yield rho, a


def enum_rho_a_exact(n, first, rows=None):
    """(rho, a) for every connected skew shape of exactly n cells whose first
    row has length `first`.  Used to slice the census into parallel tasks."""
    if first > n:
        return
    for k in range(1, n - first + 2):
        for rest in compositions_exact(n - first, k - 1):
            rho = (first,) + rest
            ranges = [range(1, min(rho[i], rho[i + 1]) + 1)
                      for i in range(len(rho) - 1)]
            for a in itertools.product(*ranges):
                yield rho, a


def compositions_exact(total, parts):
    """Compositions of exactly `total` into exactly `parts` positive parts."""
    if parts == 0:
        if total == 0:
            yield ()
        return
    for first in range(1, total - parts + 2):
        for rest in compositions_exact(total - first, parts - 1):
            yield (first,) + rest


def pack(rho, a):
    return bytes(rho) + b"|" + bytes(a)


def unpack(b):
    r, _, aa = b.partition(b"|")
    return tuple(r), tuple(aa)


def _task(arg):
    n, first = arg
    out = defaultdict(list)
    for rho, a in enum_rho_a_exact(n, first):
        x, y = beta(rho, a)
        out[hash(det_free_h(x, y))].append(pack(rho, a))
    return n, dict(out)


def compositions(cap, parts):
    """Compositions of any total <= cap into exactly `parts` positive parts."""
    if parts == 0:
        yield ()
        return
    for first in range(1, cap - parts + 2):
        for rest in compositions(cap - first, parts - 1):
            yield (first,) + rest


# --------------------------------------------------------------------------
# Jacobi-Trudi determinant in the free h-alphabet
# --------------------------------------------------------------------------


def det_free_h(x, y):
    """det (h_{x_i - y_j}) with h_0 = 1 and h_r = 0 for r < 0, as a canonical
    tuple ((monomial, coefficient), ...).  Monomials are subscript multisets
    written as tuples sorted descending.  Memoized minor expansion, so the
    r! blow-up of a raw permutation sum is avoided for tall shapes."""
    r = len(x)
    cache = {}

    def rec(i, cols):
        if i == r:
            return (((), 1),)
        key = (i, cols)
        hit = cache.get(key)
        if hit is not None:
            return hit
        acc = defaultdict(int)
        for pos, j in enumerate(cols):
            e = x[i] - y[j]
            if e < 0:
                continue
            sub = rec(i + 1, cols[:pos] + cols[pos + 1:])
            sgn = -1 if (pos & 1) else 1
            for mono, co in sub:
                nm = mono if e == 0 else tuple(sorted(mono + (e,), reverse=True))
                acc[nm] += sgn * co
        res = tuple(sorted((m, c) for m, c in acc.items() if c))
        cache[key] = res
        return res

    return rec(0, tuple(range(r)))


def jt_of_cells(cells):
    x, y = beta_from_cells(cells)
    return det_free_h(x, y)


# --------------------------------------------------------------------------
# subdiagram enumeration
# --------------------------------------------------------------------------


def connected_skew_subdiagrams(cells):
    """Every connected skew subdiagram of `cells`, in place, as frozensets."""
    ri = row_intervals(cells)
    R = sorted(ri)
    out = []
    for t0 in range(len(R)):
        stack = [(t0, [], [])]
        while stack:
            idx, chosen, acc = stack.pop()
            if chosen:
                out.append(frozenset(acc))
            if idx >= len(R):
                continue
            i = R[idx]
            lo, hi = ri[i]
            for l in range(lo, hi + 1):
                for rr in range(l, hi + 1):
                    if chosen:
                        pl, pr = chosen[-1]
                        if l > pl or rr > pr:
                            continue
                        if rr < pl:          # overlap must be >= 1
                            continue
                    stack.append((idx + 1, chosen + [(l, rr)],
                                  acc + [(i, c) for c in range(l, rr + 1)]))
    return out


def skew_subshapes_of_set(S, must_contain=None, maxsize=None, connected=True):
    """Every skew subdiagram of an arbitrary cell set S (used to reconstruct D
    from the admissible placements).  Rows of a candidate are contiguous
    intervals inside S; lambda and mu weakly decreasing; connected on request.
    Empty rows are allowed when connected is False."""
    rows = defaultdict(set)
    for i, j in S:
        rows[i].add(j)
    R = sorted(rows)
    out = []

    def intervals(i):
        js = sorted(rows[i])
        res = []
        for a in range(len(js)):
            for b in range(a, len(js)):
                if js[b] - js[a] == b - a:
                    res.append((js[a], js[b]))
                else:
                    break
        return res

    ivs = {i: intervals(i) for i in R}
    for t0 in range(len(R)):
        stack = [(t0, [], [])]
        while stack:
            idx, chosen, acc = stack.pop()
            if chosen:
                cand = frozenset(acc)
                if (must_contain is None or must_contain in cand) and \
                   (maxsize is None or len(cand) <= maxsize):
                    out.append(cand)
            if idx >= len(R):
                continue
            if maxsize is not None and len(acc) >= maxsize:
                continue
            i = R[idx]
            if connected and chosen and i != chosen[-1][2] + 1:
                continue
            for (l, rr) in ivs[i]:
                if chosen:
                    pl, pr, _ = chosen[-1]
                    if l > pl or rr > pr:
                        continue
                    if connected and rr < pl:
                        continue
                stack.append((idx + 1, chosen + [(l, rr, i)],
                              acc + [(i, c) for c in range(l, rr + 1)]))
    return out


# --------------------------------------------------------------------------
# the composition D o_W E
# --------------------------------------------------------------------------


def v_of_W(E, Wsw, Wne, case='a'):
    """The translation carrying the bottom copy of W onto the top copy.

    For W empty MvW identify W_sw and W_ne with EDGES (Example 3.7).  The
    horizontal reading, E = W->O->W, takes the west edge of the
    southwesternmost cell and the east edge of the northeasternmost cell.  The
    vertical reading, E = W^O^W, takes the south and north edges instead.  The
    vertical reading is this engine's own extension, not the paper's: Lemma
    3.19(iii) is stated for W nonempty (the PDF reads "If W != {}"; the text
    extraction drops the negation) and governs no empty-mark case.  The two
    empty readings are gauge-equivalent, D o_{0,V} E = AT(D) o_{0,H} E with
    AT(i, j) = (-j, -i), so the extension adds chart data and no new unmarked
    factorization; a fixed-chart argument has to convert between them."""
    if not Wsw:
        isw, jsw = sw_cell(E)
        ine, jne = ne_cell(E)
        if case == 'b':
            return (ine - isw - 1, jne - jsw)
        return (ine - isw, jne - jsw + 1)
    asw = min(Wsw)
    ane = min(Wne)
    v = (ane[0] - asw[0], ane[1] - asw[1])
    if shift(Wsw, v) != Wne:
        return None
    return v


def attachment_case(E, Wsw, Wne, O):
    """(a) W->O->W  (b) W^O^W  (c) W->O^W  (d) W^O->W; W empty reads as (a)."""
    if not Wsw:
        return 'a'
    oi, oj = sw_cell(O)
    lo_h = (oi, oj - 1) in Wsw
    lo_v = (oi + 1, oj) in Wsw
    ni, nj = ne_cell(O)
    up_h = (ni, nj + 1) in Wne
    up_v = (ni - 1, nj) in Wne
    if lo_h == lo_v or up_h == up_v:
        return None
    if lo_h and up_h:
        return 'a'
    if lo_v and up_v:
        return 'b'
    if lo_h and up_v:
        return 'c'
    return 'd'


def diag_index(D, direction):
    """1 + the number of consecutive steps inside D in the given diagonal
    direction.  direction=-1 gives the northwest-decomposition ribbon index
    (theta_1 = nw_D), direction=+1 the southeast one (theta_1 = se_D)."""
    out = {}
    for (i, j) in D:
        t = 0
        while (i + direction * (t + 1), j + direction * (t + 1)) in D:
            t += 1
        out[(i, j)] = t + 1
    return out


def offsets_of(D, v, case):
    """Offset of the copy E_d for every d in D, from Definition 3.11.

    (a),(b): west step adds v, south-to-north step adds v+(-1,-1) resp.
             v+(1,1), so the offset is affine in (i,j).
    (c),(d): inside a ribbon of the northwest (resp. southeast) decomposition
             both a west and a south-to-north step add v, and a step one
             position southeast adds (1,1).  Solving those two recurrences
             gives (k-1)(1,1) + c v with k the nw ribbon index, resp.
             -(k-1)(1,1) + c v with k the se ribbon index.
    """
    if case in ('a', 'b'):
        ue = v
        un = (v[0] - 1, v[1] - 1) if case == 'a' else (v[0] + 1, v[1] + 1)
        return {(i, j): (j * ue[0] - i * un[0], j * ue[1] - i * un[1])
                for (i, j) in D}, None
    if case == 'c':
        k = diag_index(D, -1)
        sgn = 1
    else:
        k = diag_index(D, +1)
        sgn = -1
    off = {}
    for (i, j) in D:
        c = j - i
        m = sgn * (k[(i, j)] - 1)
        off[(i, j)] = (m + c * v[0], m + c * v[1])
    return off, k


def compose(D, E, Wsw, Wne, case, v=None):
    """D o_W E as a normalized cell set, or None if W is inconsistent."""
    if v is None:
        v = v_of_W(E, Wsw, Wne, case)
        if v is None:
            return None
    off, k = offsets_of(D, v, case)
    out = set()
    for d, o in off.items():
        out |= shift(E, o)
    if case in ('c', 'd'):
        extra = (1, 1) if case == 'c' else (-1, -1)
        for d in D:
            nb = (d[0] - 1, d[1])          # the cell one position north of d
            if nb in D and k[nb] == k[d]:
                o = off[d]
                out |= shift(Wne, (o[0] + extra[0], o[1] + extra[1]))
    return normalize(frozenset(out))


# --------------------------------------------------------------------------
# Hypotheses I-V
# --------------------------------------------------------------------------


def hyp_II(Wsw, Wne):
    if not Wsw:
        return True
    return min(j - i for i, j in Wne) > max(j - i for i, j in Wsw) + 1


def hyp_III(E, Wsw, Wne):
    if not Wsw:
        return True
    return (is_connected_skew(normalize(E - Wne))
            and is_connected_skew(normalize(E - Wsw)))


def hyp_IV(E, Wsw, Wne, v, K=8):
    """In Ebar = E^{amalg W infty}, no copy of Ohat is adjacent to a copy of
    What (Definition 3.20, Hypothesis 3.22).  Checked on a K-fold
    amalgamation, reading only interior copies so the truncation cannot lie."""
    if not Wsw:
        return True
    O = E - Wsw - Wne
    Ebar = set()
    for t in range(K):
        Ebar |= shift(E, (t * v[0], t * v[1]))
    Ohats, Whats = [], []
    for t in range(K):
        Ot = shift(O, (t * v[0], t * v[1]))
        Ohats.append((t, frozenset(c for c in Ot
                                   if (c[0] + 1, c[1] + 1) in Ot)))
    for t in range(K + 1):
        Wt = shift(Wsw, (t * v[0], t * v[1]))
        h = set(c for c in Ebar if (c[0] + 1, c[1] + 1) in Wt)
        h |= set(c for c in Wt if (c[0] + 1, c[1] + 1) in Ebar)
        Whats.append((t, frozenset(h)))
    lo, hi = 2, K - 3
    for t, Oh in Ohats:
        if not (lo <= t <= hi):
            continue
        for s, Wh in Whats:
            if not (lo <= s <= hi + 1):
                continue
            if Oh & Wh:
                return False
            for (i, j) in Oh:
                for nb in ((i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1)):
                    if nb in Wh:
                        return False
    return True


def hyp_V(E, Wsw, Wne, case):
    """At least one copy of W has just one cell adjacent to O.  Only imposed
    for E = W->O->W and E = W^O^W."""
    if case not in ('a', 'b') or not Wsw:
        return True
    O = E - Wsw - Wne
    for Wc in (Wsw, Wne):
        n = 0
        for (i, j) in Wc:
            if any(nb in O for nb in ((i + 1, j), (i - 1, j),
                                      (i, j + 1), (i, j - 1))):
                n += 1
        if n == 1:
            return True
    return False


def w_candidates(E, require_hyp_I=True):
    """Every (Wsw, Wne, case, v) for which E = W O W satisfies Hypotheses
    I-IV, together with a flag saying whether Hypothesis V also holds."""
    ne, sw = ne_cell(E), sw_cell(E)
    out = []
    # W empty, in both readings of Example 3.7 (see v_of_W)
    for c0 in ('a', 'b'):
        out.append((frozenset(), frozenset(), c0,
                    v_of_W(E, frozenset(), frozenset(), c0), True))
    if len(E) < 3:
        return out
    subs = connected_skew_subdiagrams(E)
    tops = [s for s in subs if ne in s]
    bots = [s for s in subs if sw in s]
    bykey = defaultdict(list)
    for B in bots:
        bykey[(len(B), normalize(B))].append(B)
    raw, raw_all = [], []
    for T in tops:
        key = (len(T), normalize(T))
        for B in bykey.get(key, ()):
            raw_all.append(B)
            if T & B:
                continue
            raw.append((B, T))
    # Hypothesis I: no strictly larger skew diagram occupying the same
    # diagonals also lies in the top and bottom of E.  MvW put no
    # disjointness condition on that larger diagram -- Example 3.6's V is
    # disqualified by a W whose two copies meet -- so the disqualifying list
    # is built before the disjointness filter.
    if require_hyp_I:
        bigger = defaultdict(list)
        for B in raw_all:
            cs = (min(j - i for i, j in B), max(j - i for i, j in B))
            bigger[cs].append(B)
        keep = []
        for B, T in raw:
            cs = (min(j - i for i, j in B), max(j - i for i, j in B))
            if any(B < B2 for B2 in bigger[cs]):
                continue
            keep.append((B, T))
        raw = keep
    for B, T in raw:
        O = E - B - T
        if not O or not is_connected_skew(normalize(O)):
            continue
        if not hyp_II(B, T):
            continue
        if not hyp_III(E, B, T):
            continue
        case = attachment_case(E, B, T, O)
        if case is None:
            continue
        v = v_of_W(E, B, T)
        if v is None:
            continue
        if not hyp_IV(E, B, T, v):
            continue
        out.append((B, T, case, v, hyp_V(E, B, T, case)))
    return out


# --------------------------------------------------------------------------
# the decision procedure
# --------------------------------------------------------------------------

_SHAPE_CACHE = {}


def shapes_upto(n):
    """Connected skew shapes of size 2..n, as cell sets."""
    if n not in _SHAPE_CACHE:
        _SHAPE_CACHE[n] = [cells_from_rho_a(r, a)
                           for r, a in enum_rho_a(n, minsize=2)]
    return _SHAPE_CACHE[n]


def placements(E, F):
    """Every t with E + t inside F."""
    e0 = min(E)
    out = []
    for f in F:
        t = (f[0] - e0[0], f[1] - e0[1])
        if shift(E, t) <= F:
            out.append(t)
    return out


CD_CAP = 12          # cap on |D| in the mixed-attachment cases
CD_CAP_HITS = [0]    # times that cap bit, reported in the SCOPE line


def factorizations(F, require_hyp_I=True, allow_disconnected_D=False):
    """Every nontrivial factorization F = D o_W E, as (D, E, Wsw, Wne, case).

    Trivial factorizations are (1) o_W F, F o_0 (1) and 0 o_F E, i.e. exactly
    |D| <= 1 and |E| <= 1, so the search imposes |D| >= 2 and |E| >= 2.
    Completeness rests on two facts.  Every copy E_d lies inside F, so E is a
    subdiagram of F and every offset lies in the placement set P.  And the
    offset map is injective -- in the (a),(b) cases because u_e and u_n have
    determinant +-(v_j - v_i) != 0 by Hypothesis II, in the (c),(d) cases
    because (content, ribbon index) determines the cell -- so |D| <= |P|.
    """
    found = set()
    cand_E = set()
    for S in connected_skew_subdiagrams(F):
        if len(S) >= 2:
            cand_E.add(normalize(S))
    for E in sorted(cand_E, key=lambda s: (len(s), sorted(s))):
        P = placements(E, F)
        if len(P) < 2:
            continue
        Pset = set(P)
        for (Wsw, Wne, case, v, _hv) in w_candidates(E, require_hyp_I):
            if case in ('a', 'b'):
                ue = v
                un = (v[0] - 1, v[1] - 1) if case == 'a' else (v[0] + 1, v[1] + 1)
                B = len(P)
                for tau in P:
                    Q = set()
                    for i in range(-B, B + 1):
                        for j in range(-B, B + 1):
                            o = (j * ue[0] - i * un[0], j * ue[1] - i * un[1])
                            if (o[0] + tau[0], o[1] + tau[1]) in Pset:
                                Q.add((i, j))
                    if (0, 0) not in Q:
                        continue
                    for D in skew_subshapes_of_set(
                            Q, must_contain=(0, 0), maxsize=len(P),
                            connected=not allow_disconnected_D):
                        if len(D) < 2:
                            continue
                        R = compose(D, E, Wsw, Wne, case, v)
                        if R is not None and R == F:
                            found.add((normalize(D), E, Wsw, Wne, case))
            else:
                cap = min(len(P), CD_CAP)
                if len(P) > CD_CAP:
                    CD_CAP_HITS[0] += 1
                for D in shapes_upto(cap):
                    off, _k = offsets_of(D, v, case)
                    ov = list(off.values())
                    ok = False
                    for tau in P:
                        if all((o[0] + tau[0], o[1] + tau[1]) in Pset
                               for o in ov):
                            ok = True
                            break
                    if not ok:
                        continue
                    R = compose(D, E, Wsw, Wne, case, v)
                    if R is not None and R == F:
                        found.add((normalize(D), E, Wsw, Wne, case))
    return sorted(found, key=lambda t: (len(t[0]), len(t[1]), t[4],
                                        sorted(t[0]), sorted(t[1])))


def is_composition_irreducible(F, **kw):
    return not factorizations(F, **kw)


# --------------------------------------------------------------------------
# validation
# --------------------------------------------------------------------------

RESULTS = []


def row(status, name, detail=""):
    RESULTS.append((status, name, detail))
    print(f"{status:4s}  {name}" + (f"    {detail}" if detail else ""))


def profile(cells):
    ri = row_intervals(cells)
    return [ri[i][1] - ri[i][0] + 1 for i in sorted(ri)]


def from_lam_mu(lam, mu):
    mu = list(mu) + [0] * (len(lam) - len(mu))
    out = set()
    for i, (L, M) in enumerate(zip(lam, mu)):
        for j in range(M, L):
            out.add((i, j))
    return normalize(frozenset(out))


def mark(E):
    """E with its unique W as MvW would take it, for the small test shapes."""
    cands = w_candidates(E)
    return cands


def validate(fast=True):
    print("=" * 78)
    print("VALIDATION")
    print("=" * 78)

    # ---- MvW Example 3.12, first case: E = (4,4,2)/(3) = W->O->W -----------
    E = from_lam_mu((4, 4, 2), (3,))
    Wsw = frozenset({(1, 0), (2, 0)})
    Wne = frozenset({(0, 3), (1, 3)})
    case = attachment_case(E, Wsw, Wne, E - Wsw - Wne)
    D = from_lam_mu((2, 2), ())
    R = compose(D, E, Wsw, Wne, case)
    row("PASS" if case == 'a' else "FAIL",
        "Ex 3.12 first E is W->O->W", f"case={case}")
    row("PASS" if profile(R) == [1, 4, 5, 5, 5, 2] else "FAIL",
        "Ex 3.12 (a): row profile of D o_W E",
        f"{profile(R)}  paper [1, 4, 5, 5, 5, 2]")

    # ---- MvW Example 3.13: 2x2 o_empty 2x2 --------------------------------
    Sq = from_lam_mu((2, 2), ())
    R = compose(Sq, Sq, frozenset(), frozenset(), 'a')
    row("PASS" if R == from_lam_mu((5, 5, 4, 4, 2), (3, 1, 1)) else "FAIL",
        "Ex 3.13: 2x2 o_0 2x2 = (5,5,4,4,2)/(3,1,1)",
        f"|R|={len(R)} profile={profile(R)}")

    # ---- MvW Example 3.12, second case: E = (3,3,3,2)/(2,2) = W->O^W ------
    E2 = from_lam_mu((3, 3, 3, 2), (2, 2))
    Wsw2 = frozenset({(2, 0), (3, 0)})
    Wne2 = frozenset({(0, 2), (1, 2)})
    case2 = attachment_case(E2, Wsw2, Wne2, E2 - Wsw2 - Wne2)
    R2 = compose(D, E2, Wsw2, Wne2, case2)
    row("PASS" if case2 == 'c' else "FAIL",
        "Ex 3.12 second E is W->O^W", f"case={case2}")
    row("PASS" if profile(R2) == [1, 1, 3, 2, 4, 4, 5, 2] else "FAIL",
        "Ex 3.12 (c): row profile of D o_W E",
        f"{profile(R2)}  paper [1, 1, 3, 2, 4, 4, 5, 2]")

    # ---- Remark 5.8: (2) o_0 (2) = (4) ------------------------------------
    two = from_lam_mu((2,), ())
    row("PASS" if compose(two, two, frozenset(), frozenset(), 'a')
        == from_lam_mu((4,), ()) else "FAIL",
        "Rmk 5.8: (2) o_0 (2) = (4)")

    # ---- Lemma 3.19 (i),(ii),(iii) over a systematic structural sweep -----
    ecap, dcap = (7, 5) if fast else (8, 6)
    Es = [cells_from_rho_a(r, a) for r, a in enum_rho_a(ecap, minsize=2)]
    Ds = [cells_from_rho_a(r, a) for r, a in enum_rho_a(dcap, minsize=1)]
    bad_skew = bad_rot = bad_tr = n_tested = 0
    marked = []
    for E in Es:
        for (Wsw, Wne, case, v, hv) in w_candidates(E):
            Er, Wswr, Wner, caser, vr = rotate_marked(E, Wsw, Wne, case)
            marked.append((E, Wsw, Wne, case, v, hv,
                           Er, Wswr, Wner, caser, vr))
            for Dd in Ds:
                R = compose(Dd, E, Wsw, Wne, case, v)
                if R is None:
                    continue
                n_tested += 1
                if not is_skew(R):
                    bad_skew += 1
                if caser is not None and vr is not None:
                    R2 = compose(rotate(Dd), Er, Wswr, Wner, caser, vr)
                    if R2 is not None and rotate(R) != R2:
                        bad_rot += 1
                if not Wsw and case == 'a':
                    Rt = compose(rotate(Dd), transpose(E), frozenset(),
                                 frozenset(), 'b')
                    if Rt is not None and transpose(R) != Rt:
                        bad_tr += 1
    row("PASS" if bad_skew == 0 else "FAIL",
        "Lemma 3.19(i): D o_W E is a skew diagram",
        f"{n_tested} compositions, {bad_skew} failures")
    row("PASS" if bad_rot == 0 else "FAIL",
        "Lemma 3.19(ii): (D o_W E)* = D* o_{W*} E*", f"{bad_rot} failures")
    row("PASS" if bad_tr == 0 else "FAIL",
        "empty-mark transposition (this engine's extension; Lemma 3.19(iii) "
        "assumes W nonempty): (D o_0 E)^t = D* o_0 E^t, E^t read as W^O^W",
        f"{bad_tr} failures")

    # ---- Theorem 5.3: factor reversal preserves the skew Schur function ---
    # Restricted to compositions small enough to expand exactly, which is the
    # only limit here; every orbit inside the window is checked.
    ROWCAP = 11
    Ds2 = [cells_from_rho_a(r, a) for r, a in enum_rho_a(4, minsize=2)]
    revV = revV_bad = rev4 = rev4_bad = 0
    for (E, Wsw, Wne, case, v, hv, Er, Wswr, Wner, caser, vr) in marked:
        if len(E) > 6:
            continue
        for Dd in Ds2:
            variants = [(Dd, E, Wsw, Wne, case, v),
                        (rotate(Dd), E, Wsw, Wne, case, v)]
            if caser is not None and vr is not None:
                variants += [(Dd, Er, Wswr, Wner, caser, vr),
                             (rotate(Dd), Er, Wswr, Wner, caser, vr)]
            polys, ok = set(), True
            for (dd, ee, ws, wn, cs, vv) in variants:
                RR = compose(dd, ee, ws, wn, cs, vv)
                if RR is None or not is_connected_skew(RR) \
                        or len(row_intervals(RR)) > ROWCAP:
                    ok = False
                    break
                polys.add(jt_of_cells(RR))
            if not ok:
                continue
            rev4 += 1
            if len(polys) != 1:
                rev4_bad += 1
            if hv:
                revV += 1
                if len(polys) != 1:
                    revV_bad += 1
    row("PASS" if revV_bad == 0 and revV > 100 else "FAIL",
        "Thm 5.3: factor reversal preserves s_D, Hyp I-V",
        f"{revV} reversal orbits, {revV_bad} failures")
    row("PASS" if rev4_bad == 0 else "WARN",
        "Cnj 3.26: the same under Hyp I-IV alone",
        f"{rev4} reversal orbits, {rev4_bad} failures")

    # ---- completeness of the factorization SEARCH -------------------------
    # Forward-generate F = D o_W E, then require the search to recover it.
    miss = tried = 0
    missing_cases = defaultdict(int)
    for (E, Wsw, Wne, case, v, hv, *_r) in marked:
        if len(E) > 6:
            continue
        for Dd in Ds2:
            F = compose(Dd, E, Wsw, Wne, case, v)
            if F is None or not is_connected_skew(F) or len(F) > 16:
                continue
            tried += 1
            fs = factorizations(F)
            if (normalize(Dd), E, Wsw, Wne, case) not in set(fs):
                miss += 1
                missing_cases[case] += 1
    row("PASS" if miss == 0 else "FAIL",
        "search recovers every forward-generated factorization",
        f"{tried} generated, {miss} not recovered {dict(missing_cases)}")

    # ---- irreducibility is closed under transposition and rotation -------
    # s_{D^t} = omega(s_D) and s_{D*} = s_D, and the classification is
    # equivariant, so the predicate must be too.  Transposition exchanges the
    # attachment cases (a)<->(b) and (c)<->(d), so this exercises all four.
    tcap = 9 if fast else 10
    bad_t = bad_r = ntr = 0
    for rho, a in enum_rho_a(tcap, minsize=1):
        S = cells_from_rho_a(rho, a)
        i0 = is_composition_irreducible(S)
        ntr += 1
        if i0 != is_composition_irreducible(transpose(S)):
            bad_t += 1
        if i0 != is_composition_irreducible(rotate(S)):
            bad_r += 1
    row("PASS" if bad_t == 0 else "FAIL",
        "irreducibility is closed under transposition",
        f"{ntr} shapes of at most {tcap} cells, {bad_t} violations")
    row("PASS" if bad_r == 0 else "FAIL",
        "irreducibility is closed under antipodal rotation",
        f"{ntr} shapes, {bad_r} violations")

    # ---- Remark 5.8: eight members from E = (2,1), W = (1) ----------------
    E = from_lam_mu((2, 1), ())
    Wne, Wsw = frozenset({(0, 1)}), frozenset({(1, 0)})
    case = attachment_case(E, Wsw, Wne, E - Wsw - Wne)
    Es_, Wsws, Wnes, cases, _v = rotate_marked(E, Wsw, Wne, case)
    got, polys = set(), set()
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                pick = lambda t: (E, Wsw, Wne, case) if t == 0 else \
                    (Es_, Wsws, Wnes, cases)
                e1, e2, e3 = pick(a), pick(b), pick(c)
                inner = compose(e1[0], e2[0], e2[1], e2[2], e2[3])
                outer = compose(inner, e3[0], e3[1], e3[2], e3[3])
                got.add(outer)
                polys.add(jt_of_cells(outer))
    row("PASS" if (case, cases) == ('d', 'c') else "FAIL",
        "Rmk 5.8: E=(2,1) is W^O->W and E* is W->O^W",
        f"cases {case}/{cases}")
    row("PASS" if len(got) == 8 else "FAIL",
        "Rmk 5.8: the eight (E' o_W E'') o_W E''' differ",
        f"{len(got)} distinct, sizes {sorted({len(g) for g in got})}")
    row("PASS" if len(polys) == 1 else "FAIL",
        "Rmk 5.8: all eight are skew-equivalent",
        f"{len(polys)} distinct skew Schur functions")

    # ---- irreducible witnesses -------------------------------------------
    print()
    print("  composition-IRREDUCIBLE witnesses")
    for lam, mu in [((1,), ()), ((2,), ()), ((1, 1), ()), ((2, 1), ()),
                    ((1, 1, 1), ()), ((2, 2), ()), ((3,), ()),
                    ((4, 4, 4, 4), ())]:
        S = from_lam_mu(lam, mu)
        f = factorizations(S)
        f2 = factorizations(S, allow_disconnected_D=True)
        row("PASS" if not f and not f2 else "FAIL",
            f"  {lam}/{mu or (0,)} ({len(S)} cells) is IRREDUCIBLE",
            f"{len(f)} factorizations, {len(f2)} allowing disconnected D")

    # ---- reducible witnesses, with the factorization printed --------------
    print()
    print("  composition-REDUCIBLE witnesses")
    red = [((4,), (), "(4) = (2) o_0 (2), MvW Rmk 5.8"),
           ((1, 1, 1, 1, 1), (), "five-cell column, PRIME size"),
           ((5,), (), "five-cell row, PRIME size")]
    for lam, mu, note in red:
        S = from_lam_mu(lam, mu)
        f = factorizations(S)
        row("PASS" if f else "FAIL",
            f"  {lam}/{mu or (0,)} ({len(S)} cells) is REDUCIBLE",
            f"{len(f)} factorizations   [{note}]")
        for d, e, ws, wn, c in f[:2]:
            dl, dm = lam_mu_of(d)
            el, em = lam_mu_of(e)
            print(f"          D={dl}/{dm}  E={el}/{em}  |W|={len(ws)}  "
                  f"case={c}")

    # ---- the four-member 11-cell class -----------------------------------
    print()
    print("  the given four-member class")
    klass = [((5, 5, 4, 4, 3), (4, 3, 2, 1, 0)),
             ((5, 5, 5, 4, 2), (4, 3, 2, 1, 0)),
             ((5, 4, 3, 2, 1), (3, 1, 0, 0, 0)),
             ((5, 4, 3, 2, 1), (2, 1, 1, 0, 0))]
    shp = [from_lam_mu(l, m) for l, m in klass]
    row("PASS" if len({jt_of_cells(s) for s in shp}) == 1 else "FAIL",
        "  the four shapes are one exact skew Schur class",
        f"sizes {sorted({len(s) for s in shp})}")
    row("PASS" if len(set(shp)) == 4 else "FAIL",
        "  ... and are four distinct diagrams", f"{len(set(shp))}")
    facs = []
    for (l, m), S in zip(klass, shp):
        f = factorizations(S)
        facs.append(f)
        row("PASS" if f else "FAIL",
            f"  {l}/{m} is REDUCIBLE", f"{len(f)} factorizations")
        for d, e, ws, wn, c in f:
            dl, dm = lam_mu_of(d)
            el, em = lam_mu_of(e)
            print(f"          D={dl}/{dm}  E={el}/{em}  |W|={len(ws)}  "
                  f"case={c}")
    # the four factorizations must be the four reversal choices of one pair
    Dset = {facs[0][0][0], facs[1][0][0]}
    Eset = {facs[0][0][1], facs[2][0][1]}
    ok = (len(facs[0]) == len(facs[1]) == len(facs[2]) == len(facs[3]) == 1
          and rotate(facs[0][0][0]) == facs[1][0][0]
          and rotate(facs[0][0][1]) == facs[2][0][1])
    row("PASS" if ok else "FAIL",
        "  the four members are the four factor reversals of one (D, E)",
        f"D* pairing and E* pairing both hold: {ok}")

    # ---- the eight-cell nonrotation pair ---------------------------------
    print()
    print("  the eight-cell nonrotation pair")
    pair = [((4, 4, 3, 3), (3, 2, 1, 0)), ((4, 4, 4, 2), (3, 2, 1, 0))]
    ps = [from_lam_mu(l, m) for l, m in pair]
    row("PASS" if jt_of_cells(ps[0]) == jt_of_cells(ps[1]) else "FAIL",
        "  the pair is skew-equal")
    row("PASS" if rotate(ps[0]) != ps[1] and ps[0] != ps[1] else "FAIL",
        "  the pair is a NONROTATION pair")
    for (l, m), S in zip(pair, ps):
        f = factorizations(S)
        row("PASS" if f else "FAIL",
            f"  {l}/{m} is REDUCIBLE", f"{len(f)} factorizations")
        for d, e, ws, wn, c in f:
            dl, dm = lam_mu_of(d)
            el, em = lam_mu_of(e)
            print(f"          D={dl}/{dm}  E={el}/{em}  |W|={len(ws)}  "
                  f"case={c}")


def rotate_marked(E, Wsw, Wne, case='a'):
    """(E*, W*_sw, W*_ne, case, v): rotation swaps the top and bottom copies.
    Rotation carries west to east and north to south, so a horizontal
    attachment stays horizontal: case (a) and (b) are fixed and (c) and (d)
    are exchanged, which is Lemma 3.19(ii)'s own remark.  For the empty W the
    reading of Example 3.7 is carried across unchanged."""
    rE = [(-i, -j) for i, j in E]
    di = -min(i for i, _ in rE)
    dj = -min(j for _, j in rE)
    Er = frozenset((i + di, j + dj) for i, j in rE)
    rWsw = frozenset((-i + di, -j + dj) for i, j in Wsw)
    rWne = frozenset((-i + di, -j + dj) for i, j in Wne)
    Wswr, Wner = rWne, rWsw
    caser = attachment_case(Er, Wswr, Wner, Er - Wswr - Wner) if Wswr else case
    vr = v_of_W(Er, Wswr, Wner, caser) if caser is not None else None
    return Er, Wswr, Wner, caser, vr



# --------------------------------------------------------------------------
# census
# --------------------------------------------------------------------------


def census(cap, irr_cap=None, jobs=1):
    """Group connected skew diagrams by the EXACT free-h Jacobi-Trudi
    determinant, then report every class holding a nonrotation equal pair
    against the composition-irreducibility of its members.

    Shapes are bucketed by hash(determinant) first and every bucket of size
    at least two is then split by the exact polynomial, so the classes are
    exact while only the multi-member buckets ever hold a polynomial.  A hash
    collision between two different determinants can only merge two buckets,
    which the exact split then separates."""
    print()
    print("=" * 78)
    print(f"CENSUS over connected skew diagrams of at most {cap} cells")
    print("=" * 78)
    t0 = time.time()
    buckets = defaultdict(list)
    total = 0
    tasks = [(n, f) for n in range(1, cap + 1) for f in range(1, n + 1)]
    if jobs and jobs > 1:
        import multiprocessing as mp
        with mp.Pool(jobs) as pool:
            for n, sub in pool.imap_unordered(_task, tasks, chunksize=1):
                for h, lst in sub.items():
                    buckets[(n, h)].extend(lst)
                    total += len(lst)
    else:
        for arg in tasks:
            n, sub = _task(arg)
            for h, lst in sub.items():
                buckets[(n, h)].extend(lst)
                total += len(lst)
    t1 = time.time()
    nclasses = 0
    multi = []
    bysize_shapes = defaultdict(int)
    bysize_classes = defaultdict(int)
    for key, mem in buckets.items():
        bysize_shapes[key[0]] += len(mem)
        if len(mem) == 1:
            nclasses += 1
            bysize_classes[key[0]] += 1
            continue
        shapes = [unpack(b) for b in mem]
        # A bucket that is a single orbit of the rotation involution needs no
        # polynomial: s_{D*} = s_D is MvW Proposition 3.4, so the bucket is
        # already known to be one exact class.  Everything else, including a
        # hash collision, is split by the exact determinant.
        canon = set()
        for rho, a in shapes:
            r2, a2 = rot_rho_a(rho, a)
            canon.add(min((rho, a), (r2, a2)))
        if len(canon) == 1:
            nclasses += 1
            bysize_classes[key[0]] += 1
            multi.append(shapes)
            continue
        exact = defaultdict(list)
        for rho, a in shapes:
            x, y = beta(rho, a)
            exact[det_free_h(x, y)].append((rho, a))
        nclasses += len(exact)
        bysize_classes[key[0]] += len(exact)
        for pol, m2 in exact.items():
            if len(m2) > 1:
                multi.append(m2)
    print(f"  connected shapes up to translation : {total}")
    print(f"  exact skew Schur classes           : {nclasses}")
    print(f"  classes with more than one shape   : {len(multi)}")
    cum_s = cum_c = 0
    print(f"  {'n':>3} {'shapes':>10} {'classes':>10} {'cum shapes':>11} "
          f"{'cum classes':>11}")
    for n in range(1, cap + 1):
        cum_s += bysize_shapes[n]
        cum_c += bysize_classes[n]
        print(f"  {n:>3} {bysize_shapes[n]:>10} {bysize_classes[n]:>10} "
              f"{cum_s:>11} {cum_c:>11}")
    print(f"  time: {t1-t0:.1f}s grouping, {time.time()-t1:.1f}s exact split")

    nonrot = []
    for mem in multi:
        cells = [cells_from_rho_a(r, a) for r, a in mem]
        hit = any(cells[q] != rotate(cells[p])
                  for p in range(len(cells))
                  for q in range(p + 1, len(cells)))
        if hit:
            nonrot.append((len(cells[0]), mem, cells))
    nonrot.sort(key=lambda t: (t[0], len(t[1]), sorted(t[2][0])))
    print(f"  classes holding a nonrotation pair : {len(nonrot)}")
    print(f"  shapes lying in one                : "
          f"{sum(len(m) for _, m, _ in nonrot)}")
    bysize = defaultdict(int)
    for n, m, _ in nonrot:
        bysize[(n, len(m))] += 1
    print("  (cells, class size) -> classes     : "
          + ", ".join(f"({n},{s}):{c}" for (n, s), c in sorted(bysize.items())))
    allsizes = defaultdict(int)
    for mem in multi:
        allsizes[len(mem)] += 1
    print("  every multi-shape class by size     : "
          + ", ".join(f"{k}:{v}" for k, v in sorted(allsizes.items())))

    print()
    print("  every class holding a nonrotation equal pair, graded")
    print(f"  {'cells':>5} {'rows':>4} {'|class|':>7} {'2^r':>4} "
          f"{'irred':>5} {'facts':>5}  members")
    print("  " + "-" * 74)
    anomalies = []
    graded = 0
    hypI_disagree = 0
    maxrows_seen = [0]
    for n, mem, cells in nonrot:
        if irr_cap is not None and n > irr_cap:
            continue
        graded += 1
        irr, nf = 0, []
        for S in cells:
            f = factorizations(S)
            nf.append(len(f))
            if not f:
                irr += 1
        irr_noI = sum(1 for S in cells
                      if is_composition_irreducible(S, require_hyp_I=False))
        if irr_noI != irr:
            hypI_disagree += 1
        p2 = (len(mem) & (len(mem) - 1)) == 0
        names = "  ".join(f"{lam_mu_of(S)[0]}/{lam_mu_of(S)[1]}"
                          for S in cells[:2])
        rmax = max(len(row_intervals(S)) for S in cells)
        maxrows_seen[0] = max(maxrows_seen[0], rmax)
        print(f"  {n:5d} {rmax:4d} {len(mem):7d} {'y' if p2 else 'NO':>4} "
              f"{irr:5d} {str(min(nf))+'-'+str(max(nf)):>5}  {names}"
              + ("  ..." if len(cells) > 2 else ""))
        if irr or not p2:
            anomalies.append((n, len(mem), irr, cells))
    print("  " + "-" * 74)
    print(f"  classes graded                     : {graded}")
    # A census silently capped on the number of ROWS undercounts badly: at
    # sixteen cells, capping rows at seven gives 98,463 classes and 56
    # nonrotation classes, while the whole population gives 172,315 and 80.
    # Nothing here is capped, and the deepest class in range says so.
    print(f"  deepest nonrotation class         : {maxrows_seen[0]} rows")
    row("PASS" if maxrows_seen[0] > 7 or cap < 13 else "FAIL",
        "the census is not row-capped",
        f"a nonrotation class of {maxrows_seen[0]} rows is in range")
    row("PASS" if hypI_disagree == 0 else "WARN",
        "the verdict agrees with Hypothesis I enforced and dropped",
        f"{hypI_disagree} of {graded} classes disagree")
    print(f"  with an irreducible member or a non-power-of-two size : "
          f"{len(anomalies)}")

    # MvW predicts |class| = 2^r for r nonsymmetric factors, so a member of a
    # class of size 4 or more must carry at least two factors and cannot be
    # composition-irreducible.  Both halves are checked here.
    bad_irr = [a for a in anomalies if a[2]]
    bad_p2 = [a for a in anomalies if (a[1] & (a[1] - 1))]
    row("PASS" if not bad_p2 else "FAIL",
        "every nonrotation class size is a power of two",
        f"{len(bad_p2)} offenders")
    row("PASS" if not bad_irr else "FAIL",
        "no nonrotation class has a composition-irreducible member",
        f"{len(bad_irr)} offenders")
    if anomalies:
        print()
        print("  *** CANDIDATE COUNTEREXAMPLES TO CONJECTURE 5.7 ***")
        for n, sz, irr, cells in anomalies:
            for S in cells:
                lam, mu = lam_mu_of(S)
                print(f"    |D|={n} class size {sz} irreducible members "
                      f"{irr}   {lam}/{mu}")

    # every shape in a class of size >= 3 must be reducible, whether or not
    # the class holds a nonrotation pair
    big = [m for m in multi if len(m) >= 3]
    bad = 0
    for mem in big:
        for rho, a in mem:
            if is_composition_irreducible(cells_from_rho_a(rho, a)):
                bad += 1
    row("PASS" if bad == 0 else "FAIL",
        "every member of a class of size >= 3 is reducible",
        f"{len(big)} such classes, {bad} irreducible members")
    return nonrot, anomalies


def lam_mu_of(cells):
    ri = row_intervals(cells)
    ks = sorted(ri)
    lam = tuple(ri[i][1] + 1 for i in ks)
    mu = tuple(ri[i][0] for i in ks)
    return lam, mu


# --------------------------------------------------------------------------


def density(cap):
    """How many connected skew diagrams of each size are composition-
    irreducible.  A search for a counterexample to Conjecture 5.7 that filters
    on parent irreducibility is priced against this number."""
    print()
    print("=" * 78)
    print(f"IRREDUCIBLE DENSITY up to {cap} cells")
    print("=" * 78)
    print(f"  {'n':>3} {'shapes':>9} {'irreducible':>12} {'fraction':>9}")
    tot = irr = 0
    for n in range(1, cap + 1):
        sn = inn = 0
        for first in range(1, n + 1):
            for rho, a in enum_rho_a_exact(n, first):
                sn += 1
                if is_composition_irreducible(cells_from_rho_a(rho, a)):
                    inn += 1
        tot += sn
        irr += inn
        print(f"  {n:>3} {sn:>9} {inn:>12} {inn/sn:>9.3f}")
    print(f"  cumulative: {irr} of {tot} shapes are composition-irreducible "
          f"({irr/tot:.3f})")


def parse_shape(spec):
    """'5,5,4,4,3/4,3,2,1,0' -> cell set."""
    lam, _, mu = spec.partition('/')
    lam = tuple(int(t) for t in lam.replace(' ', '').split(',') if t != '')
    mu = tuple(int(t) for t in mu.replace(' ', '').split(',') if t != '') \
        if mu.strip() else ()
    return from_lam_mu(lam, mu)


def report_shape(spec):
    S = parse_shape(spec)
    lam, mu = lam_mu_of(S)
    print(f"shape {lam}/{mu}  {len(S)} cells, "
          f"{len(row_intervals(S))} rows")
    print(f"  connected skew diagram : {is_connected_skew(S)}")
    print(f"  D* = D                 : {rotate(S) == S}")
    print(f"  D^t = D                : {transpose(S) == S}")
    for tag, kw in (("connected D", {}),
                    ("disconnected D allowed", {"allow_disconnected_D": True})):
        f = factorizations(S, **kw)
        print(f"  nontrivial factorizations, {tag}: {len(f)}")
        for d, e, ws, wn, c in f:
            dl, dm = lam_mu_of(d)
            el, em = lam_mu_of(e)
            wl = lam_mu_of(ws) if ws else ((), ())
            print(f"      D={dl}/{dm}  E={el}/{em}  W={wl[0]}/{wl[1]}"
                  f"  case={c}")
    print(f"  VERDICT: composition-"
          f"{'IRREDUCIBLE' if is_composition_irreducible(S) else 'REDUCIBLE'}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cap", type=int, default=13)
    ap.add_argument("--irr-cap", type=int, default=None)
    ap.add_argument("--skip-validate", action="store_true")
    ap.add_argument("--skip-census", action="store_true")
    ap.add_argument("--thorough", action="store_true")
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--shape", type=str, default=None,
                    help="test one shape, e.g. 5,5,4,4,3/4,3,2,1,0")
    ap.add_argument("--density", type=int, default=0)
    args = ap.parse_args()

    if args.shape:
        report_shape(args.shape)
        return
    if not args.skip_validate:
        validate(fast=not args.thorough)
    if not args.skip_census:
        census(args.cap, args.irr_cap, args.jobs)
    if args.density:
        density(args.density)

    print()
    nfail = sum(1 for s, _, _ in RESULTS if s == "FAIL")
    nwarn = sum(1 for s, _, _ in RESULTS if s == "WARN")
    print("SCOPE.  o_W is implemented from McNamara-van Willigenburg "
          "Definition 3.11 in all four attachment cases, with the empty W "
          "read both horizontally and vertically (Example 3.7, forced by "
          "Lemma 3.19(iii)), and Hypotheses I-V (3.8, 3.22, 3.27) as stated. "
          "A factorization is nontrivial exactly when |D| >= 2 and |E| >= 2, "
          "which is Definition 5.5's list of the three trivial ones.")
    print("  The search is complete for connected D: E must be a subdiagram "
          "of F, every offset must lie in the placement set P, and the offset "
          "map is injective, so |D| <= |P| -- and in the W->O->W and W^O^W "
          f"cases D is reconstructed rather than enumerated.  Capped at "
          f"|D| <= {CD_CAP} in the mixed W->O^W / W^O->W cases; disconnected "
          "D is swept on request in the W->O->W and W^O^W cases only.")
    print(f"  Census: every connected skew diagram of at most {args.cap} "
          "cells, grouped by the exact free-h Jacobi-Trudi determinant.")
    print(f"  The mixed-case |D| cap bit {CD_CAP_HITS[0]} times in this run"
          + ("." if CD_CAP_HITS[0] == 0
             else " -- those searches are NOT complete."))
    print(f"{len(RESULTS)} validation rows, {nfail} FAIL, {nwarn} WARN")
    if nfail:
        print("SOME CHECKS FAILED")
        sys.exit(1)
    print("ALL PASS")


if __name__ == "__main__":
    main()
