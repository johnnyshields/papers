"""Paper section `sec:roots` (The geometry of a chart and two complete searches); targets `lem:copies`, `lem:bands`, `cor:outer`, `eq:private`, `lem:size`, `thm:searches`, `tab:roots`.

Terminal rigidity on the census: every member of every nonrotation class has a proper chart.

A CHART of a connected diagram F is F = D o_W E with D, E connected, |D|, |E| >= 2 and the marked
inner (E, W) satisfying Hypotheses I-IV.  Two searches, both complete at every size (paper, section on
root finding), are run on every member and must return the same chart set:
  search S  every connected subdiagram of F as the inner; outer heights from the private diagonals;
  search B  the inner read directly off the first and last q diagonals of F, for every period q and
            width w with N_F = N_D q + w.
Every chart is recomposed cell for cell, its mark is re-derived from Hypotheses I-IV, and the
private-diagonal identity and the size bound |F| >= q|D| + N_E - q are asserted on it.

Validation where nothing is assumed about the census: every connected profile of 2..VMAX cells
(search S == search B), and forward compositions D o_W E over a box of small factors (both searches
recover the generating chart).  Controls: the hook (2,1;0) is rootless; a deliberately misaligned
search B misses charts; random profiles of census size are mostly rootless; a chart with a 13-cell
outer is found (no cap on the outer).

Usage: python3 verify_roots.py [--work DIR] [--jobs J] [--vmax 10] [--box small|full]
"""
import argparse
import json
import os
import random
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import skew_core as C      # noqa: E402
import skew_compose as K   # noqa: E402

# Published per-area table: N -> (members, rooted members, charts, members with 1/2/3/4+ charts).
EXPECTED = {
    8: (1, 4, 4, 4, 4, 0, 0, 0, 3, 0, 0, 2, 2),
    9: (1, 4, 4, 4, 4, 0, 0, 0, 3, 4, 0, 0, 0),
    10: (1, 4, 4, 4, 4, 0, 0, 0, 4, 0, 0, 2, 2),
    11: (3, 12, 12, 12, 12, 0, 0, 0, 4, 0, 0, 6, 6),
    12: (7, 28, 28, 28, 28, 0, 0, 0, 5, 16, 0, 6, 6),
    13: (5, 20, 20, 24, 16, 4, 0, 0, 5, 0, 0, 12, 12),
    14: (12, 48, 48, 52, 44, 4, 0, 0, 6, 4, 4, 22, 22),
    15: (29, 116, 116, 128, 104, 12, 0, 0, 6, 68, 4, 28, 28),
    16: (21, 84, 84, 96, 72, 12, 0, 0, 8, 24, 0, 36, 36),
    17: (34, 136, 136, 144, 128, 8, 0, 0, 7, 8, 8, 64, 64),
    18: (81, 324, 324, 372, 276, 48, 0, 0, 9, 168, 16, 94, 94),
    19: (64, 256, 256, 276, 236, 20, 0, 0, 8, 16, 16, 122, 122),
    20: (132, 532, 532, 580, 484, 48, 0, 0, 10, 184, 48, 174, 174),
    21: (212, 848, 848, 900, 796, 52, 0, 0, 9, 408, 24, 234, 234),
    22: (190, 760, 760, 840, 680, 80, 0, 0, 11, 76, 52, 356, 356),
    23: (311, 1248, 1248, 1352, 1152, 88, 8, 0, 10, 140, 140, 536, 536),
    24: (639, 2560, 2560, 2820, 2300, 260, 0, 0, 12, 1344, 104, 686, 686),
    25: (519, 2080, 2080, 2196, 1968, 108, 4, 0, 11, 360, 120, 858, 858),
    26: (808, 3236, 3236, 3448, 3036, 188, 12, 0, 13, 368, 328, 1376, 1376),
}


def say(*a):
    print(*a, flush=True)


def load_classes(work):
    raw = json.load(open(os.path.join(work, 'classes.json')))
    return {int(N): [[(tuple(F[0]), tuple(F[1])) for F in cl] for cl in cls] for N, cls in raw.items()}


def chart_ok(F, k, q):
    D, E, B, T, case = k
    mk = [m for m in K.marks(E) if m[0] == B and m[1] == T and m[2] == case]
    if len(mk) != 1 or mk[0][4] != q:
        return 'mark not legal'
    if K.compose(D, E, B, T, case, mk[0][3]) != F:
        return 'does not recompose'
    if not K.is_connected_skew(D) or len(D) < 2 or len(E) < 2:
        return 'improper'
    if not K.private_heights_hold(F, D, E, q):
        return 'private heights fail'
    if not K.size_bound_holds(F, D, E, q):
        return 'size bound fails'
    return None


def w_both(prof):
    F = C.cells(prof)
    t0 = time.time()
    b = K.finder_band(F)
    t1 = time.time()
    s = K.finder_subdiagram(F)
    t2 = time.time()
    bad = []
    if b != s:
        bad.append('search B != search S')
    for k, q in s.items():
        r = chart_ok(F, k, q)
        if r:
            bad.append(r)
    return prof, s, bad, (t1 - t0, t2 - t1)


def w_forward(item):
    F, gens = item
    b = K.finder_band(F)
    s = K.finder_subdiagram(F) if len(F) <= 24 else None
    bad = []
    for k, q in gens:
        if b.get(k) != q:
            bad.append('generating chart missed by search B')
        if s is not None and s.get(k) != q:
            bad.append('generating chart missed by search S')
    if s is not None and s != b:
        bad.append('search B != search S')
    for k, q in b.items():
        r = chart_ok(F, k, q)
        if r:
            bad.append(r)
    return len(F), len(b), bad


def finder_band_misaligned(F):
    """Control: search B with the upper band aligned one row too low."""
    out = {}
    F = K.normalize(F)
    HF = K.height_seq(F)
    NF = len(HF)
    c0 = min(j - i for i, j in F)
    for q in range(2, NF):
        for w in range(q):
            if (NF - w) % q or (NF - w) // q < 2:
                continue
            ND = (NF - w) // q
            sh = (ND - 1) * q
            rows_w = [i for i, j in F if j - i - c0 == w]
            rows_b = [i for i, j in F if j - i - c0 == w + sh]
            a = min(rows_b) - min(rows_w) + 1
            E0 = frozenset({(i, j) for (i, j) in F if j - i - c0 < q}
                           | {(i - a, j - a - sh) for (i, j) in F if j - i - c0 >= NF - q})
            if len(E0) < 2 or not K.is_connected_skew(E0):
                continue
            E = K.normalize(E0)
            hs = K.outer_heights(HF, K.height_seq(E), q, w, ND) if len(K.height_seq(E)) == q + w else None
            if hs is None:
                continue
            for (B, T, case, v, qq) in K.marks(E):
                if qq == q:
                    for D in K.shapes_with_heights(hs):
                        if len(D) >= 2 and K.compose(D, E, B, T, case, v) == F:
                            out[(D, E, B, T, case)] = q
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', default=os.environ.get('SKEWBASE_WORK', os.path.join(HERE, '_work')))
    ap.add_argument('--jobs', type=int, default=int(os.environ.get('SKEWBASE_JOBS', '4')))
    ap.add_argument('--vmax', type=int, default=10)
    ap.add_argument('--box', default='small')
    args = ap.parse_args()
    T0 = time.time()
    import multiprocessing as mp
    pool = mp.get_context('fork').Pool(args.jobs)

    # ------------------------------------------------------------ controls
    hook = C.cells(((2, 1), (0,)))
    assert not K.finder_band(hook) and not K.finder_subdiagram(hook)
    say('PASS (control: rootless hook): the hook (2,1;0) has no chart under either search')
    E = C.cells(((2, 1), (0,)))
    D13 = C.cells(((2, 2, 2, 2, 2, 2, 1), (0, 0, 0, 0, 0, 0)))
    nbig = 0
    for (B, T, case, v, q) in K.marks(E):
        F = K.compose(D13, E, B, T, case, v)
        assert K.is_connected_skew(F)
        k = (D13, E, B, T, case)
        assert K.finder_band(F).get(k) == q
        nbig += 1
    say('PASS (control: large outer): every chart (2,2,2,2,2,2,1;0,...,0) o_W (2,1;0) with a 13-cell outer is '
        'found by search B (%d marks; parents of %s cells)' % (nbig, sorted({len(K.compose(D13, E, *m[:4])) for m in K.marks(E)})))

    # ------------------------------------------------------------ V1: every profile of 2..vmax cells
    t = time.time()
    small = [F for N in range(2, args.vmax + 1) for F in C.all_profiles(N)]
    nch = nroot = 0
    bad1 = []
    for prof, s, bad, _ in pool.imap_unordered(w_both, small, chunksize=16):
        nch += len(s)
        nroot += 1 if s else 0
        if bad:
            bad1.append((prof, bad))
    assert not bad1, bad1[:5]
    say('PASS (V1): all %d connected profiles of 2..%d cells: search B = search S, every chart legal, recomposed, '
        'with the private-diagonal identity and the size bound; %d charts, %d profiles with a chart (%.0fs)'
        % (len(small), args.vmax, nch, nroot, time.time() - t))
    probe = [F for F in small if 6 <= C.area(F) <= 9]
    nmiss = sum(1 for F in probe if finder_band_misaligned(C.cells(F)) != K.finder_band(C.cells(F)))
    assert nmiss > 0
    say('PASS (control: misaligned search): search B with its upper band one row off disagrees with the true '
        'chart set on %d of %d profiles of 6..9 cells' % (nmiss, len(probe)))

    # ------------------------------------------------------------ V2: forward compositions
    t = time.time()
    boxes = ((4, 5), (5, 4)) if args.box == 'small' else ((4, 6), (5, 5), (6, 4))
    gen = {}
    for dmax, emax in boxes:
        Ds = [C.cells(F) for N in range(2, dmax + 1) for F in C.all_profiles(N)]
        Es = [C.cells(F) for N in range(2, emax + 1) for F in C.all_profiles(N)]
        for E in Es:
            for (B, T, case, v, q) in K.marks(E):
                for D in Ds:
                    F = K.compose(D, E, B, T, case, v)
                    assert K.is_connected_skew(F), 'a composition of connected factors is connected'
                    gen.setdefault(F, {})[(D, E, B, T, case)] = q
    items = [(F, list(g.items())) for F, g in gen.items()]
    ncomp = sum(len(g) for _, g in items)
    bad2, nb = [], 0
    bycase = Counter(k[4] for _, g in items for k, _ in g)
    for sz, nbch, bad in pool.imap_unordered(w_forward, items, chunksize=8):
        nb += nbch
        if bad:
            bad2.append(bad)
    assert not bad2, bad2[:5]
    say('PASS (V2): %d forward compositions (boxes %s, by case %s) give %d connected parents of %d..%d cells; '
        'search B recovers every generating chart (search S too, on parents of <= 24 cells) and every chart '
        'found is legal, recomposed, and obeys the private-diagonal identity and the size bound (%.0fs)'
        % (ncomp, boxes, dict(sorted(bycase.items())), len(items), min(len(F) for F in gen),
           max(len(F) for F in gen), time.time() - t))

    # ------------------------------------------------------------ the census
    classes = load_classes(args.work)
    members = [F for N in sorted(classes) for cl in classes[N] for F in cl]
    t = time.time()
    res = {}
    tb = ts = 0.0
    for prof, s, bad, (a, b) in pool.imap_unordered(w_both, sorted(members, key=lambda F: -C.area(F)), chunksize=2):
        assert not bad, (prof, bad)
        res[prof] = s
        tb += a
        ts += b
    pool.close()
    pool.join()
    for F in members:
        sF, sR = res[F], res[C.rot(F)]
        assert len(sF) == len(sR)
        for (D, E, B, T, case), q in sF.items():
            Er, Br, Tr, cr, vr = K.rotate_mark(E, B, T, case, K.find_mark(E, B, T, case)[3])
            assert sR.get((K.rotate(D), Er, Br, Tr, cr)) == q, 'a chart does not rotate to a chart of F*'
    say('PASS (rotation): every chart of every member rotates (Lemma 3.19(ii)) to a chart of its rotation')
    say('')
    say('TABLE  N | classes | members | rooted | charts | members with 1/2/3/>=4 charts | largest outer | cases a/b/c/d')
    allrows = {}
    for N in sorted(classes):
        mem = [F for cl in classes[N] for F in cl]
        if not mem:
            continue
        nr = sum(1 for F in mem if res[F])
        nchart = sum(len(res[F]) for F in mem)
        dist = Counter(min(len(res[F]), 4) for F in mem)
        maxD = max(len(k[0]) for F in mem for k in res[F])
        cases = Counter(k[4] for F in mem for k in res[F])
        row = (len(classes[N]), len(mem), nr, nchart, dist[1], dist[2], dist[3], dist[4], maxD,
               cases['a'], cases['b'], cases['c'], cases['d'])
        allrows[N] = row
        say('TABLE %2d | %s' % (N, ' | '.join(map(str, row))))
        if N in EXPECTED:
            assert tuple(EXPECTED[N]) == row, ('published table row differs', N)
    tot = len(members)
    rooted = sum(1 for F in members if res[F])
    assert rooted == tot, 'a member of a nonrotation class has no chart'
    say('PASS (A on the census): all %d members of all %d nonrotation classes of area <= %d have a proper chart '
        '(searches: B %.0fs, S %.0fs of worker time)' % (tot, sum(len(v) for v in classes.values()),
                                                          max(classes), tb, ts))

    # ------------------------------------------------------------ base rate
    rng = random.Random(20261003)
    memset = set(members)
    for Nr in (20, 23, 26):
        samp = set()
        while len(samp) < 300:
            cuts = [i for i in range(1, Nr) if rng.random() < 0.5]
            pts = [0] + cuts + [Nr]
            rows = tuple(pts[i + 1] - pts[i] for i in range(len(pts) - 1))
            gaps = tuple(rng.randrange(min(rows[i], rows[i + 1])) for i in range(len(rows) - 1))
            if (rows, gaps) not in memset:
                samp.add((rows, gaps))
        nr = sum(1 for F in samp if K.finder_band(C.cells(F)))
        assert nr < len(samp)
        say('PASS (control: base rate): %d of 300 random connected profiles of %d cells have a chart' % (nr, Nr))
    say('ALL PASS (%.0fs)' % (time.time() - T0))


if __name__ == '__main__':
    main()
