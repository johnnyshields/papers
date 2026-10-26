"""Paper section `sec:census` (The census); targets `def:census`, `thm:census`, `tab:census`.

The complete list of Schur classes of connected skew diagrams, area by area.

For each area N the connected profiles are processed in shards, one shard per row multiset (a
partition of N).  Inside a shard the candidates are grouped by
    (gap multiset, value of s_F at a random point of F_p),  p = 2^31 - 1,
and every group holding two or more rotation orbits is refined by a second random point and then
CONFIRMED by exact equality of the Jacobi-Trudi polynomials in Z[h_1, h_2, ...].

Why the result is exactly the partition into Schur classes.
  * Area, row multiset and gap (adjacent-overlap) multiset are Schur invariants (degree; Reiner,
    Shaw and van Willigenburg, Cor. 8.11 with k = 1, 2), so a Schur class never leaves a shard or a
    gap block.
  * Evaluation at a point is a ring homomorphism, so Schur-equal diagrams get equal values: a class
    never leaves a value group.  Since s_F = s_{F*}, only one profile of each rotation orbit is
    evaluated (the lexicographically smaller of F, F*).
  * A value group consisting of one orbit {F, F*} is a class by s_{F*} = s_F.  A group of two or
    more orbits is split by exact polynomial equality, so every part is one class.
  * Profiles in different groups have different invariants or different values, hence different
    Schur functions.
So no class can be split (missed) and no two classes can be merged.

Output: a checkpoint per area in WORK (resumable) and WORK/classes.json listing every class with at
least two rotation orbits ("nonrotation classes").  The per-area table printed at the end is
asserted against the published table for every area that was computed.

Usage: python3 verify_classes.py [NMAX] [--work DIR] [--jobs J]      (NMAX defaults to 16)
"""
import argparse
import json
import os
import pickle
import sys
import time
from collections import Counter, defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import skew_core as C   # noqa: E402

SEED1, SEED2 = 20261003, 20261004
HMAX = 40

# Published per-area table: N -> (profiles, classes, size-1, size-2, size-4, size-8, other sizes,
# nonrotation classes, their members).  Filled from the computation; asserted on every rerun.
EXPECTED = {
    1: (1, 1, 1, 0, 0, 0, 0, 0, 0),
    2: (2, 2, 2, 0, 0, 0, 0, 0, 0),
    3: (4, 3, 2, 1, 0, 0, 0, 0, 0),
    4: (9, 7, 5, 2, 0, 0, 0, 0, 0),
    5: (20, 12, 4, 8, 0, 0, 0, 0, 0),
    6: (46, 29, 12, 17, 0, 0, 0, 0, 0),
    7: (105, 57, 9, 48, 0, 0, 0, 0, 0),
    8: (242, 134, 28, 105, 1, 0, 0, 1, 4),
    9: (557, 288, 21, 266, 1, 0, 0, 1, 4),
    10: (1285, 674, 65, 608, 1, 0, 0, 1, 4),
    11: (2964, 1503, 48, 1452, 3, 0, 0, 3, 12),
    12: (6842, 3490, 152, 3331, 7, 0, 0, 7, 28),
    13: (15793, 7947, 111, 7831, 5, 0, 0, 5, 20),
    14: (36463, 18395, 351, 18032, 12, 0, 0, 12, 48),
    15: (84187, 42193, 257, 41907, 29, 0, 0, 29, 116),
    16: (194388, 97580, 814, 96745, 21, 0, 0, 21, 84),
    17: (448847, 224686, 593, 224059, 34, 0, 0, 34, 136),
    18: (1036426, 519073, 1882, 517110, 81, 0, 0, 81, 324),
    19: (2393208, 1197225, 1370, 1195791, 64, 0, 0, 64, 256),
    20: (5526198, 2765141, 4352, 2760657, 131, 1, 0, 132, 532),
    21: (12760671, 6381706, 3165, 6378329, 212, 0, 0, 212, 848),
    22: (29466050, 14737862, 10054, 14727618, 190, 0, 0, 190, 760),
    23: (68041019, 34023851, 7309, 34016231, 310, 1, 0, 311, 1248),
    24: (157115917, 78568933, 23231, 78545063, 638, 1, 0, 639, 2560),
    25: (362802072, 181408955, 16880, 181391556, 518, 1, 0, 519, 2080),
    26: (837759792, 418905913, 53654, 418851451, 807, 1, 0, 808, 3236),
}


def say(*a):
    print(*a, flush=True)


def canonical_mask(R, G):
    """True where (rows, gaps) <= its rotation (lexicographic, rows first then gaps)."""
    def lex_le(A, Ar):
        if A.shape[1] == 0:
            return np.ones(len(A), dtype=bool), np.ones(len(A), dtype=bool)
        d = A != Ar
        has = d.any(axis=1)
        first = np.argmax(d, axis=1)
        idx = np.arange(len(A))
        less = A[idx, first] < Ar[idx, first]
        return has & less, ~has          # strictly less, equal
    rl, re = lex_le(R, R[:, ::-1])
    gl, ge = lex_le(G, G[:, ::-1])
    return rl | (re & (gl | ge)), re & ge


def gap_block_key(G):
    """Exact code of the gap multiset: sum_i 26^{g_i} = sum_g c_g 26^g, injective for n - 1 < 26."""
    key = np.zeros(len(G), dtype=np.int64)
    pw = np.array([26 ** k for k in range(13)], dtype=np.int64)
    for i in range(G.shape[1]):
        key += pw[G[:, i].astype(np.int64)]
    return key


def runs_of(keys_sorted):
    brk = np.nonzero(np.any(np.diff(keys_sorted, axis=0) != 0, axis=1))[0] + 1 \
        if keys_sorted.ndim == 2 else np.nonzero(np.diff(keys_sorted))[0] + 1
    starts = np.concatenate([[0], brk])
    ends = np.concatenate([brk, [len(keys_sorted)]])
    return starts, ends


def process_shard(parts):
    """All profiles with row multiset `parts`.  Returns a dict of tallies and the nonrotation classes."""
    t0 = time.time()
    h1 = C.make_point(SEED1, HMAX)
    h2 = C.make_point(SEED2, HMAX)
    n = len(parts)
    Rs, Gs, Ss, Ks, Vs = [], [], [], [], []
    nprof = 0
    for R, G in C.profile_chunks_of_rowset(parts):
        nprof += len(R)
        keep, selfrot = canonical_mask(R, G)
        R, G, selfrot = R[keep], G[keep], selfrot[keep]
        Rs.append(R)
        Gs.append(G)
        Ss.append(selfrot)
        Ks.append(gap_block_key(G))
        Vs.append(C.eval_batch(R, G, h1))
    R = np.concatenate(Rs)
    G = np.concatenate(Gs)
    S = np.concatenate(Ss)
    K = np.concatenate(Ks)
    V = np.concatenate(Vs)
    del Rs, Gs, Ss, Ks, Vs
    reps = len(R)
    assert nprof == int(2 * reps - S.sum()), 'rotation orbits do not account for every profile'
    assert nprof == C.shard_size(parts), ('shard count', parts)
    order = np.lexsort((V, K))
    keys = np.stack([K[order], V[order]], axis=1)
    starts, ends = runs_of(keys)
    lens = ends - starts
    hist = Counter()
    # singleton groups: one rotation orbit each
    single = order[starts[lens == 1]]
    nself = int(S[single].sum())
    hist[1] += nself
    hist[2] += len(single) - nself
    multi = [(int(s), int(e)) for s, e in zip(starts[lens >= 2], ends[lens >= 2])]
    coll1 = len(multi)
    nontriv = []
    false_merge = 0
    exact_runs = 0
    for s, e in multi:
        idx = order[s:e]
        mem = [(tuple(int(x) for x in R[i]), tuple(int(x) for x in G[i])) for i in idx]
        sub = defaultdict(list)
        for F in mem:
            sub[C.eval_one(F, h2)].append(F)
        for grp in sub.values():
            if len(grp) == 1:
                F = grp[0]
                hist[1 if F == C.rot(F) else 2] += 1
                continue
            exact_runs += 1
            ex = defaultdict(list)
            for F in grp:
                ex[C.poly_key(C.jt_poly(F))].append(F)
            false_merge += len(ex) - 1
            for cl in ex.values():
                members = sorted({F for G0 in cl for F in (G0, C.rot(G0))})
                hist[len(members)] += 1
                if len(cl) >= 2:
                    nontriv.append(members)
    return dict(parts=parts, n=n, profiles=nprof, reps=reps, hist=dict(hist), nontrivial=nontriv,
                coll1=coll1, false_merge=false_merge, exact_runs=exact_runs, secs=time.time() - t0)


def area_table(res):
    hist = Counter()
    nprof = 0
    nontriv = []
    fm = 0
    for r in res.values():
        hist.update(r['hist'])
        nprof += r['profiles']
        nontriv += r['nontrivial']
        fm += r['false_merge']
    classes = sum(hist.values())
    other = sum(v for k, v in hist.items() if k not in (1, 2, 4, 8))
    members = sum(len(c) for c in nontriv)
    return (nprof, classes, hist[1], hist[2], hist[4], hist[8], other, len(nontriv), members), \
        nontriv, fm, hist


def run_area(N, work, jobs):
    path = os.path.join(work, 'area-%02d.pkl' % N)
    if os.path.exists(path):
        return pickle.load(open(path, 'rb'))
    part_path = path + '.partial'
    res = pickle.load(open(part_path, 'rb')) if os.path.exists(part_path) else {}
    total = sum(1 for _ in C.partitions(N))
    shards = [p for p in C.partitions(N) if p not in res]
    shards.sort(key=lambda p: -C.shard_size(p))
    t0 = time.time()
    last = time.time()
    if shards:
        if jobs > 1:
            import multiprocessing as mp
            pool = mp.get_context('fork').Pool(jobs, maxtasksperchild=50)
            it = pool.imap_unordered(process_shard, shards, chunksize=1)
        else:
            pool = None
            it = map(process_shard, shards)
        for r in it:
            res[r['parts']] = r
            if time.time() - last > 60:
                pickle.dump(res, open(part_path + '.tmp', 'wb'))
                os.replace(part_path + '.tmp', part_path)
                last = time.time()
                say('  N=%d: %d/%d shards, %.0fs' % (N, len(res), total, time.time() - t0))
        if pool is not None:
            pool.close()
            pool.join()
    assert set(res) == set(C.partitions(N))
    out = dict(N=N, shards=res, secs=time.time() - t0)
    pickle.dump(out, open(path + '.tmp', 'wb'))
    os.replace(path + '.tmp', path)
    if os.path.exists(part_path):
        os.remove(part_path)
    return out


def exact_small_census(N):
    """Control: the Schur classes of area N computed with NO invariant and NO evaluation, by grouping
    every profile on its exact polynomial."""
    ex = defaultdict(list)
    for F in C.all_profiles(N):
        ex[C.poly_key(C.jt_poly(F))].append(F)
    return sorted(sorted(cl) for cl in ex.values())


def two_instruments(cl):
    """Both exact instruments on every member of a class; all must give one polynomial.  Returns a
    SHA-256 digest of it, used only to show that different classes have different polynomials (a digest
    collision could only produce a false alarm there)."""
    import hashlib
    p0 = None
    for F in cl:
        a = C.poly_key(C.jt_poly(F))
        assert a == C.poly_key(C.jt_poly_flint(F)), ('exact instruments disagree', C.fmt(F))
        assert p0 is None or a == p0, ('class members differ exactly', C.fmt(F))
        p0 = a
    return hashlib.sha256(repr(p0).encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('nmax', nargs='?', type=int, default=16)
    ap.add_argument('--work', default=os.environ.get('SKEWBASE_WORK', os.path.join(HERE, '_work')))
    ap.add_argument('--jobs', type=int, default=int(os.environ.get('SKEWBASE_JOBS', '4')))
    args = ap.parse_args()
    assert args.nmax <= 26, 'the gap-multiset code is injective only through 26 cells'
    os.makedirs(args.work, exist_ok=True)
    T0 = time.time()
    dp = C.dp_counts(args.nmax)
    pal = C.dp_counts_self_rotational(args.nmax)
    say('Schur-class census of connected skew diagrams through %d cells (work: %s, %d jobs)'
        % (args.nmax, args.work, args.jobs))
    tables, allnt = {}, {}
    for N in range(1, args.nmax + 1):
        out = run_area(N, args.work, args.jobs)
        row, nontriv, fm, hist = area_table(out['shards'])
        assert row[0] == dp[N], ('enumeration count differs from the DP', N, row[0], dp[N])
        selfrot = 2 * sum(r['reps'] for r in out['shards'].values()) - row[0]
        assert selfrot == pal[N], ('self-rotational count differs from the DP', N, selfrot, pal[N])
        for cl in nontriv:
            assert all(C.rot(F) in cl for F in cl), 'class not closed under rotation'
            assert len({C.canon(F) for F in cl}) >= 2
            assert all(C.area(F) == N for F in cl)
            assert len({tuple(sorted(F[0])) for F in cl}) == 1 and len({tuple(sorted(F[1])) for F in cl}) == 1
        tables[N] = row
        allnt[N] = sorted(nontriv)
        say('N=%2d  profiles %11d  classes %11d  sizes 1:%d 2:%d 4:%d 8:%d other:%d  nonrotation classes %d '
            '(%d members)  false merges split exactly: %d  [%.0fs]'
            % ((N,) + row[:2] + row[2:7] + row[7:9] + (fm, out['secs'])))
        if N in EXPECTED:
            assert tuple(EXPECTED[N]) == row, ('published table row differs', N, EXPECTED[N], row)
    say('PASS (enumeration): the census evaluated exactly the DP count of connected profiles at every area '
        '1..%d (%d in total), and its rotation-orbit representatives account for exactly the DP count of '
        'self-rotational profiles' % (args.nmax, sum(dp[1:args.nmax + 1])))
    say('PASS (classes): every nonrotation class is closed under rotation and lies in one row multiset and one '
        'gap multiset; %d nonrotation classes, %d members through %d cells'
        % (sum(len(v) for v in allnt.values()), sum(len(c) for v in allnt.values() for c in v), args.nmax))
    checked = [N for N in tables if N in EXPECTED]
    say('PASS (published table): rows asserted for areas %s' % (checked if checked else 'none (table not yet filled)'))

    # ---------------------------------------------------------------- controls
    # (1) Without invariants or evaluation: exact grouping of every profile of area <= 11.
    for N in range(1, min(args.nmax, 11) + 1):
        ex = exact_small_census(N)
        nt = sorted(cl for cl in ex if len({C.canon(F) for F in cl}) >= 2)
        assert nt == allnt[N], ('exact-only census differs', N)
        assert len(ex) == tables[N][1]
    say('PASS (control: exact-only census): grouping every profile of area <= %d by its exact polynomial alone '
        'gives the same classes and class counts' % min(args.nmax, 11))
    # (2) A known ribbon pair: (1,2,1,3,2) and (1,3,2,1,2) are Schur-equal and not rotations.
    if args.nmax >= 9:
        A, B = ((1, 2, 1, 3, 2), (0, 0, 0, 0)), ((1, 3, 2, 1, 2), (0, 0, 0, 0))
        assert any(A in cl and B in cl for cl in allnt[9])
        say('PASS (control: ribbon pair): the 9-cell ribbons (1,2,1,3,2) and (1,3,2,1,2) are found in one class')
    # (3) A perturbed member leaves its class: the exact check and the evaluation both separate it.
    h1 = C.make_point(SEED1, HMAX)
    nsplit = 0
    for N in sorted(allnt):
        for cl in allnt[N]:
            F = cl[0]
            rows, gaps = list(F[0]), list(F[1])
            for i in range(len(gaps) - 1):
                g2 = gaps[:]
                g2[i], g2[i + 1] = g2[i + 1], g2[i]
                G0 = (tuple(rows), tuple(g2))
                if g2 != gaps and C.valid(*G0) and G0 not in cl:
                    if len(rows) <= 14:
                        assert C.poly_key(C.jt_poly(G0)) != C.poly_key(C.jt_poly(F))
                    assert C.eval_one(G0, h1) != C.eval_one(F, h1)
                    nsplit += 1
                    break
    assert nsplit > 0 or args.nmax < 8
    say('PASS (control: perturbation): swapping two adjacent gaps of a class member produces a profile with the '
        'same invariants that is separated by evaluation, and by the exact polynomial when it has at most 14 rows '
        '(%d classes tested)' % nsplit)
    # (4) Fault injection: grouping with a corrupted evaluation (one profile evaluated at a different point)
    #     must break a class, so the grouping step can fail.
    if args.nmax >= 8:
        cl = allnt[8][0]
        h_bad = C.make_point(SEED1 + 99, HMAX)
        vals = [C.eval_one(F, h1) for F in cl[:-1]] + [C.eval_one(cl[-1], h_bad)]
        assert len(set(vals)) == 2
        say('PASS (control: fault injection): evaluating one member of an 8-cell class at a different point splits it')
    # (5) The two exact instruments agree on every member of every nonrotation class.
    flat = [cl for N in sorted(allnt) for cl in allnt[N]]
    import multiprocessing as mp
    with mp.get_context('fork').Pool(args.jobs) as pool:
        fl = list(pool.imap(two_instruments, flat, chunksize=1))
    assert len(set(fl)) == len(fl)
    say('PASS (exact instruments): Laplace expansion and fraction-free fmpz_mpoly elimination give the same '
        'polynomial on all %d members; the %d class polynomials are pairwise distinct'
        % (sum(len(cl) for cl in flat), len(fl)))

    json.dump({str(N): [[[list(F[0]), list(F[1])] for F in cl] for cl in allnt[N]] for N in allnt},
              open(os.path.join(args.work, 'classes.json'), 'w'))
    say('')
    say('TABLE  N | profiles | classes | size 1 | size 2 | size 4 | size 8 | other | nonrotation classes | members')
    for N in sorted(tables):
        say('TABLE %2d | %s' % (N, ' | '.join(str(x) for x in tables[N])))
    tot = [sum(tables[N][k] for N in tables) for k in range(9)]
    say('TABLE all | %s' % ' | '.join(str(x) for x in tot))
    say('ALL PASS (%.0fs)' % (time.time() - T0))


if __name__ == '__main__':
    main()
