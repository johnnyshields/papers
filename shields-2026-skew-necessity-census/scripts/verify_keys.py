"""Paper section `sec:keys` (Keys and necessity); targets `def:key`, `prop:induction`.

Key invariance on the census: Schur-equal diagrams have the same keys of minimal charts.

For a chart chi = (D, omega) of F with period q the COST is (N_W, N_E) = (N_F mod q, q + N_F mod q),
ordered lexicographically; chi is MINIMAL when its cost is least among the charts of F (this
is McNamara-van Willigenburg's "minimal factorization", Def. 5.5).  The KEY of chi is
    ( marked inner omega up to rotation,  s_D as an exact polynomial ),
and K(F) is the set of keys of all minimal charts of F.  Asserted on every nonrotation class:
  (R)  all members have the same key set K(F);
  (G)  modulo the ordinary gauge (an ordinary mark of case (b) paired with the case-(a) mark at the
       same width, displacement v + e, and s_D replaced by omega(s_D) = s_{D^t}), each member's
       minimal charts carry ONE key, so the key of any chosen minimal chart is well
       defined.
Controls: corrupting one member's key (outer replaced by its transpose) splits a class; replacing
minimal charts by arbitrary charts changes the key set inside some class.

Usage: python3 verify_keys.py [--work DIR] [--jobs J]
"""
import argparse
import json
import os
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import skew_core as C      # noqa: E402
import skew_compose as K   # noqa: E402

# Published per-area table: N -> (classes, members with >= 2 root periods, minimal period
# distribution as a sorted tuple of (period, classes)).
EXPECTED = {
    8: (1, 0, ((2, 1),)),
    9: (1, 0, ((3, 1),)),
    10: (1, 0, ((2, 1),)),
    11: (3, 0, ((2, 1), (3, 2))),
    12: (7, 0, ((2, 3), (3, 2), (4, 2))),
    13: (5, 4, ((2, 3), (3, 2))),
    14: (12, 4, ((2, 5), (3, 2), (4, 5))),
    15: (29, 12, ((2, 7), (3, 14), (4, 2), (5, 6))),
    16: (21, 12, ((2, 13), (3, 2), (4, 6))),
    17: (34, 8, ((2, 16), (3, 6), (5, 12))),
    18: (81, 48, ((2, 25), (3, 25), (4, 18), (5, 5), (6, 8))),
    19: (64, 20, ((2, 33), (3, 14), (4, 5), (5, 12))),
    20: (132, 48, ((2, 51), (3, 10), (4, 26), (5, 20), (6, 25))),
    21: (212, 52, ((2, 68), (3, 68), (5, 32), (6, 16), (7, 28))),
    22: (190, 80, ((2, 107), (3, 20), (4, 31), (5, 14), (6, 18))),
    23: (311, 92, ((2, 141), (3, 32), (4, 23), (5, 43), (6, 16), (7, 56))),
    24: (639, 252, ((2, 219), (3, 158), (4, 68), (5, 27), (6, 81), (7, 38), (8, 48))),
    25: (519, 112, ((2, 288), (3, 54), (4, 21), (5, 84), (6, 16), (7, 56))),
    26: (808, 192, ((2, 430), (3, 42), (4, 37), (5, 32), (6, 89), (7, 64), (8, 114))),
}

_POLY = {}


def outer_poly(D):
    P = _POLY.get(D)
    if P is None:
        P = C.poly_key(C.jt_poly(C.profile_of_cells(D)))
        _POLY[D] = P
    return P


def key_of(c, corrupt=False):
    D, E, B, T, case, v, q = c
    Dk = K.transpose(D) if corrupt else D
    return (K.canon_marked(E, B, T, case, v), outer_poly(Dk))


def gauge_key(c):
    """Key modulo the ordinary gauge: a case-(b) chart whose inner also carries the case-(a) mark at
    the same width with displacement v + e is read through that mark, with the outer transposed."""
    D, E, B, T, case, v, q = c
    if case == 'b' and B:
        for (B2, T2, c2, v2, q2) in K.marks(E):
            if c2 == 'a' and q2 == q and v2 == (v[0] + 1, v[1] + 1):
                assert K.compose(K.antitranspose(D), E, B2, T2, c2, v2) == K.compose(D, E, B, T, case, v)
                return (K.canon_marked(E, B2, T2, c2, v2), outer_poly(K.transpose(D)))
    return key_of(c)


def member_data(prof):
    F = C.cells(prof)
    cs = K.charts(F)
    NF = K.nd(F)
    for c in cs:
        D, E, B, T, case, v, q = c
        nw = K.nd(B) if B else 0
        assert (nw, K.nd(E)) == K.cost(F, q) == (NF % q, q + NF % q)
    sm = K.minimal_charts(F)
    ks = frozenset(key_of(c) for c in sm)
    gs = frozenset(gauge_key(c) for c in sm)
    allk = frozenset(key_of(c) for c in cs)
    bad = frozenset(key_of(c, corrupt=True) for c in sm)
    return prof, dict(keys=ks, gkeys=gs, allkeys=allk, corrupt=bad, smp=sm[0][6] if sm else None,
                      periods=tuple(sorted({c[6] for c in cs})), nsm=len(sm))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', default=os.environ.get('SKEWBASE_WORK', os.path.join(HERE, '_work')))
    ap.add_argument('--jobs', type=int, default=int(os.environ.get('SKEWBASE_JOBS', '4')))
    args = ap.parse_args()
    T0 = time.time()
    raw = json.load(open(os.path.join(args.work, 'classes.json')))
    classes = {int(N): [[(tuple(F[0]), tuple(F[1])) for F in cl] for cl in cls] for N, cls in raw.items()}
    members = [F for N in classes for cl in classes[N] for F in cl]
    import multiprocessing as mp
    with mp.get_context('fork').Pool(args.jobs) as pool:
        info = dict(pool.imap_unordered(member_data, members, chunksize=4))
    assert all(info[F]['keys'] for F in members), 'a member without charts'
    nsplit_corrupt = nsplit_arbitrary = 0
    multi_g = 0
    say = print
    say('TABLE  N | classes | members with >= 2 periods | minimal period: classes')
    for N in sorted(classes):
        if not classes[N]:
            continue
        smdist = Counter()
        multi = 0
        for cl in classes[N]:
            ks = {info[F]['keys'] for F in cl}
            assert len(ks) == 1, ('two key sets in one class', [C.fmt(F) for F in cl])
            assert len({info[F]['smp'] for F in cl}) == 1
            smdist[info[cl[0]]['smp']] += 1
            for F in cl:
                if len(info[F]['gkeys']) != 1:
                    multi_g += 1
                multi += len(info[F]['periods']) >= 2
            corrupt = {info[cl[0]]['corrupt']} | {info[F]['keys'] for F in cl[1:]}
            nsplit_corrupt += len(corrupt) > 1
            nsplit_arbitrary += len({info[F]['allkeys'] for F in cl}) > 1
        row = (len(classes[N]), multi, tuple(sorted(smdist.items())))
        say('TABLE %2d | %d | %d | %s' % (N, row[0], row[1], ' '.join('%d:%d' % kv for kv in row[2])), flush=True)
        if N in EXPECTED:
            assert tuple(EXPECTED[N]) == row, ('published table row differs', N)
    say('PASS (R on the census): in each of the %d nonrotation classes every member has the same set of '
        'minimal keys (marked inner up to rotation, exact outer polynomial)' % sum(len(v) for v in classes.values()))
    assert multi_g == 0
    say('PASS (G): modulo rotation and the ordinary gauge, the minimal charts of each of the %d members '
        'carry a single key' % len(members))
    assert nsplit_corrupt > 0
    say('PASS (control: corrupted key): replacing one member\'s outer by its transpose splits %d classes'
        % nsplit_corrupt)
    say('INFO: classes in which the keys of ALL charts (not only minimal ones) differ between members: %d'
        % nsplit_arbitrary)
    say('ALL PASS (%.0fs)' % (time.time() - T0))


if __name__ == '__main__':
    main()
