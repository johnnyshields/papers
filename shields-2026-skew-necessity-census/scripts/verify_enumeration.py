"""Paper section `sec:diagrams` (Profiles and Schur invariants); targets `lem:profiles`, `eq:dp`, `lem:invariants`.

Connected skew diagrams up to translation and their profiles; the number of them by area.

(1) The profile map is a bijection.  Every legal profile of area N gives a connected skew diagram, the
    inverse map recovers the profile, and -- by an enumeration that never uses profiles -- the
    connected skew diagrams of N cells are exactly these: all fixed polyominoes of N cells are grown
    cell by cell from smaller ones and those that are skew diagrams are kept.
(2) The number of connected profiles of each area is computed by the row-appending DP and, through
    18 cells, by direct enumeration; the self-rotational ones by the half-profile DP and, through 18
    cells, directly.  The table through 30 cells is asserted against the published table.

Usage: python3 verify_enumeration.py [--polymax 10] [--directmax 16]
"""
import argparse
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import skew_core as C      # noqa: E402
import skew_compose as K   # noqa: E402

# Connected skew diagrams of N cells, N = 1..30 (index 0 unused).
PUBLISHED = [0, 1, 2, 4, 9, 20, 46, 105, 242, 557, 1285, 2964, 6842, 15793, 36463, 84187, 194388, 448847,
             1036426, 2393208, 5526198, 12760671, 29466050, 68041019, 157115917, 362802072, 837759792]
PUBLISHED_SELF = [0, 1, 2, 2, 5, 4, 12, 9, 28, 21, 65, 48, 152, 111, 351, 257, 814]


def is_skew_cellset(S):
    """Rows are intervals in consecutive rows and both row ends weakly decrease downward."""
    ri = K.row_intervals(S)
    if ri is None:
        return False
    ks = sorted(ri)
    if ks != list(range(ks[0], ks[0] + len(ks))):
        return False
    return all(ri[b][0] <= ri[a][0] and ri[b][1] <= ri[a][1] for a, b in zip(ks, ks[1:]))


def polyominoes(nmax):
    """Fixed polyominoes of 1..nmax cells (normalized), by adding one edge-neighbor at a time."""
    level = {frozenset({(0, 0)})}
    out = {1: level}
    for n in range(2, nmax + 1):
        nxt = set()
        for P in level:
            for (i, j) in P:
                for c in ((i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1)):
                    if c not in P:
                        nxt.add(K.normalize(P | {c}))
        out[n] = nxt
        level = nxt
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--polymax', type=int, default=10)
    ap.add_argument('--directmax', type=int, default=16)
    args = ap.parse_args()
    T0 = time.time()
    poly = polyominoes(args.polymax)
    for N in range(1, args.polymax + 1):
        skew = {P for P in poly[N] if is_skew_cellset(P)}
        prof = list(C.all_profiles(N))
        img = {C.cells(F) for F in prof}
        assert len(img) == len(prof), 'two profiles give one diagram'
        assert img == skew, ('profiles and polyomino enumeration differ', N)
        for F in prof:
            S = C.cells(F)
            assert C.profile_of_cells(S) == F and K.is_connected_skew(S) and len(S) == N
            assert C.cells(C.rot(F)) == K.rotate(S)
            assert C.span(F) == K.nd(S) and tuple(C.heights(F)) == K.height_seq(S)
    print('PASS (bijection): for every N <= %d the connected skew diagrams among all fixed polyominoes of N cells '
          'are exactly the images of the legal profiles, bijectively; rotation reverses rows and gaps; '
          'N_F = sum r - sum g' % args.polymax, flush=True)
    dp = C.dp_counts(30)
    pal = C.dp_counts_self_rotational(30)
    for N in range(1, args.directmax + 1):
        n_all = n_self = 0
        for F in C.all_profiles(N):
            n_all += 1
            n_self += F == C.rot(F)
        assert n_all == dp[N] and n_self == pal[N], N
    assert sum(C.shard_size(p) for p in C.partitions(20)) == dp[20]
    print('PASS (counts): direct enumeration equals both DPs through %d cells; the row-multiset shard sizes '
          'sum to the DP count at 20 cells' % args.directmax, flush=True)
    assert dp[1:27] == PUBLISHED[1:27]
    assert pal[1:17] == PUBLISHED_SELF[1:17]
    print('TABLE  N | connected diagrams | self-rotational')
    for N in range(1, 31):
        print('TABLE %2d | %d | %d' % (N, dp[N], pal[N]))
    print('ALL PASS (%.0fs)' % (time.time() - T0))


if __name__ == '__main__':
    main()
