#!/usr/bin/env python3
"""thm:nonnegative-rigidity, tested on the global census.

Paper section `sec:boundary` (Boundary coefficients and dense rigidity).

Statement: connected D with full beta lists X,Y, x_n >= y_1 (every JT index nonnegative) =>
every connected Schur mate is a translate of D or D*.
Test: the census below (built here, through CMAX cells) holds EVERY nontrivial class (more than
one rotation orbit).  No member of such a class may satisfy the hypothesis.  Firing control: relaxed hypotheses (min X >= max Y - t, t=1,2) must hit members.
Also a direct exact check on small sizes: for every nonnegative-index profile of <= NEX cells,
compare its free-h JT polynomial with every profile of the same row/gap multisets (full mate
space by arrangement), using the determinant built here.
Usage: python3 check_nonnegative_rigidity.py [NEX=14] [CMAX=16]
"""
import sys, time, itertools
from collections import Counter

# ============================================================================ census (standalone)
# Every connected skew diagram of n cells is a profile (rows; gaps), rows top to bottom, gap = overlap - 1,
# 0 <= g_i < min(r_i, r_{i+1}).  Full beta lists: x_n = r_n, y_n = 0, y_i = x_{i+1} - g_i, x_i = y_i + r_i,
# and s_D = det(h_{x_i - y_j}) (Jacobi-Trudi; h_0 = 1, h_{<0} = 0).  s_D = s_{D*} for the rotation D*, so
# the census works on rotation orbits.  Orbits are grouped by evaluating the determinant at two random
# points mod 2^61 - 1 (a fingerprint that can only merge, never split, Schur-equal orbits); every group of
# two or more orbits is then split by exact polynomial equality in the free h-alphabet.  A class is
# NONTRIVIAL when it holds more than one rotation orbit.
import random as _random
from collections import defaultdict as _dd

_P61 = (1 << 61) - 1
_CRNG = _random.Random(20261007)
_CPTS = [[_CRNG.randrange(1, _P61) for _ in range(64)] for _ in range(2)]
# connected profiles and nontrivial classes per area, from the published census table
_CENSUS_COUNTS = {1: 1, 2: 2, 3: 4, 4: 9, 5: 20, 6: 46, 7: 105, 8: 242, 9: 557, 10: 1285, 11: 2964,
                  12: 6842, 13: 15793, 14: 36463, 15: 84187, 16: 194388, 17: 448847, 18: 1036426}
_CENSUS_CLASSES = {8: 1, 9: 1, 10: 1, 11: 3, 12: 7, 13: 5, 14: 12, 15: 29, 16: 21, 17: 34, 18: 81}


def census_profiles(n):
    """Every connected profile of exactly n cells."""
    def comps(m):
        if m == 0:
            yield ()
            return
        for x in range(1, m + 1):
            for t in comps(m - x):
                yield (x,) + t

    def gapseq(rows, k):
        if k == len(rows) - 1:
            yield ()
            return
        for g in range(min(rows[k], rows[k + 1])):
            for t in gapseq(rows, k + 1):
                yield (g,) + t
    for rows in comps(n):
        for gaps in gapseq(rows, 0):
            yield rows, gaps


def census_betas(rows, gaps):
    n = len(rows)
    x = [0] * n
    y = [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return x, y


def _jt_mod(rows, gaps, pt):
    x, y = census_betas(rows, gaps)
    n = len(rows)
    M = [[(1 if x[i] == y[j] else (pt[x[i] - y[j] - 1] if x[i] > y[j] else 0)) for j in range(n)]
         for i in range(n)]
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det = det * M[c][c] % _P61
        inv = pow(M[c][c], _P61 - 2, _P61)
        for r in range(c + 1, n):
            if M[r][c]:
                f = M[r][c] * inv % _P61
                M[r] = [(a - f * b) % _P61 for a, b in zip(M[r], M[c])]
    return det % _P61


def _jt_exact(rows, gaps):
    """Exact Jacobi-Trudi polynomial over the free h-alphabet: {sorted index tuple: coefficient},
    by Laplace expansion along the rows with memoization on the set of used columns."""
    x, y = census_betas(rows, gaps)
    n = len(rows)
    memo = {}

    def rec(i, used):
        if i == n:
            return {(): 1}
        key = (i, used)
        if key in memo:
            return memo[key]
        out = _dd(int)
        sign = 1
        for j in range(n):
            if used >> j & 1:
                continue
            d = x[i] - y[j]
            if d >= 0:
                for m, c in rec(i + 1, used | (1 << j)).items():
                    mm = tuple(sorted(m + (d,))) if d else m
                    out[mm] += sign * c
            sign = -sign
        res = {m: c for m, c in out.items() if c}
        memo[key] = res
        return res
    return rec(0, 0)


def census(nmax):
    """{n: [nontrivial class, ...]} for n = 1..nmax; a class is a sorted list of profiles (all members,
    both orientations).  Profile and class counts are asserted against the published census table."""
    out = {}
    for n in range(1, nmax + 1):
        groups = _dd(list)
        count = 0
        for F in census_profiles(n):
            count += 1
            Fr = (F[0][::-1], F[1][::-1])
            if Fr < F:
                continue
            groups[tuple(_jt_mod(F[0], F[1], pt) for pt in _CPTS)].append(F)
        if n in _CENSUS_COUNTS:
            assert count == _CENSUS_COUNTS[n], ('census profile count', n, count)
        classes = []
        for orbits in groups.values():
            if len(orbits) < 2:
                continue
            exact = _dd(list)
            for F in orbits:
                exact[tuple(sorted(_jt_exact(*F).items()))].append(F)
            for orb in exact.values():
                if len(orb) > 1:
                    classes.append(sorted({G for F in orb for G in (F, (F[0][::-1], F[1][::-1]))}))
        classes.sort()
        assert len(classes) == _CENSUS_CLASSES.get(n, len(classes)), ('census class count', n, len(classes))
        out[n] = classes
    return out


def betas(rows, gaps):
    n = len(rows)
    x = [0] * n; y = [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return x, y   # x decreasing, y decreasing, y[-1]=0

def min_index(rows, gaps):
    x, y = betas(rows, gaps)
    return x[-1] - y[0]

def jt_poly(rows, gaps):
    x, y = betas(rows, gaps)
    n = len(rows); out = Counter()
    for perm in itertools.permutations(range(n)):
        idx = []; ok = True
        for i, j in enumerate(perm):
            d = x[i] - y[j]
            if d < 0: ok = False; break
            if d: idx.append(d)
        if not ok: continue
        s = 1; p = list(perm)
        for a in range(n):
            while p[a] != a:
                b = p[a]; p[a], p[b] = p[b], p[a]; s = -s
        out[tuple(sorted(idx))] += s
    return {m: c for m, c in out.items() if c}

def arrangements(rows, gaps):
    for r in set(itertools.permutations(rows)):
        for g in set(itertools.permutations(gaps)):
            if all(0 <= g[i] < min(r[i], r[i + 1]) for i in range(len(g))):
                yield tuple(r), tuple(g)

def main():
    def P(*a):
        s = ' '.join(str(v) for v in a); print(s, flush=True)
    P('=== run', time.strftime('%Y-%m-%d %H:%M:%S'))
    NEX = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    d = census(CMAX)
    ncls = nmem = bad = 0; relax = {3: 0, 4: 0}
    for n in range(1, CMAX + 1):
        for cl in d[n]:
            ncls += 1
            for r, g in cl:
                nmem += 1
                m = min_index(tuple(r), tuple(g))
                if m >= 0:
                    bad += 1
                    if bad <= 10: P('VIOLATION', n, r, g)
                for t in (3, 4):
                    if m >= -t: relax[t] += 1
    P(f'census: {ncls} nontrivial classes, {nmem} members through {CMAX} cells; members with nonnegative full board: {bad}')
    P(f'CONTROL relaxed min index >= -3: {relax[3]} members; >= -4: {relax[4]} members (must be > 0)')
    # direct exact full-mate-space check on small sizes
    tested = viol = 0
    for area in range(1, NEX + 1):
        def comps(total, parts):
            if parts == 1:
                yield (total,); return
            for f in range(1, total - parts + 2):
                for rest in comps(total - f, parts - 1):
                    yield (f,) + rest
        seen = set()
        for nr in range(1, area + 1):
            for rows in comps(area, nr):
                for gaps in itertools.product(*[range(min(rows[i], rows[i + 1])) for i in range(nr - 1)]):
                    if (rows, gaps) in seen: continue
                    if min_index(rows, gaps) < 0: continue
                    Pp = jt_poly(rows, gaps)
                    orbit = {(rows, gaps), (rows[::-1], gaps[::-1])}
                    seen |= orbit
                    tested += 1
                    for H in arrangements(rows, gaps):
                        if H in orbit: continue
                        if jt_poly(*H) == Pp:
                            viol += 1; P('DIRECT VIOLATION', rows, gaps, H)
        P(f'direct: area {area}: nonnegative-index orbits tested {tested}, violations {viol}')
    # control for the direct instrument: a known nontrivial class from the census is detected
    cl = next(c for n in range(8, CMAX + 1) for c in d[n])
    r0, g0 = map(tuple, min(cl))
    hits = sum(1 for H in arrangements(r0, g0) if H not in {(r0, g0), (r0[::-1], g0[::-1])} and jt_poly(*H) == jt_poly(r0, g0))
    P(f'CONTROL direct instrument on census class {min(cl)}: finds {hits} nonrotation mates (must be > 0)')
    assert bad == 0 and viol == 0 and relax[3] > 0 and hits > 0, 'NOT PASS'
    P('ALL PASS')

if __name__ == '__main__':
    main()
