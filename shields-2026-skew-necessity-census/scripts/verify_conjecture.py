"""Paper sections `sec:keys` (Keys and necessity) and `sec:results` (The computation and the proof of the main theorem); targets `conj:mvw`, `thm:main`.

McNamara-van Willigenburg Conjecture 5.7 on the census.

(only if)  For every ordered pair (X, Y) in every nonrotation class, an explicit common presentation
           X = (...((E_1 o E_2) o E_3)...) o E_r,  Y = the same with each factor (and its marks) kept or
           rotated, is built by the outer-prefix induction of the paper -- a common minimal key
           gives charts X = D_X o_w E, Y = D_Y o_w' E' with w' in {w, w*} and s_{D_X} = s_{D_Y}, and the
           induction is applied to (D_X, D_Y) -- and then checked by recomposing both sides literally.
           A pair in a rotation orbit uses the one-factor presentation.
(if)       Every factor reversal of every chart of every member, and every reversal variant of every
           irreducible factorization found below, is Schur-equal to the member (exact class membership).
(size)     For every member of a nonrotation class, every irreducible factorization in the sense of
           Def. 5.5 (first factor without proper charts, each step minimal) is enumerated, and
           |class| = 2^r is asserted, r counting the factors E_i with E_i != E_i*; r is asserted to be the
           same for every irreducible factorization.  The reversal variants of every irreducible
           factorization are asserted to be exactly the class.  With --csmax M the same is asserted for
           every connected diagram of at most M cells, against its class size from the census.

Usage: python3 verify_conjecture.py [--work DIR] [--jobs J] [--csmax M] [--csmin M0]
"""
import argparse
import itertools
import json
import os
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import skew_core as C      # noqa: E402
import skew_compose as K   # noqa: E402

# Published per-area table: N -> (ordered pairs certified, longest certificate, members, irreducible
# factorizations, classes of size 4 with r = 2, classes of size 8 with r = 3).
EXPECTED = {
    8: (4, 4, 1, 0, 2),
    9: (4, 4, 1, 0, 2),
    10: (4, 4, 1, 0, 2),
    11: (12, 12, 3, 0, 2),
    12: (28, 28, 7, 0, 2),
    13: (20, 20, 5, 0, 3),
    14: (48, 48, 12, 0, 3),
    15: (116, 116, 29, 0, 3),
    16: (84, 84, 21, 0, 3),
    17: (136, 136, 34, 0, 3),
    18: (324, 324, 81, 0, 3),
    19: (256, 256, 64, 0, 3),
    20: (532, 532, 131, 1, 3),
    21: (848, 848, 212, 0, 3),
    22: (760, 760, 190, 0, 3),
    23: (1248, 1252, 310, 1, 4),
    24: (2560, 2568, 638, 1, 3),
    25: (2080, 2080, 518, 1, 4),
    26: (3236, 3244, 807, 1, 4),
}

_POLY = {}


def poly(S):
    P = _POLY.get(S)
    if P is None:
        P = C.poly_key(C.jt_poly(C.profile_of_cells(S)))
        _POLY[S] = P
    return P


def key_of(c):
    D, E, B, T, case, v, q = c
    return (K.canon_marked(E, B, T, case, v), poly(D))


def realize(pres):
    """Compose a presentation [E_1, (E_2, B_2, T_2, case_2, v_2), ...] left to right."""
    S = pres[0]
    for (E, B, T, case, v) in pres[1:]:
        S = K.compose(S, E, B, T, case, v)
    return S


def rot_factor(f):
    if isinstance(f, frozenset):
        return K.rotate(f)
    E, B, T, case, v = f
    return K.rotate_mark(E, B, T, case, v)


def common_presentation(X, Y, depth=0):
    """Common presentations of Schur-equal connected diagrams X, Y (cell sets)."""
    if Y == X or Y == K.rotate(X):
        return [X], [Y]
    kx = {key_of(c): c for c in K.minimal_charts(X)}
    ky = {key_of(c): c for c in K.minimal_charts(Y)}
    common = sorted(set(kx) & set(ky))
    assert common, 'no common minimal key'
    cx, cy = kx[common[0]], ky[common[0]]
    wx, wy = cx[1:6], cy[1:6]
    assert wy == wx or tuple(wy) == tuple(rot_factor(wx)), 'marked inners not equal up to rotation'
    assert poly(cx[0]) == poly(cy[0])
    PX, PY = common_presentation(cx[0], cy[0], depth + 1)
    return PX + [tuple(wx)], PY + [tuple(wy)]


def check_pair(item):
    X, Y = item
    PX, PY = common_presentation(C.cells(X), C.cells(Y))
    assert realize(PX) == C.cells(X) and realize(PY) == C.cells(Y)
    assert len(PX) == len(PY)
    for a, b in zip(PX, PY):
        assert b == a or b == rot_factor(a)
    return len(PX)


_IRR = {}


def irreducible_factorizations(F):
    """Every irreducible factorization of F (Def. 5.5), as lists [E_1, w_2, ..., w_r]."""
    got = _IRR.get(F)
    if got is not None:
        return got
    sm = K.minimal_charts(F)
    if not sm:
        got = [[F]]
    else:
        got = []
        for (D, E, B, T, case, v, q) in sm:
            for pre in irreducible_factorizations(D):
                got.append(pre + [(E, B, T, case, v)])
    _IRR[F] = got
    return got


def nonsym_count(pres, marked=False):
    r = 0
    for f in pres:
        if isinstance(f, frozenset):
            r += f != K.rotate(f)
        elif marked:
            r += not K.is_symmetric_marked(*f)
        else:
            r += f[0] != K.rotate(f[0])
    return r


def variants(pres):
    out = set()
    for bits in itertools.product((0, 1), repeat=len(pres)):
        out.add(realize([rot_factor(f) if b else f for f, b in zip(pres, bits)]))
    return out


def size_check(item):
    """(profile, class size, class members or None) -> (#irreducible factorizations, r values, ok flags)."""
    prof, size, cl = item
    F = C.cells(prof)
    facts = irreducible_factorizations(F)
    rs = {nonsym_count(p) for p in facts}
    rsm = {nonsym_count(p, marked=True) for p in facts}
    clset = {C.cells(G) for G in cl} if cl else {F, K.rotate(F)}
    gen_ok = gen_eq = True
    for p in facts:
        V = variants(p)
        gen_ok &= V <= clset
        gen_eq &= V == clset
    return prof, len(facts), tuple(sorted(rs)), tuple(sorted(rsm)), gen_ok, gen_eq, max(len(p) for p in facts)


def trim_caches(limit=300000):
    for cache in (K._CHARTS, K._MARKS, K._SWH, _IRR, _POLY):
        if len(cache) > limit:
            cache.clear()


def cs_chunk(chunk):
    """Class-size clause on a chunk of profiles of one area: (profile, class size, class or None)."""
    out = []
    for item in chunk:
        prof, size, cl = item
        _, nfac, rs, rsm, gen_ok, gen_eq, mx = size_check(item)
        ok = gen_ok and gen_eq and len(rs) == 1 and 2 ** rs[0] == size and rsm == rs
        out.append((prof, ok, mx > 1))
    K._CHARTS.clear()
    _IRR.clear()
    trim_caches()
    return out


def cs_items(N, member_of, chunk=500):
    buf = []
    for F in C.all_profiles(N):
        cl = member_of.get(F)
        buf.append((F, len(cl) if cl else (1 if F == C.rot(F) else 2), cl))
        if len(buf) == chunk:
            yield buf
            buf = []
    if buf:
        yield buf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', default=os.environ.get('SKEWBASE_WORK', os.path.join(HERE, '_work')))
    ap.add_argument('--jobs', type=int, default=int(os.environ.get('SKEWBASE_JOBS', '4')))
    ap.add_argument('--csmax', type=int, default=0)
    ap.add_argument('--csmin', type=int, default=1, help='first area of the all-diagram size check')
    args = ap.parse_args()
    T0 = time.time()
    raw = json.load(open(os.path.join(args.work, 'classes.json')))
    classes = {int(N): [[(tuple(F[0]), tuple(F[1])) for F in cl] for cl in cls] for N, cls in raw.items()}
    import multiprocessing as mp
    pool = mp.get_context('fork').Pool(args.jobs)

    # ---------------------------------------------------------------- only if
    pairs = [(X, Y) for N in sorted(classes) for cl in classes[N] for X in cl for Y in cl]
    lens = Counter()
    for L in pool.imap_unordered(check_pair, pairs, chunksize=8):
        lens[L] += 1
    say = print
    say('PASS (only if): %d ordered pairs in %d nonrotation classes have explicit common presentations, '
        'recomposed literally on both sides; presentation lengths %s'
        % (len(pairs), sum(len(v) for v in classes.values()), dict(sorted(lens.items()))), flush=True)

    # ---------------------------------------------------------------- if (factor reversal of every chart)
    nrev = 0
    clsets = {}
    for N in classes:
        for cl in classes[N]:
            S = frozenset(C.cells(F) for F in cl)
            for F in cl:
                clsets[C.cells(F)] = S
    for Fc, S in clsets.items():
        for (D, E, B, T, case, v, q) in K.charts(Fc):
            Er, Br, Tr, cr, vr = K.rotate_mark(E, B, T, case, v)
            for R in (K.compose(K.rotate(D), E, B, T, case, v), K.compose(D, Er, Br, Tr, cr, vr),
                      K.compose(K.rotate(D), Er, Br, Tr, cr, vr)):
                assert R in S, 'a factor reversal leaves the class'
                nrev += 1
    say('PASS (if, consistency): all %d factor reversals of all charts of all members lie in the member\'s class'
        % nrev, flush=True)

    # ---------------------------------------------------------------- class size, census members
    items = [(F, len(cl), cl) for N in classes for cl in classes[N] for F in cl]
    res = {}
    for out in pool.imap_unordered(size_check, items, chunksize=4):
        res[out[0]] = out
    say('TABLE  N | members | irreducible factorizations | classes of size 4 with r = 2 | size 8 with r = 3 | '
        'longest factorization')
    for N in sorted(classes):
        if not classes[N]:
            continue
        nf = c4 = c8 = 0
        longest = 0
        for cl in classes[N]:
            size = len(cl)
            for F in cl:
                _, nfac, rs, rsm, gen_ok, gen_eq, mx = res[F]
                assert gen_ok, ('a reversal variant leaves the class', C.fmt(F))
                assert gen_eq, ('the variants of an irreducible factorization are not the class', C.fmt(F))
                assert len(rs) == 1 and 2 ** rs[0] == size, ('class size is not 2^r', C.fmt(F), rs, size)
                assert rsm == rs, ('marked and unmarked symmetry counts differ', C.fmt(F))
                nf += nfac
                longest = max(longest, mx)
            c4 += size == 4
            c8 += size == 8
        row = (sum(len(c) for c in classes[N]), nf, c4, c8, longest)
        say('TABLE %2d | %s' % (N, ' | '.join(map(str, row))), flush=True)
        if N in EXPECTED:
            assert tuple(EXPECTED[N]) == row, ('published table row differs', N)
    say('PASS (size, nonrotation classes): every member of every nonrotation class has |class| = 2^r for every '
        'irreducible factorization, r is independent of the factorization, and the reversal variants of every '
        'irreducible factorization are exactly the class')

    # ---------------------------------------------------------------- class size, every diagram of <= csmax cells
    if args.csmax:
        member_of = {}
        for N in classes:
            for cl in classes[N]:
                for F in cl:
                    member_of[F] = cl
        t = time.time()
        ntot = nred = 0
        for N in range(args.csmin, args.csmax + 1):
            t1 = time.time()
            nN = rN = 0
            for out in pool.imap_unordered(cs_chunk, cs_items(N, member_of), chunksize=1):
                for prof, ok, red in out:
                    assert ok, ('class size clause fails', C.fmt(prof))
                    nN += 1
                    rN += red
            ntot += nN
            nred += rN
            say('  size clause, area %d: %d diagrams, %d with a proper chart (%.0fs)' % (N, nN, rN, time.time() - t1),
                flush=True)
        say('PASS (size, all diagrams): every connected diagram of %d to %d cells (%d diagrams, %d with a proper '
            'chart) satisfies |[F]| = 2^r for all its irreducible factorizations, and the reversal variants of each '
            'irreducible factorization are exactly its class (%.0fs)' % (args.csmin, args.csmax, ntot, nred, time.time() - t))
    pool.close()
    pool.join()
    say('ALL PASS (%.0fs)' % (time.time() - T0))


if __name__ == '__main__':
    main()
