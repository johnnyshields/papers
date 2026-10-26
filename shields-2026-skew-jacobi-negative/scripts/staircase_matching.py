"""Exact matching search for five-row thick upper Hessenberg profiles.

All feasibility decisions use rational Fourier--Motzkin elimination.  Reaching
its size limit raises; no floating-point solver is available.
"""
import itertools
import time
from fractions import Fraction
from collections import Counter
K=5
NV=9
_bij_cache={}
_exact_cache={}
NODES=[0]
FM_CALLS=[0]
DEPTH=Counter()
EARLY={"classifier":None,"seen":set(),"cut":0}

def var(i):
    v = [0] * (NV + 1)
    v[i] = 1
    return tuple(v)


def add(f, g):
    return tuple(x + y for x, y in zip(f, g))


def sub(f, g):
    return tuple(x - y for x, y in zip(f, g))


def sym_monomials(rows, zs):
    k = len(rows)
    out = []
    for S in range(1 << (k - 1)):
        Sset = [i for i in range(k - 1) if S >> i & 1]
        entries = [zs[i] for i in Sset]
        i = 0
        while i < k:
            j = i
            w = rows[i]
            while j in Sset:
                w = sub(add(w, rows[j + 1]), zs[j])
                j += 1
            entries.append(w)
            i = j + 1
        out.append((tuple(Sset), (-1) ** len(Sset), entries))
    return out


def domain(rows, zs):
    k = len(rows)
    out = list(zs)
    for i in range(k):
        f = rows[i]
        if i >= 1:
            f = sub(f, zs[i - 1])
        if i <= k - 2:
            f = sub(f, zs[i])
        out.append(f)
    return out


def bijection_systems(ent_plus, ent_minus, ineqs):
    ck = (tuple(ent_plus), tuple(ent_minus))
    if ck in _bij_cache:
        return _bij_cache[ck]
    seen = set()
    out = []
    k = len(ent_plus)
    for perm in itertools.permutations(range(k)):
        eqs = tuple(sorted(set(sub(ent_plus[i], ent_minus[perm[i]]) for i in range(k))))
        if eqs in seen:
            continue
        seen.add(eqs)
        if any(not any(e[:NV]) and e[NV] != 0 for e in eqs):
            continue
        if all(feasible([e], ineqs) for e in eqs) and feasible(list(eqs), ineqs):
            out.append(eqs)
    _bij_cache[ck] = out
    return out


def matchings(plus, minus, ineqs, eqs, acc, deadline):
    """Every perfect matching's equation space, with two sound cuts: a
    partial space already classified (identity / reversal / family) keeps
    that verdict on every sub-space, so it is recorded and not refined; and a
    (space, remaining items) state reached before is not re-explored."""
    if time.time() > deadline:
        raise TimeoutError
    NODES[0] += 1
    DEPTH[len(minus)] += 1
    R = rref(eqs)
    if not plus:
        acc.add(R)
        return
    cl = EARLY["classifier"]
    if cl is not None and eqs:
        kind = cl(R)
        if kind is not None:
            acc.add(R)
            EARLY["cut"] += 1
            return
    state = (R, tuple(sorted((it[0], it[1]) for it in plus)), tuple(sorted((it[0], it[1]) for it in minus)))
    if state in EARLY["seen"]:
        return
    EARLY["seen"].add(state)
    p = plus[0]
    for kk, m in enumerate(minus):
        for sysk in bijection_systems(p[2], m[2], ineqs):
            new = eqs + list(sysk)
            if feasible(new, ineqs):
                matchings(plus[1:], minus[:kk] + minus[kk + 1:], ineqs, new, acc, deadline)


def rref(rows):
    M = [[Fraction(x) for x in r] for r in rows if any(r)]
    r0 = 0
    col = 0
    while r0 < len(M) and col < NV + 1:
        piv = next((i for i in range(r0, len(M)) if M[i][col] != 0), None)
        if piv is None:
            col += 1
            continue
        M[r0], M[piv] = M[piv], M[r0]
        pv = M[r0][col]
        M[r0] = [x / pv for x in M[r0]]
        for i in range(len(M)):
            if i != r0 and M[i][col] != 0:
                f = M[i][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[r0])]
        r0 += 1
        col += 1
    return tuple(tuple(r) for r in M[:r0])


def implied(R, f):
    return len(rref(list(R) + [f])) == len(R)


def eq_mod(R, u, v):
    return implied(R, sub(u, v))


def classify(R, rows, zs, trows, tzs, fam_forms):
    coords = list(rows) + list(zs)
    tcoords = list(trows) + list(tzs)
    if all(eq_mod(R, a, b) for a, b in zip(tcoords, coords)):
        return "identity"
    rc = list(reversed(rows)) + list(reversed(zs))
    if all(eq_mod(R, a, b) for a, b in zip(tcoords, rc)):
        return "reversal"
    for conds, members in fam_forms:
        if all(implied(R, c) for c in conds):
            for mem in members:
                if all(eq_mod(R, a, b) for a, b in zip(tcoords, mem)):
                    return "family"
    return None


def family_templates():
    """Each family as a function of parameter forms returning its four
    members [(rows, zs)]; parameters are linear forms."""
    def A1(p, m, z):
        mpz = sub(add(m, p), z)
        F = ([p, m, m, m, mpz], [z, z, z, p])
        H = ([p, m, mpz, m, m], [z, p, z, z])
        return [F, H, (F[0][::-1], F[1][::-1]), (H[0][::-1], H[1][::-1])]

    def A2(p, m, z):
        mpz = sub(add(m, p), z)
        F = ([p, m, m, mpz, mpz], [z, z, p, p])
        H = ([p, m, mpz, mpz, m], [z, p, p, z])
        return [F, H, (F[0][::-1], F[1][::-1]), (H[0][::-1], H[1][::-1])]

    def B(p, m, z, w):
        pmw = sub(add(p, m), w)
        F = ([p, pmw, m, p, m], [z, z, w, z])
        H = ([p, m, p, pmw, m], [z, w, z, z])
        return [F, H, (F[0][::-1], F[1][::-1]), (H[0][::-1], H[1][::-1])]
    return [("A1", A1, 3), ("A2", A2, 3), ("B", B, 4)]


def family_forms_sym(rows, zs):
    """[(conditions, [member vectors])]: for every family and every way F can
    be one of its members, the linear conditions on F's coordinates and the
    four members written in F's coordinates."""
    coords = list(rows) + list(zs)
    out = []
    for name, tmpl, npar in family_templates():
        # parameters as unit vectors in a parameter space
        units = []
        for t in range(npar):
            u = [0] * (NV + 1)
            u[t] = 1          # borrow the first npar slots for parameter symbols
            units.append(tuple(u))
        members_sym = tmpl(*units)
        for j, (mr, mz) in enumerate(members_sym):
            vec = mr + mz
            # read each parameter off a coordinate where the member is that bare parameter
            param_forms = []
            ok = True
            for t in range(npar):
                pos = next((i for i, f in enumerate(vec) if f == units[t]), None)
                if pos is None:
                    ok = False
                    break
                param_forms.append(coords[pos])
            if not ok:
                continue
            members = tmpl(*param_forms)
            me = members[j][0] + members[j][1]
            conds = [sub(a, b) for a, b in zip(me, coords)]
            out.append((conds, [m[0] + m[1] for m in members]))
    return out


def perm_list():
    out = []
    for rp in itertools.permutations(range(1, K)):
        for zp in itertools.permutations(range(1, K - 1)):
            if rp == tuple(range(1, K)) and zp == tuple(range(1, K - 1)):
                continue
            out.append(((0,) + rp, (0,) + zp))
    return out


def strata():
    """[(name, extra inequalities (forms >= 1), extra equalities, permutations)]"""
    rows = [var(i) for i in range(K)]
    zs = [var(K + i) for i in range(K - 1)]

    def w(rs, zz):
        f = rs[0]
        for r, z in zip(rs[1:], zz):
            f = sub(add(f, r), z)
        return f
    w1234 = w(rows[:4], zs[:3])
    w2345 = w(rows[1:], zs[1:])
    w345 = w(rows[2:], zs[2:])
    g2 = sub(w2345, w1234)
    S1 = [((0,) + rp + (4,), (0,) + zp + (3,)) for rp in itertools.permutations((1, 2, 3))
          for zp in itertools.permutations((1, 2))]
    S1 = [t for t in S1 if t != ((0, 1, 2, 3, 4), (0, 1, 2, 3))]
    S2 = [((0, 1) + rp, (0, 1) + zp) for rp in itertools.permutations((2, 3, 4))
          for zp in itertools.permutations((2, 3))]
    S2 = [t for t in S2 if t != ((0, 1, 2, 3, 4), (0, 1, 2, 3))]
    return [
        ("S1", [g2, sub(w1234, w345)], [], S1),
        ("S2", [g2, sub(w345, w1234)], [], S2),
        ("S3", [g2], [sub(w1234, w345)], perm_list()),
        ("S4", [], [sub(w1234, w2345)], perm_list()),
    ]


def fm_feasible(ineqs):
    """Fourier-Motzkin: is {f >= 0} feasible over the reals?  ineqs are tuples
    of length NV+1 over Fractions with constant last; f >= 0 means
    sum c_i x_i + const >= 0."""
    FM_CALLS[0] += 1
    cur = [tuple(f) for f in ineqs]
    for v in range(NV):
        pos = [f for f in cur if f[v] > 0]
        neg = [f for f in cur if f[v] < 0]
        zero = [f for f in cur if f[v] == 0]
        new = list(zero)
        for fp in pos:
            for fn in neg:
                # eliminate v: fp/fp[v] + fn/(-fn[v])
                a, b = fp[v], -fn[v]
                g = tuple(x * b + y * a for x, y in zip(fp, fn))
                new.append(g)
        # drop duplicates and obviously redundant copies
        cur = list({f for f in new})
        for f in cur:
            if all(c == 0 for c in f[:NV]) and f[NV] < 0:
                return False
        if len(cur) > 4000:
            raise RuntimeError("Exact elimination size limit; proof incomplete")
    return all(not (all(c == 0 for c in f[:NV]) and f[NV] < 0) for f in cur)


def feasible_exact(eqs, ineqs):
    R = rref(list(eqs))
    key = (R, tuple(ineqs))
    if key in _exact_cache:
        return _exact_cache[key]
    for r in R:
        if all(c == 0 for c in r[:NV]) and r[NV] != 0:
            _exact_cache[key] = False
            return False
    # substitute pivots into the inequalities (f >= 1  ->  f - 1 >= 0)
    piv = {}
    for r in R:
        p = next(i for i in range(NV) if r[i] != 0)
        piv[p] = r
    red = []
    for f in ineqs:
        g = [Fraction(x) for x in f]
        g[NV] -= 1
        for p, r in piv.items():
            if g[p] != 0:
                c = g[p]
                g = [x - c * y for x, y in zip(g, r)]
        if all(c == 0 for c in g[:NV]):
            if g[NV] < 0:
                _exact_cache[key] = False
                return False
            continue
        red.append(tuple(g))
    # quick antiparallel check before FM
    seen = {}
    for g in red:
        keyv = tuple(g[:NV])
        seen.setdefault(keyv, g)
    for g in red:
        negk = tuple(-c for c in g[:NV])
        if negk in seen:
            h = seen[negk]
            if g[NV] + h[NV] < 0:
                _exact_cache[key] = False
                return False
    res = fm_feasible(red)
    _exact_cache[key] = res
    return res


feasible = feasible_exact
