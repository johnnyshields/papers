"""Exact substrate for the local skew-Schur equivalence attack.

Standard library only.  Nothing here is numerical: skew Schur functions are
compared through the signed multiset of h-monomials of their Jacobi-Trudi
expansion, which is a faithful invariant.

    s_{lam/mu} = det( h_{lam_i - mu_j - i + j} )_{i,j=1..n},   h_0 = 1, h_{<0} = 0.

Conventions, fixed for the whole attack:

  * partitions descend; row i of lam/mu occupies columns mu_i+1 .. lam_i.
  * D* is the 180-degree rotation.  Always D ~ D*.
  * connected means consecutive rows share at least one column.
  * concat_row(sigma, m)  is  sigma . (m)  -- a length-m row attached to the
    NORTHEAST, meeting the top row of sigma in exactly one column.
  * row_concat(m, tau)    is  (m) . tau    -- the southwest mirror.
  * T(lam/mu) = (lam_2..lam_m)/(mu_1..mu_{m-1})   canonical RSvW peel.
  * L(lam/mu) = lam/(mu_1+1..mu_m+1)              delete leftmost cell of each row;
    lowers every positive adjacent-row overlap by exactly 1.

Running this file reproduces the measurement table in the brief.
"""

from itertools import permutations
from collections import defaultdict
from functools import lru_cache


# ------------------------------------------------------------------ invariant

@lru_cache(None)
def jt_sig(lam, mu):
    """Signed multiset of h-monomials of det(h_{lam_i-mu_j-i+j}).

    Faithful: jt_sig(A) == jt_sig(B)  iff  s_A == s_B."""
    n = len(lam)
    mu = tuple(mu) + (0,) * (n - len(mu))
    out = defaultdict(int)
    for pi in permutations(range(n)):
        vals = []
        ok = True
        for i, j in enumerate(pi):
            v = lam[i] - mu[j] - i + j
            if v < 0:
                ok = False
                break
            if v:
                vals.append(v)
        if not ok:
            continue
        inv = sum(pi[i] > pi[j] for i in range(n) for j in range(i + 1, n))
        out[tuple(sorted(vals, reverse=True))] += -1 if inv % 2 else 1
    return tuple(sorted((k, v) for k, v in out.items() if v))


def equiv(A, B):
    """s_A == s_B, exactly."""
    return jt_sig(*A) == jt_sig(*B)


# --------------------------------------------------------------- shape basics

def cells(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    return {(i, j) for i in range(len(lam)) for j in range(mu[i] + 1, lam[i] + 1)}


def size(sh):
    return len(cells(sh))


def connected(sh):
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    for i in range(len(lam) - 1):
        if min(lam[i], lam[i + 1]) <= max(mu[i], mu[i + 1]):
            return False
    return True


def normalize(sh):
    """Drop empty rows and translate so the last inner part is 0."""
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    keep = [i for i in range(len(lam)) if lam[i] > mu[i]]
    if not keep:
        return ((), ())
    lam = [lam[i] for i in keep]
    mu = [mu[i] for i in keep]
    shift = mu[-1]
    return (tuple(x - shift for x in lam), tuple(x - shift for x in mu))


def rotate(sh):
    """180-degree rotation, back in (lam, mu) form and normalized."""
    C = cells(sh)
    maxi = max(i for i, j in C)
    maxj = max(j for i, j in C)
    R = {(maxi - i, maxj + 1 - j) for i, j in C}
    rows = defaultdict(list)
    for i, j in R:
        rows[i].append(j)
    lam, mu = [], []
    for i in range(max(rows) + 1):
        js = sorted(rows[i])
        assert js == list(range(js[0], js[-1] + 1)), "rotated row is not an interval"
        lam.append(js[-1])
        mu.append(js[0] - 1)
    return normalize((tuple(lam), tuple(mu)))


# ------------------------------------------------------------ caps and erosions

def concat_row(sh, m):
    """sigma . (m): length-m row to the NORTHEAST, one shared column."""
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    L_ = lam[0]
    return ((m + L_ - 1,) + tuple(lam), (L_ - 1,) + tuple(mu))


def row_concat(m, sh):
    """(m) . tau: length-m row to the SOUTHWEST, one shared column."""
    return normalize(rotate(concat_row(rotate(sh), m)))


def T(sh):
    """Canonical RSvW peel."""
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    if len(lam) < 2:
        return ((), ())
    return normalize((tuple(lam[1:]), tuple(mu[:-1])))


def L(sh):
    """Delete the leftmost cell of every row.  None if the result is illegal."""
    lam, mu = sh
    mu = tuple(mu) + (0,) * (len(lam) - len(mu))
    new = (tuple(lam), tuple(m + 1 for m in mu))
    if any(l < m for l, m in zip(new[0], new[1])):
        return None
    return normalize(new)


# ------------------------------------------------------------------ enumeration

def gen_shapes(maxsize, maxrows):
    """Every connected skew shape, normalized, with <= maxsize cells and
    <= maxrows rows.  Built by prepending rows to the top."""
    out = set()

    def rec(lam, mu):
        if lam:
            sh = (tuple(lam), tuple(mu))
            if connected(sh) and 0 < size(sh) <= maxsize:
                out.add(normalize(sh))
        if len(lam) == maxrows:
            return
        lo_l = lam[0] if lam else 1
        for nl in range(lo_l, maxsize + 1):
            lo_m = mu[0] if mu else 0
            for nm in range(lo_m, nl):
                sh = ((nl,) + tuple(lam), (nm,) + tuple(mu))
                if size(sh) > maxsize:
                    continue
                rec(list(sh[0]), list(sh[1]))

    rec([], [])
    return sorted(out)


def double_cap_sweep(maxsize=11, maxrows=5, maxm=6):
    """Every (m, sigma, tau) with (sigma,m) ~ (m,tau); flagged by whether the
    (m+1) equation also holds and by whether tau == sigma*."""
    shapes = [s for s in gen_shapes(maxsize, maxrows) if connected(s)]
    by_size = defaultdict(list)
    for s in shapes:
        by_size[size(s)].append(s)
    rows = []
    for m in range(1, maxm + 1):
        for group in by_size.values():
            cl = {s: jt_sig(*concat_row(s, m)) for s in group}
            cr = {s: jt_sig(*row_concat(m, s)) for s in group}
            cl1 = {s: jt_sig(*concat_row(s, m + 1)) for s in group}
            cr1 = {s: jt_sig(*row_concat(m + 1, s)) for s in group}
            for sg in group:
                rsg = rotate(sg)
                for tu in group:
                    if cl[sg] != cr[tu]:
                        continue
                    rows.append({
                        "m": m, "sigma": sg, "tau": tu,
                        "double": cl1[sg] == cr1[tu],
                        "is_rotation": normalize(tu) == rsg,
                    })
    return rows, shapes


# ------------------------------------------------------------------ named data

D8 = ((4, 4, 3, 3), (3, 2, 1, 0))
E8 = ((4, 4, 4, 2), (3, 2, 1, 0))
D17 = ((7, 7, 6, 6, 5, 5, 2), (6, 5, 4, 3, 2, 1, 0))
E17 = ((7, 7, 6, 6, 6, 4, 2), (6, 5, 4, 3, 2, 1, 0))
Q_D17 = ((4, 3, 3), (2, 1, 0))
Q_E17 = ((4, 3, 2), (1, 1, 0))

# the single-cap-only witness: cap m=1 holds, tau != sigma*, sigma !~ tau
WITNESS_SIGMA = ((2, 1, 1), (0, 0, 0))
WITNESS_TAU = ((2, 2, 1), (1, 0, 0))
WITNESS_M = 1


def _selftest():
    assert equiv(D8, E8) and size(D8) == 8
    assert equiv(D17, E17) and size(D17) == 17
    assert equiv(Q_D17, Q_E17) and rotate(Q_D17) == normalize(Q_E17)
    assert equiv(concat_row(WITNESS_SIGMA, WITNESS_M),
                 row_concat(WITNESS_M, WITNESS_TAU))
    assert not equiv(concat_row(WITNESS_SIGMA, WITNESS_M + 1),
                     row_concat(WITNESS_M + 1, WITNESS_TAU))
    assert normalize(WITNESS_TAU) != rotate(WITNESS_SIGMA)
    assert not equiv(WITNESS_SIGMA, WITNESS_TAU)


if __name__ == "__main__":
    _selftest()
    print("named data: OK")

    rows, shapes = double_cap_sweep(11, 5, 6)
    dbl = [r for r in rows if r["double"]]
    print(f"connected shapes |.|<=11, rows<=5 : {len(shapes)}")
    print(f"single-cap solutions              : {len(rows)}")
    print(f"  of which double-cap             : {len(dbl)}")
    print(f"  single-cap only, tau != sigma*  : "
          f"{sum(1 for r in rows if not r['double'] and not r['is_rotation'])}")
    print(f"  DOUBLE-cap,      tau != sigma*  : "
          f"{sum(1 for r in dbl if not r['is_rotation'])}   <-- must be 0")

    small = [s for s in gen_shapes(10, 5) if connected(s)]
    classes = defaultdict(list)
    for s in small:
        classes[jt_sig(*s)].append(s)
    pairs = [(a, b) for mem in classes.values() if len(mem) > 1
             for i, a in enumerate(mem) for b in mem[i + 1:]]
    sig = lambda sh: None if sh is None or not sh[0] else jt_sig(*sh)
    print(f"\nequivalent pairs |.|<=10          : {len(pairs)}")
    print(f"  not related by rotation         : "
          f"{sum(1 for a, b in pairs if normalize(b) != rotate(a))}")
    print(f"  T fails to preserve ~           : "
          f"{sum(1 for a, b in pairs if sig(T(a)) != sig(T(b)))}")
    print(f"  L fails to preserve ~           : "
          f"{sum(1 for a, b in pairs if sig(L(a)) != sig(L(b)))}")
    print(f"  TL != LT                        : "
          f"{sum(1 for s in small if sig(L(T(s))) != sig(T(L(s)) if L(s) else None))}")
