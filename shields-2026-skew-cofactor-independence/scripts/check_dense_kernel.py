#!/usr/bin/env python3
"""Base unit kernel of dense cores and its arithmetic subspace, tested exactly.

Paper sections `sec:dilation` (Integral dilation), `sec:restoration` (Common beta entries and first variations).
Target: the containment stated after `eq:endpoint-modulus` (words phi(z mod g(C)) with phi(r)+phi(N-r)=0
lie in K(C)), which the dilation theorem `thm:dilation` inherits.  The paper proves only that containment;
equality on nonsymmetric dense cores is a separate result of a companion draft and is checked here as
finite evidence; both are asserted, and only the containment is the paper's claim.

Statement tested (equality form): for a dense (min A > max B) nonsymmetric normalized core C=(A,B),
N=max A, min B=0, the rational kernel of z -> U_z on the available sites
Omega_C = {1..N-1} minus (A u B) is exactly the set of restrictions of words
phi(z mod g) with phi(r)+phi(N-r)=0, g = gcd({N-a} u B).

U_z = sum_{a_i>z>b_j} D_ij h_{a_i-z} h_{z-b_j}, D_ij the signed cofactors of (h_{a_i-b_j}).
Everything is exact: polynomials are dicts monomial->int (each determinant term is one monomial),
ranks are flint fmpz_mat ranks.  Kernel = predicted is certified by
  (i) every predicted basis vector is an exact relation (sum is the zero polynomial), and
  (ii) rank(U) = |Omega| - dim(predicted restricted space).
Firing controls: symmetric cores (predicted nonsymmetric formula must FAIL), and the formula
with g replaced by 2g or by g/2... (must fail somewhere), and a single-site vector (not a relation).
"""
import sys, itertools, math, time
from math import gcd
from functools import reduce
import flint

def det_terms(rows, cols):
    """determinant of (h_{r-c}) as dict monomial->coef; h_0=1, negative index -> 0."""
    n = len(rows)
    out = {}
    for perm in itertools.permutations(range(n)):
        idx = []
        ok = True
        for i, j in enumerate(perm):
            d = rows[i] - cols[j]
            if d < 0:
                ok = False; break
            if d > 0:
                idx.append(d)
        if not ok:
            continue
        # sign
        s = 1
        p = list(perm)
        for a in range(n):
            while p[a] != a:
                b = p[a]; p[a], p[b] = p[b], p[a]; s = -s
        m = tuple(sorted(idx))
        out[m] = out.get(m, 0) + s
    return {m: c for m, c in out.items() if c}

def cofactors(A, B):
    k = len(A)
    D = {}
    for i in range(k):
        for j in range(k):
            r = [A[t] for t in range(k) if t != i]
            c = [B[t] for t in range(k) if t != j]
            sgn = -1 if (i + j) % 2 else 1
            D[i, j] = {m: sgn * v for m, v in det_terms(r, c).items()} if k > 1 else {(): 1}
    return D

def units(A, B, sites):
    k = len(A)
    D = cofactors(A, B)
    U = {}
    for z in sites:
        poly = {}
        for i in range(k):
            if not A[i] > z: continue
            for j in range(k):
                if not z > B[j]: continue
                ext = (A[i] - z, z - B[j])
                for m, v in D[i, j].items():
                    mm = tuple(sorted(m + ext))
                    poly[mm] = poly.get(mm, 0) + v
        U[z] = {m: v for m, v in poly.items() if v}
    return U

def rank_of(U, sites):
    mons = sorted({m for z in sites for m in U[z]})
    if not mons or not sites:
        return 0
    idx = {m: t for t, m in enumerate(mons)}
    M = flint.fmpz_mat(len(mons), len(sites))
    for c, z in enumerate(sites):
        for m, v in U[z].items():
            M[idx[m], c] = v
    return M.rank()

def is_relation(U, vec):
    acc = {}
    for z, c in vec.items():
        if c == 0: continue
        for m, v in U[z].items():
            acc[m] = acc.get(m, 0) + c * v
    return all(v == 0 for v in acc.values())

def predicted_basis(N, g, sites):
    """basis of {phi(z mod g)|_sites : phi(r)+phi(N-r)=0}; returns list of dict vectors."""
    # orbits of r -> N-r mod g
    seen = set(); basis = []
    for r in range(g):
        if r in seen: continue
        s = (N - r) % g
        seen.add(r); seen.add(s)
        if s == r:
            continue  # phi(r) = 0 forced
        vec = {z: (1 if z % g == r else -1 if z % g == s else 0) for z in sites}
        if any(vec.values()):
            basis.append(vec)
    return basis

def vec_rank(vecs, sites):
    if not vecs: return 0
    M = flint.fmpz_mat(len(vecs), len(sites))
    for a, v in enumerate(vecs):
        for c, z in enumerate(sites):
            M[a, c] = v[z]
    return M.rank()

def check_core(A, B, g_override=None):
    """A, B decreasing lists, B[-1]=0, A[0]=N.  Returns (ok, nullity, preddim)."""
    N = A[0]
    k = len(A)
    S = set(A) | set(B)
    sites = [z for z in range(1, N) if z not in S]
    U = units(A, B, sites)
    rk = rank_of(U, sites)
    null = len(sites) - rk
    g = reduce(gcd, [N - a for a in A] + list(B)) if g_override is None else g_override
    basis = predicted_basis(N, g, sites)
    pd = vec_rank(basis, sites)
    rel = all(is_relation(U, v) for v in basis)
    return (rel and pd == null), null, pd, rel, U, sites

def dense_cores(k, Nmax):
    for N in range(2 * k - 1, Nmax + 1):
        for restA in itertools.combinations(range(1, N), k - 1):
            A = (N,) + tuple(sorted(restA, reverse=True))
            amin = A[-1]
            for restB in itertools.combinations(range(1, amin), k - 1):
                B = tuple(sorted(restB, reverse=True)) + (0,)
                yield A, B

def symmetric(A, B):
    N = A[0]; k = len(A)
    return all(A[i] + B[k - 1 - i] == N for i in range(k))

def main():
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s)
    P('=== run', time.strftime('%Y-%m-%d %H:%M:%S'), 'args', sys.argv[1:])
    ranges = {2: int(sys.argv[1]) if len(sys.argv) > 1 else 24,
              3: int(sys.argv[2]) if len(sys.argv) > 2 else 18,
              4: int(sys.argv[3]) if len(sys.argv) > 3 else 15,
              5: int(sys.argv[4]) if len(sys.argv) > 4 else 14}
    tot = 0; fails = 0; nz = 0; symfire = 0; symtot = 0; maxnull = 0
    wrongg_fire = 0; wrongg_tot = 0; single_fire = 0; single_tot = 0
    for k, Nmax in ranges.items():
        t0 = time.time(); cnt = 0
        for A, B in dense_cores(k, Nmax):
            sym = symmetric(A, B)
            ok, null, pd, rel, U, sites = check_core(A, B)
            if sym:
                symtot += 1
                if not ok: symfire += 1
                continue
            tot += 1; cnt += 1
            if not ok:
                fails += 1
                if fails <= 20: P('FAIL', k, A, B, 'null', null, 'pred', pd, 'rel', rel)
            if null:
                nz += 1; maxnull = max(maxnull, null)
                # control: wrong modulus 2g must not reproduce (when it changes the space)
                g = reduce(gcd, [A[0] - a for a in A] + list(B))
                wrongg_tot += 1
                ok2 = check_core(A, B, g_override=2 * g)[0]
                if not ok2: wrongg_fire += 1
                # control: a single-site vector is not a relation
                single_tot += 1
                if not is_relation(U, {sites[0]: 1}): single_fire += 1
        P(f'order {k} N<={Nmax}: nonsym cores so far {tot}, this order {cnt}, fails {fails}, nonzero kernels {nz}, maxnull {maxnull}, {time.time()-t0:.1f}s')
    P(f'SUMMARY nonsymmetric dense cores {tot}; FAILURES {fails}; nonzero kernels {nz} (max nullity {maxnull})')
    P(f'CONTROL symmetric cores: nonsym formula fails on {symfire}/{symtot} (must be >0)')
    P(f'CONTROL modulus 2g: fails on {wrongg_fire}/{wrongg_tot} nonzero-kernel cores (must be >0)')
    P(f'CONTROL single-site vector: non-relation on {single_fire}/{single_tot}')
    assert fails == 0 and symfire > 0 and wrongg_fire > 0 and tot > 0 and nz > 0, 'NOT PASS'
    P('ALL PASS')


# ---------------------------------------------------------------- dilated cores
def profiles(area, nrows):
    """connected profiles (rows top..bottom, gaps s_i = overlap-1) of given area and row count."""
    def comps(total, parts, lo=1):
        if parts == 1:
            if total >= lo: yield (total,)
            return
        for f in range(lo, total - lo * (parts - 1) + 1):
            for rest in comps(total - f, parts - 1, lo):
                yield (f,) + rest
    for rows in comps(area, nrows):
        rng = [range(0, min(rows[i], rows[i + 1])) for i in range(nrows - 1)]
        for gaps in itertools.product(*rng):
            yield rows, gaps

def betas_of(rows, gaps):
    n = len(rows)
    x = [0] * n; y = [0] * n
    y[n - 1] = 0; x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)

def main_dilated(maxarea, maxp):
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s)
    P('=== dilated run', time.strftime('%Y-%m-%d %H:%M:%S'), 'maxarea', maxarea, 'maxp', maxp)
    tot = fails = nz = 0; seen = set(); symfire = symtot = 0; maxnull = 0
    for area in range(2, maxarea + 1):
        for n in range(2, area + 1):
            for rows, gaps in profiles(area, n):
                X, Y = betas_of(rows, gaps)
                if X[-1] < Y[0]:
                    continue  # not nonnegative-index
                key = (rows, gaps)
                if key in seen: continue
                seen.add(key); seen.add((rows[::-1], gaps[::-1]))
                sym = (rows[::-1] == rows and gaps[::-1] == gaps)
                for p in range(2, maxp + 1):
                    for w in range(1, p):
                        A = tuple(p * x + w for x in X); B = tuple(p * y for y in Y)
                        ok, null, pd, rel, U, sites = check_core(A, B)
                        if sym:
                            symtot += 1; symfire += (not ok); continue
                        tot += 1
                        if null: nz += 1; maxnull = max(maxnull, null)
                        if not ok:
                            fails += 1
                            if fails <= 20: P('FAIL', rows, gaps, p, w, null, pd, rel)
        P(f'area<={area}: dilated nonsym panels {tot}, fails {fails}, nonzero kernels {nz}, maxnull {maxnull}; sym panels {symtot} fired {symfire}')
    assert fails == 0 and symfire > 0 and tot > 0, 'NOT PASS'
    P('DILATED ALL PASS')

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'dilated':
        main_dilated(int(sys.argv[2]), int(sys.argv[3]))
    else:
        main()
