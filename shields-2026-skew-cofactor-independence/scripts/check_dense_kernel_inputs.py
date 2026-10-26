#!/usr/bin/env python3
"""The two cofactor-independence inputs of edge normalization, tested exactly.

Paper sections `sec:cofactors` (Linear relations among cofactors); `sec:restoration` (Common beta entries and first variations).
(a) thm:cofactor-relations, nonsymmetric clause: the k^2 signed cofactors of a dense core C != C*
    are Q-linearly independent (rank k^2); symmetric clause: rank k(k+1)/2.
(b) prop:symmetric-unit-kernel: for symmetric dense C of order >= 2, K(C) = {lam_z + lam_{N-z} = 0}.
Helpers from check_dense_kernel.  Controls: symmetric cores must have rank < k^2;
the reflection space must FAIL to be the kernel on some nonsymmetric core.
"""
import sys, time, flint
import check_dense_kernel as K

def cof_rank(A, B):
    D = K.cofactors(A, B)
    mons = sorted({m for v in D.values() for m in v})
    idx = {m: t for t, m in enumerate(mons)}
    M = flint.fmpz_mat(len(mons), len(D))
    for c, key in enumerate(sorted(D)):
        for m, v in D[key].items():
            M[idx[m], c] = v
    return M.rank()

def refl_ok(A, B):
    N = A[0]; S = set(A) | set(B)
    sites = [z for z in range(1, N) if z not in S]
    U = K.units(A, B, sites)
    null = len(sites) - K.rank_of(U, sites)
    basis = []
    for z in sites:
        if z < N - z:
            v = {s: 0 for s in sites}; v[z] = 1
            if N - z in v: v[N - z] = -1
            basis.append(v)
        elif z == N - z:
            pass
    pd = K.vec_rank(basis, sites)
    return pd == null and all(K.is_relation(U, v) for v in basis)

def main():
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True)
    P('=== run', time.strftime('%Y-%m-%d %H:%M:%S'), sys.argv[1:])
    rng = {2: 30, 3: 22, 4: 17, 5: 15}
    if len(sys.argv) > 1: rng = dict(zip((2, 3, 4, 5), map(int, sys.argv[1:5])))
    nons = nf = sy = sf = symker = symkerf = ctrl = 0
    for k, Nmax in rng.items():
        for A, B in K.dense_cores(k, Nmax):
            sym = K.symmetric(A, B)
            r = cof_rank(A, B)
            if sym:
                sy += 1
                if r != k * (k + 1) // 2: sf += 1; P('SYM RANK FAIL', A, B, r)
                symker += 1
                if not refl_ok(A, B): symkerf += 1; P('SYM KERNEL FAIL', A, B)
            else:
                nons += 1
                if r != k * k: nf += 1; P('NONSYM RANK FAIL', A, B, r)
                if nons % 50 == 0 and not refl_ok(A, B): ctrl += 1
        P(f'order {k} N<={Nmax}: nonsym {nons} (rank fails {nf}); sym {sy} (rank fails {sf}; kernel fails {symkerf})')
    P(f'CONTROL reflection-kernel formula fails on {ctrl} sampled nonsymmetric cores (must be > 0); symmetric rank < k^2 on all {sy}')
    assert nf == sf == symkerf == 0 and ctrl > 0 and nons > 0 and sy > 0, 'NOT PASS'
    P('ALL PASS')

main()
