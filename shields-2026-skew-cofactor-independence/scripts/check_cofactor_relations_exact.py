"""v-CA: thm:cofactor-relations of skew-cofactor-independence, tested exactly.

Paper section `sec:cofactors` (Linear relations among cofactors).

For every normalized dense core (a1=N, b_n=0, a_n > b_1) of order n with N <= Nmax(n):
  * exact rank over Q of the n^2 signed cofactors (full matrix, NOT grouped by label);
    nonsymmetric -> must be n^2; symmetric -> must be n(n+1)/2 and the relation space must equal
    span{e_ij - e_{n+1-j,n+1-i}} (each generator an exact identity D_ij == D_{n+1-j,n+1-i}, and nullity n(n-1)/2).
  * proof steps, checked exactly on every core:
    (P1) private derivative  dD_ij/dh_N = (-1)^{n-1} D^R_{i-1,j}  (i>1, j<n), zero on row 1 / column n;
    (P2) lem:boundary-pair: a_i+b_j=N, i>1, j<n  =>  D_1j, D_in not proportional (rank 2);
    (P3) R=R* branch: after rotation to u<v: h_{a2} private at (2,n), Q nonsymmetric, and
         dD_ij/dh_{a2} = +-D^Q (exact) for i!=2, j!=n;
    (P4) symmetric clause: max-square monomial of each S-minor (i<=j) unique, coefficient +-1, equal to the
         printed leader (eq:symmetric-leader), and the n(n+1)/2 leaders distinct.
Controls (must fire):
    (K1) symmetric cores violate the nonsymmetric clause (rank < n^2);
    (K2) connected NON-dense nonsymmetric cores (a_n <= b_1) with rank < n^2 exist;
    (K3) the wrong involution (i,j)->(j,i) is not a relation on some symmetric core;
    (K4) a corrupted derivative sign in (P1) is detected.
usage: check_cofactor_relations_exact.py n Nmax [ctrlNmax]
"""
import sys
import time
from _cofactor_lib import cofactors, rank_of, relation_space, is_symmetric, dense_cores, connected_cores, det_poly


def deriv(P, x):
    """d/dh_x of P (dict)."""
    out = {}
    for k, v in P.items():
        c = k.count(x)
        if c:
            l = list(k)
            l.remove(x)
            kk = tuple(l)
            out[kk] = out.get(kk, 0) + c * v
    return {k: v for k, v in out.items() if v}


def neg(P, s):
    return {k: s * v for k, v in P.items()} if s != 1 else P


def rotate(A, B):
    N = A[0]
    n = len(A)
    return tuple(N - B[n - 1 - i] for i in range(n)), tuple(N - A[n - 1 - i] for i in range(n))


def main():
    n = int(sys.argv[1])
    Nmax = int(sys.argv[2])
    cN = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    t0 = time.time()
    st = dict(cores=0, nonsym=0, sym=0, fail_rank=0, fail_symrel=0, P1=0, P1fail=0, P2pairs=0, P2fail=0,
              RsymBranch=0, P3fail=0, P4fail=0, K1=0, K3=0, K4=0)
    lastN = None
    for A, B in dense_cores(n, Nmax):
        if A[0] != lastN:
            if lastN is not None:
                print(f"PROGRESS n={n} N={lastN} done cores={st['cores']} t={time.time()-t0:.0f}s", flush=True)
            lastN = A[0]
        st['cores'] += 1
        N = A[0]
        D = cofactors(A, B)
        flat = [D[i][j] for i in range(n) for j in range(n)]
        r = rank_of(flat)
        sym = is_symmetric(A, B)
        if sym:
            st['sym'] += 1
            if r != n * (n + 1) // 2:
                st['fail_rank'] += 1
                print("FAIL symrank", A, B, r)
            if r < n * n:
                st['K1'] += 1
            ok = all(D[i][j] == D[n - 1 - j][n - 1 - i] for i in range(n) for j in range(n))
            if not ok:
                st['fail_symrel'] += 1
                print("FAIL symrel", A, B)
            if any(D[i][j] != D[j][i] for i in range(n) for j in range(n)):
                st['K3'] += 1
            # P4: leaders from S_{ij}=h_{a_i+a_j-N}
            d = [2 * A[i] - N for i in range(n)]
            e = [A[i] + A[i + 1] - N for i in range(n - 1)]
            leaders = set()
            for i in range(n):
                for j in range(i, n):
                    rows = [A[r] for r in range(n) if r != i]
                    cols = [N - A[c] for c in range(n) if c != j]  # S_{rc} = h_{a_r - (N - a_c)}
                    P = det_poly(rows, cols)
                    sq = {k: sum(x * x for x in k) for k in P}
                    mx = max(sq.values())
                    top = [k for k in P if sq[k] == mx]
                    pred = tuple(sorted(d[:i] + e[i:j] + d[j + 1:]))
                    if len(top) != 1 or abs(P[top[0]]) != 1 or top[0] != pred:
                        st['P4fail'] += 1
                        print("FAIL P4", A, i, j, top, pred)
                    leaders.add(top[0])
            if len(leaders) != n * (n + 1) // 2:
                st['P4fail'] += 1
                print("FAIL P4 distinct", A)
        else:
            st['nonsym'] += 1
            if r != n * n:
                st['fail_rank'] += 1
                print("FAIL rank", A, B, r)
            # P2
            for i in range(1, n):
                for j in range(n - 1):
                    if A[i] + B[j] == N:
                        st['P2pairs'] += 1
                        if rank_of([D[0][j], D[i][n - 1]]) != 2:
                            st['P2fail'] += 1
                            print("FAIL P2", A, B, i, j)
            # P3: R symmetric branch
            if n >= 3:
                R = (A[1:], B[:-1])
                if is_symmetric(tuple(x - B[-2] for x in R[0]), tuple(x - B[-2] for x in R[1])):
                    st['RsymBranch'] += 1
                    AA, BB = A, B
                    u, v = N - A[1], B[-2]
                    if u == v:
                        st['P3fail'] += 1
                        print("FAIL P3 u==v", A, B)
                    if u > v:
                        AA, BB = rotate(A, B)
                    u, v = N - AA[1], BB[-2]
                    a2 = AA[1]
                    sites = [(i, j) for i in range(n) for j in range(n) if AA[i] - BB[j] == a2]
                    Qc = (tuple(x for k, x in enumerate(AA) if k != 1), BB[:-1])
                    Qn = (tuple(x - BB[-2] for x in Qc[0]), tuple(x - BB[-2] for x in Qc[1]))
                    if sites != [(1, n - 1)] or not u < v or is_symmetric(*Qn):
                        st['P3fail'] += 1
                        print("FAIL P3", A, B, sites, u, v)
                    DD = cofactors(AA, BB)
                    DQ = cofactors(*Qc)
                    for i in range(n):
                        for j in range(n):
                            g = deriv(DD[i][j], a2)
                            if i == 1 or j == n - 1:
                                if g:
                                    st['P3fail'] += 1
                                continue
                            ii = 0 if i == 0 else i - 1
                            if not (g == DQ[ii][j] or g == neg(DQ[ii][j], -1)):
                                st['P3fail'] += 1
                                print("FAIL P3 deriv", A, B, i, j)
        # P1 (all dense cores, n>=3; also n=2)
        if n >= 2:
            R = (A[1:], B[:-1])
            DR = cofactors(*R) if n >= 2 else None
            sgn = -1 if (n - 1) % 2 else 1
            for i in range(n):
                for j in range(n):
                    g = deriv(D[i][j], N)
                    st['P1'] += 1
                    if i == 0 or j == n - 1:
                        if g:
                            st['P1fail'] += 1
                            print("FAIL P1 boundary", A, B, i, j)
                    else:
                        want = neg(DR[i - 1][j], sgn)
                        if g != want:
                            st['P1fail'] += 1
                            print("FAIL P1", A, B, i, j)
                        if want and g == neg(DR[i - 1][j], -sgn):
                            pass
                        elif want:
                            st['K4'] += 1  # corrupted sign is detected
    print(f"PROGRESS n={n} N={lastN} done cores={st['cores']} t={time.time()-t0:.0f}s", flush=True)
    # K2 control: connected non-dense nonsymmetric
    k2 = k2tot = 0
    zf = zftot = 0
    ex = exzf = None
    if cN:
        for A, B in connected_cores(n, cN):
            if is_symmetric(A, B):
                continue
            k2tot += 1
            D = cofactors(A, B)
            zfree = not (set(A) & set(B))
            zftot += zfree
            if rank_of([D[i][j] for i in range(n) for j in range(n)]) < n * n:
                k2 += 1
                if ex is None:
                    ex = (A, B)
                if zfree:
                    zf += 1
                    if exzf is None:
                        exzf = (A, B)
    print(f"RESULT n={n} Nmax={Nmax} {st}")
    print(f"CONTROL K2 n={n} nondense-connected-nonsym N<={cN}: rank-deficient {k2}/{k2tot} example {ex}; of which zero-free (A,B disjoint, some negative index): {zf}/{zftot} example {exzf}")
    assert st['cores'] > 0 and st['sym'] > 0 and st['nonsym'] > 0, 'empty enumeration'
    assert st['fail_rank'] == st['fail_symrel'] == st['P1fail'] == st['P2fail'] == st['P3fail'] == st['P4fail'] == 0, st
    assert st['P1'] > 0, st
    if n >= 3:
        assert st['P2pairs'] > 0, st
    assert st['K1'] > 0 and st['K3'] > 0 and st['K4'] > 0, st
    if n >= 3:
        assert st['RsymBranch'] > 0, st
    if cN and n >= 4:
        # connected non-dense nonsymmetric cores with deficient rank first occur at order 4
        assert k2 > 0, 'control K2 did not fire'
    print(f"TIME {time.time()-t0:.1f}s")
    print("ALL PASS")


if __name__ == "__main__":
    main()
