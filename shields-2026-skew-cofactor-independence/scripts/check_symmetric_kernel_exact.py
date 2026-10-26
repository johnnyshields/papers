"""v-CA: prop:symmetric-unit-kernel of skew-cofactor-independence, tested exactly.

Paper section `sec:restoration` (Common beta entries and first variations).

For every normalized SYMMETRIC dense core of order n (a1=N, b_j = N - a_{n+1-j}, 2a_n > N), N <= Nmax:
  (T1) U_z == U_{N-z} exactly (polynomial dicts) for every z in Omega_C;
  (T2) rank{U_z : z in Omega} == ceil(|Omega|/2)   (so dim K = floor(|Omega|/2); with T1 => K = reflection space);
  (T3) the representatives {U_z : 2z <= N} are independent (rank = their number);
  proof steps:
  (S1) dU_z/dh_N == 0 for z<u, == (-1)^{n-1} U^{C'}_{z-u} for z>u (z<a_2), C' = (a_{p+1}-u, b_q-u), u=b_{n-1};
  (S2) for z<u:  [h_{N-z}] U_z == h_z D_{1n}  (exact), and every U_{z'} with z<z'<u has all indices < N-z.
Controls (must fire):
  (K1) on NONsymmetric dense cores the reflection formula fails (U_z != U_{N-z} for some z, or rank differs);
  (K2) on symmetric cores the wrong reflection z -> N-1-z is not a symmetry of the units;
  (K3) a wrong sign in (S1) is detected.
usage: check_symmetric_kernel_exact.py n Nmax [ctrl_nonsym_Nmax]
"""
import sys
import time
import itertools
from _cofactor_lib import cofactors, rank_of, is_symmetric, dense_cores, units, pmul_mon


def deriv(P, x):
    out = {}
    for k, v in P.items():
        c = k.count(x)
        if c:
            l = list(k)
            l.remove(x)
            kk = tuple(l)
            out[kk] = out.get(kk, 0) + c * v
    return {k: v for k, v in out.items() if v}


def coeff_lin(P, x):
    """coefficient of h_x (as a polynomial), assuming P linear in h_x."""
    out = {}
    for k, v in P.items():
        c = k.count(x)
        assert c <= 1
        if c:
            l = list(k)
            l.remove(x)
            out[tuple(l)] = out.get(tuple(l), 0) + v
    return {k: v for k, v in out.items() if v}


def sym_cores(n, Nmax):
    for N in range(2 * n - 1 if n > 1 else 2, Nmax + 1):
        lo = N // 2 + 1
        for As in itertools.combinations(range(lo, N), n - 1):
            A = (N,) + tuple(sorted(As, reverse=True))
            B = tuple(N - A[n - 1 - j] for j in range(n))
            assert B[-1] == 0 and A[-1] > B[0]
            yield A, B


def main():
    n = int(sys.argv[1])
    Nmax = int(sys.argv[2])
    cN = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    t0 = time.time()
    st = dict(cores=0, T1fail=0, T2fail=0, T3fail=0, S1checks=0, S1fail=0, S2checks=0, S2fail=0, K2=0, K3=0,
              maxOmega=0, maxdimK=0)
    lastN = None
    for A, B in sym_cores(n, Nmax):
        if A[0] != lastN:
            if lastN is not None:
                print(f"PROGRESS n={n} N={lastN} cores={st['cores']} t={time.time()-t0:.0f}s", flush=True)
            lastN = A[0]
        st['cores'] += 1
        N = A[0]
        D = cofactors(A, B)
        Om, Us = units(A, B, D)
        pos = {z: k for k, z in enumerate(Om)}
        U = dict(zip(Om, Us))
        if any(U[z] != U[N - z] for z in Om):
            st['T1fail'] += 1
            print("FAIL T1", A, B)
        if any((N - 1 - z) in U and U[z] != U[N - 1 - z] for z in Om):
            st['K2'] += 1
        r = rank_of(Us)
        if r != (len(Om) + 1) // 2:
            st['T2fail'] += 1
            print("FAIL T2", A, B, r, len(Om))
        reps = [U[z] for z in Om if 2 * z <= N]
        if rank_of(reps) != len(reps):
            st['T3fail'] += 1
            print("FAIL T3", A, B)
        st['maxOmega'] = max(st['maxOmega'], len(Om))
        st['maxdimK'] = max(st['maxdimK'], len(Om) - r)
        if n >= 2:
            u = B[n - 2]
            assert u == N - A[1] and 0 < 2 * u < N
            Cp = (tuple(a - u for a in A[1:]), tuple(b - u for b in B[:-1]))
            assert is_symmetric(*Cp)
            Omp, Usp = units(*Cp)
            Up = dict(zip(Omp, Usp))
            sgn = -1 if (n - 1) % 2 else 1
            for z in Om:
                if z >= A[1]:
                    continue
                g = deriv(U[z], N)
                st['S1checks'] += 1
                if z < u:
                    if g:
                        st['S1fail'] += 1
                        print("FAIL S1 low", A, z)
                else:
                    want = {k: sgn * v for k, v in Up[z - u].items()}
                    if g != want:
                        st['S1fail'] += 1
                        print("FAIL S1", A, z)
                    if want and g != {k: -v for k, v in want.items()}:
                        st['K3'] += 1
            for z in Om:
                if z >= u:
                    continue
                st['S2checks'] += 1
                c = coeff_lin(U[z], N - z)
                if c != pmul_mon(D[0][n - 1], (z,)) or not c:
                    st['S2fail'] += 1
                    print("FAIL S2", A, z)
                for z2 in Om:
                    if z < z2 < u and any(max(k) >= N - z for k in U[z2] if k):
                        st['S2fail'] += 1
                        print("FAIL S2 order", A, z, z2)
    print(f"PROGRESS n={n} N={lastN} cores={st['cores']} t={time.time()-t0:.0f}s", flush=True)
    # K1 control on nonsymmetric dense cores
    k1 = k1tot = 0
    if cN:
        for A, B in dense_cores(n, cN):
            if is_symmetric(A, B):
                continue
            k1tot += 1
            N = A[0]
            Om, Us = units(A, B)
            U = dict(zip(Om, Us))
            refl_ok = all((N - z) in U and U[z] == U[N - z] for z in Om)
            dim_ok = rank_of(Us) == (len(Om) + 1) // 2
            if not (refl_ok and dim_ok):
                k1 += 1
    print(f"RESULT n={n} Nmax={Nmax} {st}")
    print(f"CONTROL K1 n={n} nonsym dense N<={cN}: reflection formula fails on {k1}/{k1tot}")
    assert st['cores'] > 0, 'empty enumeration'
    assert st['T1fail'] == st['T2fail'] == st['T3fail'] == st['S1fail'] == st['S2fail'] == 0, st
    assert st['S1checks'] > 0 and st['S2checks'] > 0 and st['K2'] > 0 and st['K3'] > 0, st
    if cN:
        assert k1 > 0, 'control K1 did not fire'
    print(f"TIME {time.time()-t0:.1f}s")
    print("ALL PASS")


if __name__ == "__main__":
    main()
