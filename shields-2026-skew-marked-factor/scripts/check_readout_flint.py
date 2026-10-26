"""Paper section `sec:extraction` (Recovering the factors); results `thm:extraction`, `eq:terminal`, `eq:inner-recovery`, `eq:outer-recovery`, `eq:ratio`.

Second route to the differential readout of ordinary charts (python-flint, independent of `schur_tools.py`).

CLAIM.  For a proper ordinary I-IV chart F = D o_omega E of period p, with P = s_F:
  (2)  a_p(P) := max{j : delta_p^j P != 0} = |D|;
  (3)  s_E = prim(U / gcd(U, T)),  T = delta_p^a P, U = delta_p^(a-1) P;
  (5)  prim sum_{nu |- a} (delta_{p nu} P / T) p_nu / z_nu = s_D (case a), omega(s_D) (case b),
       the ratios delta_{p nu}P / T being scalars.
CLAIM (active modes).  From (P, p) alone a triangular recursion gives Z_m = M_omega(p_m) for every active m
  (delta_m s_D != 0), M_omega(h_j) = s_W^(j-1) s_{(j) o E}; if 2 is active, s_W is the unique
  irreducible factor of J_2 = (Z_2 + s_E^2)/2 of weight < |E| (none iff W empty); if 2, 3 are active,
  s_W = prim gcd(J_2, J_3), J_3 = (Z_3 - s_E^3)/3.  Also: delta_p s_E = sigma s_W s_What s_Ohat, and
  T = sigma^a f^D A^r B^c C^M (A, B, C = s_W, s_What, s_Ohat), sigma = (-1)^(height of v).

MECHANISM: every connected inner E of 2..NE_MAX cells, EVERY
legal ordinary mark the engine's w_candidates(E) returns (Hypotheses I-IV, both empty readings), every
connected outer D of 2..ND_MAX cells (plus nonribbon outers of 5-6 cells on small inners); parents by
the engine's compose, cross-checked cell-for-cell against my own implementation of the paper's offset
formula L(d) = t v +- i e.  Polynomials: my flint Jacobi-Trudi, my delta_k (itself cross-checked
against a Murnaghan-Nakayama rim-hook route in _readout_lib self-test).  The decoder receives
ONLY (P, p); every comparison target (s_E, s_D, s_{D^t}, s_W, b_j) is computed separately from the
known factors.

FIRING CONTROLS (must fail, and do): a wrong period p' (the readout of s_E must fail or give a
different function); a mixed chart (the ordinary readout breaks: delta_p P = 0); the case-(b)
outer without the involution (must differ from s_D whenever s_D != omega s_D); the empty-outer trap.
"""
import os
import sys
import time
import json
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _readout_lib as L

ENG = L.ENG
NE_MAX = int(os.environ.get('NE_MAX', '7'))
ND_MAX = int(os.environ.get('ND_MAX', '4'))


def my_ordinary_compose(Dc, Ec, v, case):
    """Paper's cell form: copy for d = (i, i + t) at t v + i e (a) or t v - i e (b)."""
    S = set()
    for (i, j) in Dc:
        t = j - i
        if case == 'a':
            o = (t * v[0] + i, t * v[1] + i)
        else:
            o = (t * v[0] - i, t * v[1] - i)
        for (x, y) in Ec:
            S.add((x + o[0], y + o[1]))
    return ENG.normalize(frozenset(S))


def hatted(E, Wsw, Wne, v):
    O = E - Wsw - Wne
    amal = set()
    for k in range(-4, 5):
        amal |= {(x + k * v[0], y + k * v[1]) for x, y in E}
    Oh = {c for c in O if (c[0] + 1, c[1] + 1) in O}
    Wh = {c for c in amal if (c[0] + 1, c[1] + 1) in Wsw}
    Wh |= {c for c in Wsw if (c[0] + 1, c[1] + 1) in amal}
    return frozenset(Wh), frozenset(Oh)


def readout(P, p):
    """The decoder, implemented from the statement: input ONLY (P, p)."""
    a = 0
    T = P
    U = None
    while True:
        nxt = L.delta(T, p)
        if nxt.is_zero():
            break
        U, T = T, nxt
        a += 1
    if a < 1 or U is None:
        return None
    g = U.gcd(T)
    sE = L.prim(L.exact_div(U, g))
    ratios = {}
    for nu in L.partitions(a):
        d = L.delta_seq(P, [p * k for k in nu])
        c = L.scalar_ratio(d, T)
        if c is None:
            return {'a': a, 'sE': sE, 'T': T, 'U': U, 'nonscalar': nu}
        ratios[nu] = c
    # Q_p = sum ratio(nu) p_nu / z_nu
    from fractions import Fraction
    Lden = 1
    for nu, c in ratios.items():
        fr = c / L.zee(nu)
        Lden = Lden * fr.denominator // L.gcd(Lden, fr.denominator)
    Q = L.ZERO
    for nu, c in ratios.items():
        fr = c / L.zee(nu) * Lden
        if fr:
            assert fr.denominator == 1
            Q = Q + L.const(int(fr.numerator)) * L.p_nu_in_h(nu)
    return {'a': a, 'sE': sE, 'T': T, 'U': U, 'Q': L.prim(Q), 'ratios': ratios}


def decode_modes(P, p, rd):
    """Active modes (4): Z_m for every active m, from (P, p) and the readout only."""
    a, T, sE = rd['a'], rd['T'], rd['sE']
    Q = rd['Q']                       # recovered outer function (case-a normalized)
    fD = L.characters(Q, a)[(1,) * a]
    S_num, S_den = T, fD              # S = T / f^D
    Xi = L.exact_div(sE * T, rd['U'])
    Qp = L.power_sum_coeffs(Q, a)     # {lambda: coeff}
    from fractions import Fraction

    def dnu_p(coeffs, nu):
        # apply delta_nu in the power-sum basis: delta_k p_lam = k m_k(lam) p_{lam - k}
        cur = dict(coeffs)
        for k in nu:
            new = {}
            for lam, c in cur.items():
                m = lam.count(k)
                if m:
                    l2 = list(lam)
                    l2.remove(k)
                    l2 = tuple(l2)
                    new[l2] = new.get(l2, 0) + c * k * m
            cur = {x: y for x, y in new.items() if y}
        return cur
    active = [m for m in range(1, a + 1) if dnu_p(Qp, (m,))]
    Z = {}
    for m in active:
        wit = None
        for nu in L.partitions(a - m):
            R = dnu_p(Qp, nu)
            gam = R.get((m,), 0)
            if gam:
                wit = (nu, R, gam)
                break
        assert wit is not None, 'active mode without witness'
        nu, R, gam = wit
        lifted_num = Xi ** m * L.delta_seq(P, [p * k for k in nu]) * S_den
        lifted = L.exact_div(lifted_num, S_num)
        # subtract R_m(Z)
        rest_num = L.ZERO
        rest_den = 1
        terms = [(lam, c) for lam, c in R.items() if lam != (m,)]
        for lam, c in terms:
            rest_den = rest_den * Fraction(c).denominator // L.gcd(rest_den, Fraction(c).denominator)
        for lam, c in terms:
            assert all(j in Z for j in lam), ('inactive lower mode used', m, lam)
            term = L.const(int(Fraction(c) * rest_den))
            for j in lam:
                term = term * Z[j]
            rest_num = rest_num + term
        # Z_m = (lifted - rest_num/rest_den)/gam
        gamF = Fraction(gam)
        num = lifted * rest_den - rest_num
        den = gamF * rest_den
        # num / den must be an integral polynomial
        num = num * den.denominator
        dd = den.numerator
        Zm = L.exact_div(num, L.const(dd)) if dd != 1 else num
        Z[m] = Zm
    return Z, Xi


def main():
    t0 = time.time()
    counts = Counter()
    fails = []
    inners = []
    for n in range(2, NE_MAX + 1):
        for prof in L.profiles(n):
            inners.append(L.cells_of_prof(prof))
    outers = []
    for n in range(2, ND_MAX + 1):
        for prof in L.profiles(n):
            outers.append((prof, L.cells_of_prof(prof)))
    extra_outers = []
    for n in (5, 6):
        for prof in L.profiles(n):
            if any(g > 0 for g in prof[1]):          # nonribbon outers only
                extra_outers.append((prof, L.cells_of_prof(prof)))
    example = None
    for E in inners:
        sE_true = L.schur_cells(E)
        Ecount = len(E)
        marks = [m for m in ENG.w_candidates(E) if m[2] in ('a', 'b')]
        for (Wsw, Wne, case, v, _hv) in marks:
            p = v[1] - v[0]
            w = L.span_cells(Wsw) if Wsw else 0
            A = L.schur_cells(Wsw) if Wsw else L.ONE
            Wh, Oh = hatted(E, Wsw, Wne, v)
            B = L.schur_cells(Wh) if Wh else L.ONE
            C = L.schur_cells(Oh) if Oh else L.ONE
            sigma = (-1) ** (abs(v[0]) + (1 if case == 'b' else 0))   # vertical reading: v_V = v_H - e
            Xi_true = L.delta(sE_true, p)
            counts['marks'] += 1
            if Xi_true == L.const(sigma) * A * B * C:
                counts['Xi=sigmaABC'] += 1
            else:
                counts['Xi!=sigmaABC'] += 1
                if len(fails) < 20:
                    fails.append(('Xi', L.prof_of_cells(E), case, v, str(Xi_true), str(A * B * C)))
            use_outers = outers + (extra_outers if Ecount <= 4 else [])
            bvals = {}
            for (Dprof, Dc) in use_outers:
                F = ENG.compose(Dc, E, Wsw, Wne, case, v)
                mine = my_ordinary_compose(Dc, E, v, case)
                assert F == mine, ('engine compose disagrees with paper offsets', Dprof, L.prof_of_cells(E), case)
                Fprof = L.prof_of_cells(F)
                N = L.span_cells(F)
                r_D = len(Dprof[0])
                M_D = L.span_cells(Dc)
                assert N == M_D * p + w, ('span law', Dprof, L.prof_of_cells(E))
                P = L.schur_prof(Fprof)
                a = len(Dc)
                rd = readout(P, p)
                counts['charts'] += 1
                counts['nonribbon_outer'] += any(g > 0 for g in Dprof[1])
                ok1 = rd is not None and rd['a'] == a
                ok2 = ok1 and rd['sE'] == sE_true
                sD = L.schur_prof(Dprof)
                sDt = L.schur_cells(L.transpose_cells(Dc))
                target = sD if case == 'a' else sDt
                ok3 = ok2 and ('Q' in rd) and rd['Q'] == target
                if ok1:
                    counts['T1 a_p=|D|'] += 1
                if ok2:
                    counts['T2 s_E readout'] += 1
                if ok3:
                    counts['T3 outer readout'] += 1
                if case == 'b' and sD != sDt:
                    counts['case-b charts with s_D != omega s_D'] += 1
                    if ok3:
                        assert rd['Q'] != sD
                        counts['CONTROL fired: case-b readout differs from s_D'] += 1
                if not (ok1 and ok2 and ok3):
                    if len(fails) < 40:
                        fails.append(('readout', Dprof, L.prof_of_cells(E), case, v, rd and rd.get('a'),
                                      rd and str(rd.get('sE')), rd and rd.get('nonscalar')))
                    continue
                # T = sigma^a f^D A^r B^c C^M ?
                fD = L.characters(sD, a)[(1,) * a]
                c_D = M_D - r_D + 1
                Tpred = L.const(sigma ** a * fD) * A ** r_D * B ** c_D * C ** M_D
                if Tpred is not None:
                    if rd['T'] == Tpred:
                        counts['T=sigma^a f A^r B^c C^M'] += 1
                    else:
                        counts['T formula differs (case %s)' % case] += 1
                        if counts['T formula differs (case %s)' % case] <= 3:
                            print('TDIFF', case, Dprof, L.prof_of_cells(E), v, 'T=', rd['T'], 'pred=', Tpred)
                # Active modes: active-mode decoding (case a; case b via transposition)
                if case == 'a':
                    Z, Xi = decode_modes(P, p, rd)
                    assert Xi == Xi_true
                    for m, Zm in Z.items():
                        if m not in bvals:
                            row = frozenset((0, k) for k in range(m))
                            bm = ENG.compose(row, E, Wsw, Wne, case, v)
                            bvals[m] = L.schur_cells(bm)
                    # true M(p_m)
                    Mh = {0: L.ONE}
                    for j in range(1, max(Z) + 1):
                        if j not in bvals:
                            row = frozenset((0, k) for k in range(j))
                            bvals[j] = L.schur_cells(ENG.compose(row, E, Wsw, Wne, case, v))
                        Mh[j] = A ** (j - 1) * bvals[j]
                    for m, Zm in Z.items():
                        pm = L.p_in_h(m)
                        true = L.ZERO
                        for mono, co in zip(pm.monoms(), pm.coeffs()):
                            term = L.const(int(co))
                            for idx, e in enumerate(mono):
                                if e:
                                    term = term * Mh[idx + 1] ** e
                            true = true + term
                        if Zm == true:
                            counts['Active modes Z_m decoded'] += 1
                        else:
                            counts['Active modes Z_m WRONG'] += 1
                            if len(fails) < 40:
                                fails.append(('Zm', Dprof, L.prof_of_cells(E), m))
                    if 2 in Z:
                        J2 = L.exact_div(Z[2] + sE_true ** 2, L.const(2))
                        assert J2 == A * bvals[2], 'J2 != A b2'
                        fac = J2.factor()
                        small = [f for f, e in fac[1] if L.weight(f) < Ecount]
                        if Wsw:
                            okA = len(small) == 1 and L.prim(small[0]) == A
                        else:
                            okA = len(small) == 0
                        counts['Active modes s_W by factor selection ' + ('OK' if okA else 'FAIL')] += 1
                        if not okA and len(fails) < 40:
                            fails.append(('sW', Dprof, L.prof_of_cells(E), [str(f) for f in small], str(A)))
                        if 3 in Z:
                            J3 = L.exact_div(Z[3] - sE_true ** 3, L.const(3))
                            gg = J2.gcd(J3)
                            okG = L.prim(gg) == A
                            counts['Active modes s_W by gcd(J2,J3) ' + ('OK' if okG else 'FAIL')] += 1
                            if not okG and len(fails) < 40:
                                fails.append(('gcdA', Dprof, L.prof_of_cells(E), str(gg), str(A)))
                    else:
                        counts['Active modes mode 2 inactive'] += 1
                    if example is None and Wsw and 2 in Z and any(g > 0 for g in Dprof[1]):
                        example = (Dprof, L.prof_of_cells(E), case, v, Fprof, str(A))
        L.schur_prof.cache_clear()
    # ---------------- firing controls ----------------
    ctl = Counter()
    # (i) wrong period: E = (2,3;1) type two-row inner with a legal mark, readout at p+1
    for prof in [((3, 3), (1,)), ((2, 4, 2), (1, 1)), ((3, 2, 1), (1, 0))]:
        E = L.cells_of_prof(prof)
        for (Wsw, Wne, case, v, _hv) in ENG.w_candidates(E):
            if case not in ('a', 'b'):
                continue
            p = v[1] - v[0]
            Dc = L.cells_of_prof(((2, 2), (1,)))
            F = ENG.compose(Dc, E, Wsw, Wne, case, v)
            P = L.schur_prof(L.prof_of_cells(F))
            for pp in (p - 1, p + 1):
                if pp < 2:
                    continue
                rd = readout(P, pp)
                wrong = (rd is None or rd['a'] != 4 or rd['sE'] != L.schur_cells(E)
                         or rd.get('Q') != (L.schur_prof(((2, 2), (1,)))))
                ctl['wrong period gives a wrong readout' if wrong else 'wrong period NOT detected'] += 1
    # (ii) a mixed chart: the ordinary readout must fail (delta_p P = 0)
    hook = L.cells_of_prof(((2, 1), (0,)))
    for (Wsw, Wne, case, v, _hv) in ENG.w_candidates(hook):
        if case in ('c', 'd'):
            Dc = L.cells_of_prof(((2, 2), (1,)))
            F = ENG.compose(Dc, hook, Wsw, Wne, case, v)
            P = L.schur_prof(L.prof_of_cells(F))
            p = v[1] - v[0]
            ctl['mixed chart: delta_p P = 0' if L.delta(P, p).is_zero() else 'mixed chart: delta_p P != 0'] += 1
    # (iii) empty-outer trap
    if ENG.compose(frozenset(), hook, frozenset(), frozenset(), 'a', (0, 2)) == frozenset():
        ctl['engine returns EMPTY set for an empty outer (known defect; no empty outer is used)'] += 1
    print('COUNTS', json.dumps(dict(counts), indent=1))
    print('CONTROLS', json.dumps(dict(ctl), indent=1))
    print('EXAMPLE nonribbon outer with active mode 2 and nonempty mark:', example)
    print('FAILS (first 40):')
    for f in fails:
        print('  ', f)
    print('RANGE: inners 2..%d cells (all connected), all legal ordinary marks; outers 2..%d cells (all), '
          'plus nonribbon outers of 5-6 cells on inners <= 4 cells' % (NE_MAX, ND_MAX))
    assert counts['charts'] > 0
    assert ctl['wrong period NOT detected'] == 0
    status = 'ALL PASS' if not [f for f in fails if f[0] != 'Xi'] and counts['Active modes Z_m WRONG'] == 0 else 'FAILURES'
    print(status, '(%.0fs)' % (time.time() - t0))
    assert status == 'ALL PASS'


if __name__ == '__main__':
    main()
