"""Paper section `sec:extraction` (Recovering the factors); results `thm:extraction`, `eq:ratio`, `lem:primitive`.

Ordinary extraction and area bounds, by a second route (python-flint).

For each ordinary chart F = D o_omega E (D discrete-interior, D^- nonempty) the DECODER receives only (P, p):
  a  = max{j : delta_p^j P != 0}                      (must equal |D|)
  T  = delta_p^a P, U = delta_p^(a-1) P, e = prim(U / gcd(U, T))   (must equal s_E)
  Xi = T e / U
  q_nu = delta_{p nu} P / T   (scalars, nu |- a)
  mode m active  <=>  q_{mu u (m)} != 0 for some mu |- a - m
  R_mu = delta_{p mu} P * Xi^m / T  = sum_{lam |- m} q_{mu u lam} / z_lam * prod Zhat_{lam_i}   (solved for Zhat_m)
Every admissible mu must give the same Zhat_m (asserted).
Targets, computed independently of the decoder from the mark geometry and literal compositions:
  A = s_W, B = s_What, C = s_Ohat (Hypothesis IV hatted sets in a 7-copy amalgam), b_j = s_{(j) o E},
  M(h_j) = A^(j-1) b_j, M(p_m) by Newton; Phi = M (case a), M o iota (case b): Phi(p_m) = (-1)^(m-1) M(p_m).
Checked: Zhat_m == Phi(p_m); (5) J_2 = (e^2 + Zhat_2)/2 == A s_{(2) o E} (a) / B s_{(1,1) o E} (b);
(6) J_3 = (e^3 - Zhat_3)/3 == A B s_{K o E}, K = (2,1;0); J_m has exactly ONE irreducible factor containing some
h_j, j >= p, and it is +- the probe function; spans of A, B, C are < p; the area law and the probe areas (8),
all < |F|; the effective-outer readout prim sum q_nu p_nu/z_nu = s_D (a) / s_{D^t} (b); active sets of s_D and
s_{D^t} agree.  Cross-type exclusion: every MIXED legal mark of the same inners gives delta_p P = 0.
Controls (must fire): in case (b) the row probe does not divide J_2; the decoder at p+1 fails.
"""
import argparse
import itertools
import math
import os
import sys
import time
from collections import Counter
from fractions import Fraction

import flint

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import _decoder_lib as L  # noqa: E402
import importlib.util  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    'eng', os.path.join(HERE, '_composition_engine.py'))
eng = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(eng)


# ----------------------------------------------------------------------------- polynomial helpers (fmpq)
class QR:
    def __init__(self, N):
        self.N = N
        self.ctx = flint.fmpq_mpoly_ctx.get(('h', N), 'deglex')
        self.g = self.ctx.gens()
        self.one = self.ctx.from_dict({(0,) * N: 1})
        self.zero = self.ctx.from_dict({})

    def h(self, k):
        if k == 0:
            return self.one
        if k < 0:
            return self.zero
        return self.g[k - 1]


def det_q(M, R):
    r = len(M)
    memo = {}

    def rec(i, cols):
        if i == r:
            return R.one
        key = (i, cols)
        if key in memo:
            return memo[key]
        acc = R.zero
        for pos, j in enumerate(cols):
            e = M[i][j]
            if e < 0:
                continue
            sub = rec(i + 1, cols[:pos] + cols[pos + 1:])
            acc = acc - R.h(e) * sub if (pos & 1) else acc + R.h(e) * sub
        memo[key] = acc
        return acc

    return rec(0, tuple(range(r)))


def comps(S):
    S = set(S)
    out = []
    while S:
        x = S.pop()
        st = [x]
        c = {x}
        while st:
            i, j = st.pop()
            for nb in ((i + 1, j), (i - 1, j), (i, j + 1), (i, j - 1)):
                if nb in S:
                    S.discard(nb)
                    c.add(nb)
                    st.append(nb)
        out.append(frozenset(c))
    return out


def s_of_set(S, R):
    f = R.one
    for c in comps(S):
        cn = L.normalize(c)
        assert eng.is_connected_skew(cn), "component not skew"
        f = f * det_q(L.jt_index_matrix(cn), R)
    return f


def sp(f, R):
    best = 0
    for m in f.to_dict():
        for t, x in enumerate(m):
            if x:
                best = max(best, t + 1)
    return best


def delta(f, k, R):
    acc = R.zero
    for j in range(k, R.N + 1):
        d = f.derivative(j - 1)
        if not d.is_zero():
            acc = acc + R.h(j - k) * d
    return acc


class DecodeFail(Exception):
    pass


def prim(f, R):
    """Scale so that the minimum-square monomial (sum of j^2 over its h_j factors; the JT row monomial of a skew
    Schur polynomial, unique by strict rearrangement) has coefficient +1."""
    d = f.to_dict()
    best = None
    for m, c in d.items():
        key = sum((t + 1) ** 2 * x for t, x in enumerate(m))
        if best is None or key < best[0]:
            best = (key, c, 1)
        elif key == best[0]:
            best = (key, best[1], best[2] + 1)
    if best[2] != 1:
        raise DecodeFail("minimum-square monomial not unique")
    return f * (1 / flint.fmpq(best[1]))


def partitions(n, maxp=None):
    if maxp is None:
        maxp = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxp), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def zee(lam):
    c = Counter(lam)
    z = 1
    for i, m in c.items():
        z *= i ** m * math.factorial(m)
    return z


# ----------------------------------------------------------------------------- geometry
def hatted_sets(E, Wsw, Wne, v, K=7):
    O = E - Wsw - Wne
    Eb = set()
    for t in range(-K, K + 1):
        Eb |= eng.shift(E, (t * v[0], t * v[1]))
    W1 = Wsw  # the copy at t = 0, interior of the amalgam
    What = {x for x in Eb if (x[0] + 1, x[1] + 1) in W1} | {x for x in W1 if (x[0] + 1, x[1] + 1) in Eb}
    Ohat = {x for x in O if (x[0] + 1, x[1] + 1) in O}
    return frozenset(What), frozenset(Ohat)


def compose(D, E, mk):
    Wsw, Wne, case, v, _ = mk
    return eng.compose(D, E, Wsw, Wne, case, v)


ROW2 = frozenset({(0, 0), (0, 1)})
COL2 = frozenset({(0, 0), (1, 0)})
HOOK = frozenset({(0, 0), (0, 1), (1, 0)})


def rows_cols(D):
    return len({i for i, _ in D}), len({j for _, j in D})


# ----------------------------------------------------------------------------- the decoder: (P, p) only
def decode(P, p, R):
    a = 0
    cur = P
    chain = [P]
    while True:
        nxt = delta(cur, p, R)
        if nxt.is_zero():
            break
        a += 1
        chain.append(nxt)
        cur = nxt
        if a > 40:
            raise DecodeFail("a too large")
    if a == 0:
        raise DecodeFail("delta_p P = 0")
    T = chain[a]
    U = chain[a - 1]
    g = U.gcd(T)
    num = U / g
    e = prim(num, R)
    try:
        Xi = (T * e) / U
    except Exception:
        raise DecodeFail("Xi not polynomial")
    # q_nu for nu |- a, with memo of delta_{p mu} P
    memo = {(): P}

    def dmu(mu):
        mu = tuple(sorted(mu, reverse=True))
        if mu in memo:
            return memo[mu]
        f = delta(dmu(mu[1:]), p * mu[0], R)
        memo[mu] = f
        return f

    q = {}
    for nu in partitions(a):
        val = dmu(nu)
        if val.is_zero():
            q[nu] = Fraction(0)
            continue
        try:
            ratio = val / T
        except Exception:
            raise DecodeFail("ratio not polynomial")
        if not ratio.is_constant():
            raise DecodeFail("ratio not scalar")
        c = ratio.to_dict().get((0,) * R.N, 0)
        q[nu] = Fraction(int(c.p), int(c.q))
    # effective outer function, in the p-basis: sum q_nu p_nu / z_nu (returned as dict nu -> coeff)
    Q = {nu: q[nu] / zee(nu) for nu in q}

    def qq(mu, lam):
        return q[tuple(sorted(mu + lam, reverse=True))]

    Z = {1: e}
    active = {}
    for m in (2, 3):
        if m > a:
            active[m] = False
            continue
        mus = [mu for mu in partitions(a - m) if qq(mu, (m,)) != 0]
        active[m] = bool(mus)
        if not mus:
            continue
        vals = []
        for mu in mus:
            Rmu = (dmu(mu) * Xi ** m) / T
            acc = Rmu
            for lam in partitions(m):
                if lam == (m,):
                    continue
                c = qq(mu, lam)
                if c == 0:
                    continue
                if any(part not in Z for part in lam):
                    raise DecodeFail("inactive lower mode needed")
                term = R.one
                for part in lam:
                    term = term * Z[part]
                acc = acc - term * flint.fmpq(c.numerator, c.denominator) * flint.fmpq(1, zee(lam))
            cm = qq(mu, (m,)) / m
            vals.append(acc * flint.fmpq(cm.denominator, cm.numerator))
        for v_ in vals[1:]:
            if v_ != vals[0]:
                raise DecodeFail("inconsistent Zhat across mu")
        Z[m] = vals[0]
    return dict(a=a, e=e, Xi=Xi, Z=Z, active=active, Q=Q, T=T)


def p_basis_to_poly(Qd, R):
    """sum c_nu p_nu as a polynomial in h, via Newton."""
    maxn = max((sum(nu) for nu in Qd), default=0)
    pp = {0: R.one}
    for n in range(1, maxn + 1):
        acc = R.h(n) * n
        for i in range(1, n):
            acc = acc - pp[i] * R.h(n - i)
        pp[n] = acc
    f = R.zero
    for nu, c in Qd.items():
        if c == 0:
            continue
        t = R.one
        for part in nu:
            t = t * pp[part]
        f = f + t * flint.fmpq(c.numerator, c.denominator)
    return f


# ----------------------------------------------------------------------------- one chart
def run_chart(D, E, mk, stats, verbose=False, controls=True):
    Wsw, Wne, case, v, _ = mk
    F = compose(D, E, mk)
    assert F is not None
    p = v[1] - v[0]
    w = len({j - i for i, j in Wsw})
    NF = L.span(F)
    assert NF == p * L.span(D) + w, "span law"
    probes = {'row': compose(ROW2, E, mk), 'col': compose(COL2, E, mk), 'hook': compose(HOOK, E, mk)}
    Nmax = max(NF, max(L.span(x) for x in probes.values())) + 2
    R = QR(Nmax)
    P = det_q(L.jt_index_matrix(F), R)
    sE = det_q(L.jt_index_matrix(E), R)
    dec = decode(P, p, R)
    ok = True
    if dec['a'] != len(D):
        ok = False
        print("FAIL a_p != |D|", sorted(D), sorted(E), case)
    if dec['e'] != sE:
        ok = False
        print("FAIL e != s_E", sorted(D), sorted(E), case)
    # targets
    What, Ohat = hatted_sets(E, Wsw, Wne, v)
    A = s_of_set(Wsw, R) if Wsw else R.one
    B = s_of_set(What, R) if What else R.one
    C = s_of_set(Ohat, R) if Ohat else R.one
    for name, f in (('A', A), ('B', B), ('C', C)):
        if sp(f, R) >= p:
            ok = False
            print("FAIL span of", name, ">= p")
    a_, b_, z_ = len(Wsw), len(What), len(Ohat)
    if len(E) != p + a_ + b_ + z_:
        ok = False
        print("FAIL e0 = p+a+b+z", sorted(E), case, len(E), p, a_, b_, z_)
    rD, cD = rows_cols(D)
    if len(F) != p * len(D) + a_ * rD + b_ * cD + z_ * L.span(D):
        ok = False
        print("FAIL area law")
    sizes = {'row': 2 * p + a_ + 2 * b_ + 2 * z_, 'col': 2 * p + 2 * a_ + b_ + 2 * z_,
             'hook': 3 * p + 2 * a_ + 2 * b_ + 3 * z_}
    for k_, X in probes.items():
        if len(X) != sizes[k_] or not len(X) < len(F):
            ok = False
            print("FAIL probe area", k_, len(X), sizes[k_], len(F))
    if len(F) < 4 * p + 2 * a_ + 2 * b_ + 3 * z_:
        ok = False
        print("FAIL (7)")
    # Phi(p_m)
    bj = {j: det_q(L.jt_index_matrix(compose(frozenset((0, t) for t in range(j)), E, mk)), R) for j in (1, 2, 3)}
    Mh = {j: A ** (j - 1) * bj[j] for j in (1, 2, 3)}
    if Mh[1] != sE:
        ok = False
        print("FAIL M(h1) != s_E")
    Mp = {1: Mh[1], 2: Mh[2] * 2 - Mh[1] ** 2, 3: Mh[3] * 3 - Mh[1] * Mh[2] * 3 + Mh[1] ** 3}
    sgn = (lambda m: 1) if case == 'a' else (lambda m: (-1) ** (m - 1))
    # effective outer
    Qpoly = p_basis_to_poly(dec['Q'], R)
    sD = det_q(L.jt_index_matrix(D), R)
    sDt = det_q(L.jt_index_matrix(eng.transpose(D)), R)
    target_outer = sD if case == 'a' else sDt
    fD = Qpoly / target_outer if not Qpoly.is_zero() else None
    if fD is None or not fD.is_constant():
        ok = False
        print("FAIL effective outer")
    # active sets of s_D and s_D^t agree; and agree with the decoder
    for m in (2, 3):
        a1 = not delta(sD, m, R).is_zero()
        a2 = not delta(sDt, m, R).is_zero()
        if a1 != a2 or a1 != dec['active'][m]:
            ok = False
            print("FAIL active-set", m, a1, a2, dec['active'][m])
    e = dec['e']
    for m in (2, 3):
        if not dec['active'][m]:
            stats[f'inactive{m}'] += 1
            continue
        Zm = dec['Z'][m]
        if Zm != Mp[m] * sgn(m):
            ok = False
            print("FAIL Zhat_m != Phi(p_m)", m, case)
        if m == 2:
            J = (e ** 2 + Zm) * flint.fmpq(1, 2)
            if case == 'a':
                probe, cof = probes['row'], A
            else:
                probe, cof = probes['col'], B
        else:
            J = (e ** 3 - Zm) * flint.fmpq(1, 3)
            probe, cof = probes['hook'], A * B
        sprobe = det_q(L.jt_index_matrix(probe), R)
        if J != cof * sprobe:
            ok = False
            print("FAIL identity", m, case, sorted(D), sorted(E))
        # unique high-span factor
        Jz = flint.fmpz_mpoly_ctx.get(('h', R.N), 'deglex')
        Jint = Jz.from_dict({k: int(c) for k, c in J.to_dict().items()}) if all(
            c.q == 1 for c in J.to_dict().values()) else None
        if Jint is None:
            ok = False
            print("FAIL J not integral")
        else:
            _, facs = Jint.factor()
            high = []
            for f_, mult in facs:
                fs = max((t + 1 for mm in f_.to_dict() for t, x in enumerate(mm) if x), default=0)
                if fs >= p:
                    high.append((f_, mult))
            sp_int = Jz.from_dict({k: int(c) for k, c in sprobe.to_dict().items()})
            if len(high) != 1 or high[0][1] != 1 or not (high[0][0] == sp_int or high[0][0] == -sp_int):
                ok = False
                print("FAIL unique high factor", m, case, len(high))
        stats[f'J{m}{case}'] += 1
        if controls and m == 2 and case == 'b':
            srow = det_q(L.jt_index_matrix(probes['row']), R)
            try:
                qq_ = J / srow
                divides = True
            except Exception:
                divides = False
            if L.normalize(probes['row']) in (L.normalize(probes['col']), L.rotate(probes['col'])):
                stats['ctrl_b_row_is_col'] += 1
            elif divides and srow != sprobe:
                stats['ctrl_b_row_divides'] += 1
            else:
                stats['ctrl_b_fired'] += 1
    if controls:
        try:
            d2 = decode(P, p + 1, R)
            if d2['e'] == sE and d2['a'] == len(D):
                stats['ctrl_p1_silent'] += 1
            else:
                stats['ctrl_p1_fired'] += 1
        except DecodeFail:
            stats['ctrl_p1_fired'] += 1
    stats['charts'] += 1
    stats['case_' + case] += 1
    if not ok:
        stats['fail'] += 1
    return ok


def mixed_check(D, E, mk, stats):
    Wsw, Wne, case, v, _ = mk
    F = compose(D, E, mk)
    p = v[1] - v[0]
    R = QR(L.span(F) + 2)
    P = det_q(L.jt_index_matrix(F), R)
    for k in (1, 2):
        if not delta(P, k * p, R).is_zero():
            stats['mixed_fail'] += 1
            print("FAIL mixed annihilation", sorted(D), sorted(E), case)
            return
    stats['mixed_ok'] += 1


def inners(lo, hi):
    out = []
    for n in range(lo, hi + 1):
        for rows, gaps in L.all_connected_profiles(n):
            E = L.cells_from_profile(rows, gaps)
            if len(rows) == 1 or max(rows) == 1:
                continue        # lines excluded (K1); nonline inners only
            out.append(E)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--emin', type=int, default=3)
    ap.add_argument('--emax', type=int, default=5)
    ap.add_argument('--dmax', type=int, default=6)
    ap.add_argument('--fixtures', action='store_true')
    ap.add_argument('--maxF', type=int, default=40)
    ap.add_argument('--maxrows', type=int, default=18)
    A = ap.parse_args()
    stats = Counter()
    t0 = time.time()
    outers = []
    for a in range(4, A.dmax + 1):
        for rows, gaps in L.positive_discrete_profiles(a):
            outers.append(L.cells_from_profile(rows, gaps))
    if A.fixtures:
        Efix = [L.cells_from_profile((2, 3, 2, 1), (0, 1, 0)), L.cells_from_profile((3, 2, 2, 1), (1, 0, 0))]
        Dfix = [L.cells_from_profile(*x) for x in [((2, 3), (1,)), ((2, 2), (1,)), ((3, 2, 1), (1, 0)),
                                                   ((3, 3, 3), (1, 1))]]
        pairs = [(D, E) for E in Efix for D in Dfix]
    else:
        pairs = [(D, E) for E in inners(A.emin, A.emax) for D in outers]
    print(f"{len(pairs)} (outer, inner) pairs; outers: {len(outers) if not A.fixtures else 4}", flush=True)
    for idx, (D, E) in enumerate(pairs):
        for mk in eng.w_candidates(E):
            case = mk[2]
            est = len(D) * len(E)
            if est > A.maxF:
                stats['skipped_size'] += 1
                continue
            Ft = compose(D, E, mk)
            if len({i for i, _ in Ft}) > A.maxrows:
                stats['skipped_rows'] += 1
                continue
            if case in ('a', 'b'):
                try:
                    run_chart(D, E, mk, stats)
                except MemoryError:
                    stats['skipped_memory'] += 1
                    continue
                except DecodeFail as ex:
                    stats['fail'] += 1
                    print("FAIL decode", ex, L.profile_of(D), L.profile_of(E), case)
            else:
                try:
                    mixed_check(D, E, mk, stats)
                except MemoryError:
                    stats['skipped_memory'] += 1
        if idx % 50 == 0:
            print(f"  PROGRESS {idx}/{len(pairs)} {dict(stats)} {time.time() - t0:.0f}s", flush=True)
    print("FINAL", dict(sorted(stats.items())))
    good = (stats['fail'] == 0 and stats['mixed_fail'] == 0 and stats['ctrl_p1_silent'] == 0)
    print("controls: p+1 decoder fired on", stats['ctrl_p1_fired'], "silent on", stats['ctrl_p1_silent'],
          "; case-(b) row-probe control fired on", stats['ctrl_b_fired'], "(row probe = column probe up to rotation:",
          stats['ctrl_b_row_is_col'], "; row divides:", stats['ctrl_b_row_divides'], ")")
    assert good, "decoder, mixed-chart or control failure"
    assert stats['ctrl_b_fired'] > 0
    print("ALL PASS", f"({time.time() - t0:.0f}s)")


if __name__ == '__main__':
    main()
