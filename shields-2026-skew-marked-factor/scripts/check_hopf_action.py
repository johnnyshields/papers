"""Paper section `sec:action` (Marked composition and the power-sum action); results `lem:action`, `eq:action`.

Second route to the power-sum action: the identities of Sec. 5.4 and 5.5, EXACTLY in the shape
Hopf algebra S (formal sums of congruence classes; no Schur functions involved).

For a mark (E, W) and a shape D the modified composition is (thesis (5.13), (5.14))
    [D] []_W E = sgn(D) [W]^(|D|-row D) [Wbar]^(|D|-col D) [Obar]^(|D|-dia D) [D o_W E],
sgn = 1 (edge), (-1)^xi(D) (corner), extended multiplicatively over components and linearly.
Xi = (-1)^h(E) [W][Wbar][Obar].  Checked, for every connected D in the range and every m >= 1 with
m <= |D| + 1:
  case (a) Lemma 5.4.7:   ([D][]E) <- p_mk = Xi^m (([D] <- p_m) [] E),  p_mk -> ([D][]E) = Xi^m ((p_m -> [D]) [] E)
  case (b) Thm 5.4.9 (f = p_m, omega(p_m) = (-1)^(m-1) p_m):
           ([D][]E) <- p_mk = (-1)^(m-1) Xi^m ((p_m -> [D]) [] E),  p_mk -> ([D][]E) = (-1)^(m-1) Xi^m (([D] <- p_m) [] E)
  case (c) Lemma 5.5.12:  p_mk -> ([D][]E) = Xi^m ((p_m -> [D] - [D] <- p_m) [] E),  ([D][]E) <- p_mk = 0
  case (d) Lemma 5.5.13:  p_mk -> ([D][]E) = 0,  ([D][]E) <- p_mk = Xi^m (([D] <- p_m - p_m -> [D]) [] E)
and, for nu = (m1, m2), Thm 5.4.8 / the iteration step of Thm 5.5.14 (two successive actions).
Here k(E), h(E) are computed from the key ribbons built from the thesis's definitions (edge: K_up,
K_down of Sec. 5.3.3; corner: K_W = W \\ Wbar, K_O = SE(O), h = ht K_W + ht K_O + 1 (Sec. 5.5));
k(E) is asserted = content of v.  The empty mark (horizontal reading, the thesis's emptyset->O->emptyset)
is included.
FIRING CONTROLS: (F1) improper I-III edge marks (Hypothesis IV fails): the case-(a)/(b) identity must
fail for some D (counted per mark); (F2) on legal marks, the sign (-1)^h dropped; (F3) the corner sign
(-1)^xi dropped; (F4) Xi^(m-1) for Xi^m -- each must be refuted somewhere.
Usage: python3 check_hopf_action.py EMAX DMAX [vfail_only] [EMIN]
"""
import sys
import time
from collections import Counter
import _hopf_shapes_lib as L

eng = L.eng


def neg(S):
    return frozenset((-i, -j) for i, j in S)


def T(S):
    return frozenset((j, i) for i, j in S)


def kh_of(E, mk):
    """(k, h) of the mark from the thesis's key ribbons."""
    c = mk['case']
    v = mk['v']
    if c == 'a':
        bars = L.thesis_bars(E, mk['Wsw'], mk['Wne'], v)
        Ku, Kd, _ = L.key_ribbons_edge_a(E, mk, bars)
        assert len(Ku) == len(Kd)
        return len(Ku), L.height(Ku)
    if c == 'b':                      # through the transpose: K(E^T) = K(E)^T
        Et = T(E)
        mt = dict(Wsw=T(mk['Wne']), Wne=T(mk['Wsw']), case='a', v=(-v[1], -v[0]))
        bt = L.thesis_bars(Et, mt['Wsw'], mt['Wne'], mt['v'])
        Ku, Kd, _ = L.key_ribbons_edge_a(Et, mt, bt)
        return len(Ku), L.ncols(Ku) - 1     # height of the transposed ribbon
    if c == 'c':
        bars = L.thesis_bars(E, mk['Wsw'], mk['Wne'], v)
        Wmid = frozenset(mk['Wne'])
        KW = Wmid - bars['Wbar']
        KO = L.se_border(bars['O'])
        assert bars['Wbar'] <= Wmid
        assert L.is_ribbon(KW) and L.is_ribbon(KO)
        return len(KW) + len(KO), L.height(KW) + L.height(KO) + 1
    # case d: k(E) = k(E*), h(E) = h(E*)
    Er = neg(E)
    mr = dict(Wsw=neg(mk['Wne']), Wne=neg(mk['Wsw']), case='c', v=v)
    assert eng.attachment_case(Er, mr['Wsw'], mr['Wne'], Er - mr['Wsw'] - mr['Wne']) == 'c'
    return kh_of(Er, mr)


class Box:
    """[D] []_W E on S, cached per connected component."""

    def __init__(self, E, mk, sign_xi=True):
        self.E, self.mk = frozenset(E), mk
        bars = L.thesis_bars(self.E, mk['Wsw'], mk['Wne'], mk['v'])
        self.W = L.s_basis(mk['Wsw'])
        self.Wb = L.s_basis(bars['Wbar'])
        self.Ob = L.s_basis(bars['Obar'])
        self.corner = mk['case'] in 'cd'
        self.sign_xi = sign_xi
        self.cache = {}

    def comp(self, ckey):
        if ckey in self.cache:
            return self.cache[ckey]
        D = frozenset(ckey)
        F = L.compose_checked(D, self.E, self.mk)
        n = len(D)
        sgn = (-1) ** L.nw_decomp_northbound(D) if (self.corner and self.sign_xi) else 1
        val = L.s_basis(F, sgn)
        val = L.s_mul(val, L.s_pow(self.W, n - L.nrows(D)))
        val = L.s_mul(val, L.s_pow(self.Wb, n - L.ncols(D)))
        val = L.s_mul(val, L.s_pow(self.Ob, n - L.ndia(D)))
        self.cache[ckey] = val
        return val

    def __call__(self, h):
        out = {}
        for k, c in h.items():
            term = {(): c}
            for comp in k:
                term = L.s_mul(term, self.comp(comp))
            out = L.s_add(out, term)
        return out


def check_mark(E, mk, Ds, k, hE, cnt, tag, sgn_h=True, xi=True, xi_exp=0):
    box = Box(E, mk, sign_xi=xi)
    Xi = L.s_mul(L.s_mul(box.W, box.Wb), box.Ob)
    if sgn_h and hE % 2:
        Xi = {kk: -vv for kk, vv in Xi.items()}
    c = mk['case']
    ok = True
    for D in Ds:
        d = L.s_basis(D)
        bd = box(d)
        for m in range(1, len(D) + 2):
            Xm = L.s_pow(Xi, m + xi_exp)
            lhs_L = L.act(bd, m * k, 'L')
            lhs_R = L.act(bd, m * k, 'R')
            dL = L.act(d, m, 'L')
            dR = L.act(d, m, 'R')
            if c == 'a':
                rL, rR = L.s_mul(Xm, box(dL)), L.s_mul(Xm, box(dR))
            elif c == 'b':
                s = (-1) ** (m - 1)
                rL = {kk: s * vv for kk, vv in L.s_mul(Xm, box(dR)).items()}
                rR = {kk: s * vv for kk, vv in L.s_mul(Xm, box(dL)).items()}
            elif c == 'c':
                rL = {}
                rR = L.s_mul(Xm, box(L.s_add(dR, dL, -1)))
            else:
                rR = {}
                rL = L.s_mul(Xm, box(L.s_add(dL, dR, -1)))
            if lhs_L != rL or lhs_R != rR:
                ok = False
                cnt[tag + ' FAIL'] += 1
                return ok
            cnt[tag + ' identities'] += 2
        # two-part nu = (1, m2): successive actions (iteration in Thm 5.4.8 / 5.5.14)
        if c in 'ab' and len(D) >= 2:
            m1, m2 = 1, len(D) - 1
            lhs = L.act(L.act(bd, m1 * k, 'L'), m2 * k, 'L')
            if c == 'a':
                rhs = L.s_mul(L.s_pow(Xi, m1 + m2 + xi_exp), box(L.act(L.act(d, m1, 'L'), m2, 'L')))
            else:
                s = (-1) ** (m1 - 1 + m2 - 1)
                rhs = {kk: s * vv for kk, vv in L.s_mul(L.s_pow(Xi, m1 + m2 + xi_exp),
                                                         box(L.act(L.act(d, m1, 'R'), m2, 'R'))).items()}
            if lhs != rhs:
                cnt[tag + ' FAIL'] += 1
                return False
            cnt[tag + ' identities'] += 1
    return ok


def main():
    EMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    vfail_only = len(sys.argv) > 3 and sys.argv[3] == '1'
    EMIN = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    t0 = time.time()
    Ds = [frozenset(D) for D in L.connected_shapes(1, DMAX)]
    # two disconnected outers as extra inputs
    Ds_extra = [frozenset({(0, 1), (1, 0)}), frozenset({(0, 2), (0, 3), (1, 0), (1, 1)})]
    cnt = Counter()
    ctrl = Counter()
    for n in range(EMIN, EMAX + 1):
        for E in L.connected_shapes(n, n):
            E = frozenset(E)
            marks = []
            if not vfail_only:
                marks.append(dict(Wsw=frozenset(), Wne=frozenset(), case='a',
                                  v=eng.v_of_W(E, frozenset(), frozenset(), 'a'), legal=True, V=True))
            for mk in L.all_marks(E):
                if not (mk['hypI'] and mk['hypIII']):
                    continue
                mk['legal'] = mk['iv_eng']
                if vfail_only and not (mk['legal'] and mk['case'] in 'ab' and not mk['V']):
                    if not (not mk['legal'] and mk['case'] in 'ab'):
                        continue
                marks.append(mk)
            for mk in marks:
                k, hE = kh_of(E, mk)
                v = mk['v']
                assert k == v[1] - v[0], ('k != content(v)', sorted(E), mk['case'], k, v)
                c = mk['case']
                if mk['legal']:
                    tag = 'legal ' + c + (' V-fail' if (c in 'ab' and not mk['V']) else '')
                    ok = check_mark(E, mk, Ds + Ds_extra, k, hE, cnt, tag)
                    assert ok, ('IDENTITY FAILS on a legal mark', sorted(E), c, sorted(mk['Wsw']))
                    cnt['legal marks checked ' + c] += 1
                    # controls on a subsample of legal marks
                    if not mk['Wsw'] or cnt['ctrl budget ' + c] < 40:
                        cnt['ctrl budget ' + c] += 1
                        if hE % 2 and not check_mark(E, mk, Ds, k, hE, Counter(), 'x', sgn_h=False):
                            ctrl['F2 sign (-1)^h dropped refuted'] += 1
                        if c in 'cd' and not check_mark(E, mk, Ds, k, hE, Counter(), 'x', xi=False):
                            ctrl['F3 corner sign (-1)^xi dropped refuted'] += 1
                        if mk['Wsw'] and not check_mark(E, mk, Ds, k, hE, Counter(), 'x', xi_exp=-1):
                            ctrl['F4 Xi^(m-1) refuted'] += 1
                elif c in 'ab':
                    ok = check_mark(E, mk, Ds, k, hE, Counter(), 'imp')
                    ctrl['F1 improper edge marks tested'] += 1
                    if not ok:
                        ctrl['F1 improper edge marks REFUTED'] += 1
        print(f'PROGRESS n={n} {dict(cnt)} controls={dict(ctrl)} t={time.time()-t0:.0f}s', flush=True)
    for kk in ('F2 sign (-1)^h dropped refuted', 'F4 Xi^(m-1) refuted'):
        assert ctrl[kk] > 0, kk
    if not vfail_only:
        assert ctrl['F3 corner sign (-1)^xi dropped refuted'] > 0
    assert ctrl['F1 improper edge marks REFUTED'] == ctrl['F1 improper edge marks tested']
    print('RESULT', dict(cnt))
    print('CONTROLS', dict(ctrl))
    print(f'ALL PASS (inners {EMIN}..{EMAX} cells, connected outers 1..{DMAX} cells + 2 disconnected, '
          f'vfail_only={vfail_only}) t={time.time()-t0:.0f}s')


if __name__ == '__main__':
    main()
