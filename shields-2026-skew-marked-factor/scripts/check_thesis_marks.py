"""Paper section `sec:action` (Marked composition and the power-sum action); the marks of `eq:hats`.

The thesis's vocabulary against MvW's hypotheses, and Thm 5.4.1.

For every connected inner E of 2..NMAX cells and every mark with Hypotheses I, II, III and the
attachment dichotomy (Hypothesis IV NOT imposed), checks:
  (M1) the I-IV marks (iv_eng True) are exactly the engine's w_candidates (nonempty W);
  (M2) thesis attachment classification (Sec. 5.3: NE box of Wsw / SW box of Wne) = MvW's (engine);
  (M3) Remark 5.3.6: thesis properness (W-bar vs O-bar in E u_W E) = MvW Hypothesis IV (infinite strip,
       engine), and the thesis's "equivalently, W-underbar not adjacent to O-underbar";
  (M4) Remark 5.3.7 containments (W-bar in E1 for (a), in Wmid for (c); W-underbar in E2 for (a), ...);
  (M5) footnote 6: marks with I, II, O connected but Hypothesis III failing (MvW III = complements of
       each W connected skew) -- counted (the thesis's W O W class could only be LARGER);
  (M6) key ribbons (Sec. 5.3.3) for edge marks: K_up, K_down are ribbons, K_up removable on the left,
       K_down on the right, same size / rows / columns (Lemma 5.3.13), size = content of v (Rem. 5.3.14);
  (M8) Lemma 5.4.4 on every proper edge mark (no removable ribbon of size jk(E) in W, Wbar, Obar);
  (M7) Thm 5.4.1: an edge mark is proper  <=>  the only ribbons of size k(E) removable on the left
       (right) from E are K_up (K_down).  W^O^W marks are tested through the transpose.
Firing: the improper I-III edge marks are the control of (M7): each must exhibit an extra removable
k(E)-ribbon (a loose end) -- counted, must be > 0 and equal to the number of improper edge marks.
Hypothesis V failures among the legal edge marks are counted (the domain the thesis adds over MvW 3.31).
Usage: python3 check_thesis_marks.py NMAX
"""
import sys
import time
from collections import Counter
import _hopf_shapes_lib as L

eng = L.eng


def transpose_mark(E, mk):
    T = lambda S: frozenset((j, i) for i, j in S)  # noqa: E731
    Et = T(E)
    v = mk['v']
    return Et, dict(Wsw=T(mk['Wne']), Wne=T(mk['Wsw']), case={'a': 'b', 'b': 'a', 'c': 'c', 'd': 'd'}[mk['case']],
                    v=(-v[1], -v[0]))


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    t0 = time.time()
    cnt = Counter()
    cnt['M5 I,II,O-connected but III fails'] = 0
    vfail_examples = []
    for n in range(3, NMAX + 1):
        shapes = L.connected_shapes(n, n)
        for E in shapes:
            E = frozenset(E)
            mks = L.all_marks(E)
            legal_eng = {(m[0], m[1], m[2]) for m in eng.w_candidates(E) if m[0]}
            mine = set()
            for mk in mks:
                if mk['hypI'] and mk['hypIII'] and mk['iv_eng']:
                    mine.add((mk['Wsw'], mk['Wne'], mk['case']))
            assert mine == legal_eng, ('M1', sorted(E))
            for mk in mks:
                if not mk['hypI']:
                    continue
                if not mk['hypIII']:
                    cnt['M5 I,II,O-connected but III fails'] += 1
                    continue
                cnt['I-III marks'] += 1
                ta = L.thesis_attachment(E, mk['Wsw'], mk['Wne'])
                assert ta == mk['case'], ('M2', sorted(E), ta, mk['case'])
                bars = L.thesis_bars(E, mk['Wsw'], mk['Wne'], mk['v'])
                assert bars['proper'] == mk['iv_eng'], ('M3', sorted(E), mk['case'])
                assert bars['proper_und'] == bars['proper'], ('M3und', sorted(E))
                E1, E2 = bars['E1'], bars['E2']
                Wmid = frozenset(mk['Wne'])
                c = mk['case']
                if c == 'a':
                    assert bars['Wbar'] <= E1 and bars['Wund'] <= E2, 'M4a'
                elif c == 'b':
                    assert bars['Wund'] <= E1 and bars['Wbar'] <= E2, 'M4b'
                elif c == 'c':
                    assert bars['Wbar'] <= Wmid, 'M4c'
                else:
                    assert bars['Wund'] <= Wmid, 'M4d'
                cnt['M4 containments'] += 1
                if mk['iv_eng']:
                    cnt['legal I-IV marks (W nonempty), case ' + c] += 1
                    if c in 'ab' and not mk['V']:
                        cnt['legal edge marks FAILING V'] += 1
                        if len(vfail_examples) < 6:
                            vfail_examples.append((n, sorted(E), sorted(mk['Wsw']), c))
                if c not in 'ab':
                    continue
                # (M6), (M7) on the W->O->W representative
                EE, mm = (E, mk) if c == 'a' else transpose_mark(E, mk)
                bb = L.thesis_bars(EE, mm['Wsw'], mm['Wne'], mm['v'])
                Ku, Kd, info = L.key_ribbons_edge_a(EE, mm, bb)
                assert info['Wbar_ne_in_E'] and info['Wund_sw_in_E'], 'Sec 5.3.3 containment'
                k = mm['v'][1] - mm['v'][0]
                assert L.is_ribbon(Ku) and L.is_ribbon(Kd), 'M6 ribbon'
                assert len(Ku) == len(Kd) == k, ('M6 size', len(Ku), len(Kd), k)
                assert (L.nrows(Ku), L.ncols(Ku)) == (L.nrows(Kd), L.ncols(Kd)), 'Lemma 5.3.13'
                assert L.is_ideal(Ku, EE) and L.is_filter(Kd, EE), 'M6 removability'
                left = L.removable_ribbons(EE, k, 'L')
                right = L.removable_ribbons(EE, k, 'R')
                only_keys = (left == [Ku]) and (right == [Kd])
                assert Ku in left and Kd in right
                assert only_keys == bb['proper'], ('Thm 5.4.1', sorted(E), c, bb['proper'])
                cnt['Thm 5.4.1 tested (edge I-III marks)'] += 1
                if bb['proper']:
                    # Lemma 5.4.4: W, Wbar, Obar have no removable ribbons of size divisible by k(E)
                    for piece in (frozenset(mm['Wsw']), bb['Wbar'], bb['Obar']):
                        for j in range(1, len(piece) // k + 1):
                            assert not L.removable_ribbons(piece, j * k, 'L'), 'Lemma 5.4.4'
                            assert not L.removable_ribbons(piece, j * k, 'R'), 'Lemma 5.4.4'
                    cnt['Lemma 5.4.4 checked (proper edge marks)'] += 1
                if not bb['proper']:
                    cnt['CONTROL: improper edge marks, loose end found'] += 1
        print(f'PROGRESS n={n} shapes={len(shapes)} {dict(cnt)} t={time.time()-t0:.0f}s', flush=True)
    assert cnt['CONTROL: improper edge marks, loose end found'] > 0
    print('V-failing examples:', vfail_examples)
    for k in sorted(cnt):
        print(f'  {k}: {cnt[k]}')
    print(f'ALL PASS (inners 3..{NMAX} cells) t={time.time()-t0:.0f}s')


if __name__ == '__main__':
    main()
