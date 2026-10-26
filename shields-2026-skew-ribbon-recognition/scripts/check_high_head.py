r"""The arithmetic of the maximal-head comparison (ge:high-head).

Paper section `app:boundary` (Boundary constructions and exceptional entrances), ge:high-head.

Reading: the proposition is a descent from a comparison the main theorem excludes; what is tested
is the inequality chain its proof derives from the stated head hypotheses, on parameter sets
whose mark data are real.  (r, v, s, t) range over every legal case (d) mark of every connected
diagram up to J_CELLS cells (phases t < s <= v), w over 0 <= w < v with delta = v - w > 0,
g = gcd(r, delta) >= 2, g not dividing v, N = r + v, and every head H with v < H < N and
2H >= N + delta + |v - s - t|; L = N - H, D = H - v.  For every such tuple:

* L + D = r, A = H - L >= delta >= g, v > delta (equivalently w >= 1), r >= 2g, H > 2g;
* for H > r: min(L, D) < H/2, H - max(L, D) > min(L, D), and H - min(L, D) >= f - 1 for every
  f <= H/2;
* the same chain on the whole box 0 <= t < s <= v < r <= BOX, so the count does not depend on
  which marks the cell bound reaches.
The control drops g not dividing v: the tuples then include w = 0, where v > delta fails.

Uncovered: the four-cut words, the lower-root exits through ge:zero-port, ge:aligned-finish and
ge:two-window, the mixed-orientation reduction, and H < r.
"""
from math import gcd

from _gluing_common import intersection_mark, legal
from check_two_copy_flags import diagrams, phases

J_CELLS = 9
BOX = 16


def main():
    real = set()
    for J in diagrams(J_CELLS):
        for cell in J:
            try:
                mk = intersection_mark(J, cell)
            except AssertionError:
                continue
            if mk.case == 'd' and legal(mk) and mk.width > 0:
                s, t = phases(mk)
                real.add((mk.period, mk.width, s, t))
    print(f'distinct (r, v, s, t) of case (d) marks: {len(real)}')
    box = {(r, v, s, t) for r in range(2, BOX + 1) for v in range(1, r) for s in range(1, v + 1)
           for t in range(0, s)}
    assert real <= box, sorted(real - box)
    count = control = 0
    for r, v, s, t in sorted(box):
        N = r + v
        for w in range(0, v):
            delta = v - w
            g = gcd(r, delta)
            if g < 2:
                continue
            for H in range(v + 1, N):
                if 2 * H < N + delta + abs(v - s - t):
                    continue
                L, D = N - H, H - v
                assert L + D == r
                if v % g == 0:
                    control += w == 0
                    continue
                count += 1
                assert H - L >= delta >= g
                assert v > delta and w >= 1
                assert r >= 2 * g, (r, v, w, H)
                assert H > 2 * g, (r, v, w, H)
                if H > r:
                    b0, c0 = min(L, D), max(L, D)
                    assert 2 * b0 < H and H - c0 > b0
                    assert all(H - b0 >= f - 1 for f in range(1, H // 2 + 1))
    print(f'tuples satisfying the hypotheses: {count}; with g | v (control): {control}')
    assert count > 200 and control > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
