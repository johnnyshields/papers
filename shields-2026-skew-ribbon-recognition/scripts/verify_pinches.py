r"""Paper section `app:endpoints` (Endpoint scalars and ordinary reflection), ph:pinches.

For an actual positive upper mark of width 0 < w < v on a source E = V o_mu J whose finer mark mu
is ordinary (a) or mixed (d), with contacts (s, t) and delta = v - w, the lemma asserts

    s > w,   t < delta,   h_W(w) = h_W(delta - 1) = 1,

where W is the lower copy of mu and h_W(x) the number of cells of W on its content diagonal x.

Exhaustive over every connected finer J of at most CELLS cells, every legal case (a) or (d) mark
mu of J, every connected coarse V of span 3 to COARSE_CELLS cells, and every legal mark omega of
E = V o_mu J of positive width w < v of any attachment type.  The contacts (s, t) are read off the
actual marked diagonals of J (`check_two_copy_flags.phases`), the heights off the cell sets.  The
count of omegas by finer type is asserted positive for both, so neither case is vacuous.
"""
from _gluing_common import compose, content, is_connected_skew, legal, span
from check_two_copy_flags import diagrams, marks, phases

CELLS = 8
COARSE_CELLS = 5


def height(W, x):
    base = min(content(c) for c in W)
    return sum(1 for c in W if content(c) - base == x)


def main():
    coarse = [V for V in diagrams(COARSE_CELLS) if span(V) >= 3]
    seen = {'a': 0, 'd': 0}
    for J in diagrams(CELLS):
        for mu in marks(J):
            if mu.case not in 'ad' or not mu.lower:
                continue
            v = mu.width
            s, t = phases(mu)
            W = mu.lower
            for V in coarse:
                try:
                    E = compose(V, mu)
                except AssertionError:
                    continue
                if not is_connected_skew(E):
                    continue
                for om in marks(E):
                    if not (legal(om) and 0 < om.width < v):
                        continue
                    w = om.width
                    delta = v - w
                    seen[mu.case] += 1
                    assert s > w and t < delta, (sorted(J), sorted(W), s, t, w)
                    assert height(W, w) == 1 and height(W, delta - 1) == 1, \
                        (sorted(J), sorted(W), w)
    assert seen['a'] > 0 and seen['d'] > 0, seen
    print(f'ph:pinches: {seen["a"]} upper marks on ordinary (a) finers and {seen["d"]} on mixed (d) '
          f'finers, every one with s > w, t < delta, h_W(w) = h_W(delta - 1) = 1')
    print('ALL PASS')


if __name__ == '__main__':
    main()
