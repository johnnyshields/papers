r"""Paper section `app:aligned` (`lem:conormal-caps`): the permitted representative.

The lemma asserts that the first and last `q` windows of the original `E` are the windows of ONE
representative: the original marked `U`, or its simultaneous half-turn.  Test on composites
`E = U o X`, where `U` is the marked inner (its empty mark composes the outer `X`) and `X` is a
connected skew diagram, a half-turn of one, or a further composite `V^e o D^f` with each factor
possibly reversed.  Check on every instance that

* the representative `U` (or `rot U` when the inner itself is reversed) satisfies both end
  windows at once, `bw(E, U)`;
* no instance has the "mixed" shape, in which one orientation serves the first window and the
  other the last (first window of `U` together with the last window of `rot U` failing).

Nested-factor transports (`check_end_window_transport.py`) are a different mechanism and are not
tested here: those examples do not satisfy the original source-minimal aligned hypotheses.
"""
import random

from check_end_window_transport import bw, comp, rot, win
from check_row_probe_caps import connected, is_skew, random_skew


def good(S):
    return S is not None and is_skew(S) and connected(S)


def draw(rng, lo=2, hi=6):
    while True:
        S = random_skew(rng, rng.randint(1, 3))
        if good(S) and lo <= len(S) <= hi:
            return S


def main():
    rng = random.Random(7)
    count = mixed = 0
    for _ in range(1500):
        U, V, D = draw(rng), draw(rng), draw(rng)
        for ei, ev, ed in [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1), (0, 1, 1)]:
            u = rot(U) if ei else U
            v = rot(V) if ev else V
            d = rot(D) if ed else D
            for X in (d, comp(v, d)):
                if X is None or not good(X):
                    continue
                E = comp(u, X)
                if not good(E):
                    continue
                assert bw(E, u), (sorted(u), sorted(X))
                count += 1
                mixed += int(win(E, u) and win(rot(E), u) and not bw(E, u))
    assert count > 200, count
    assert mixed == 0, mixed
    print("composites tested:", count, "; the inner represents both ends in all; mixed:", mixed)


if __name__ == "__main__":
    main()
