r"""Paper section `app:aligned` (`lem:conormal-caps`, noncell realization): orientation of the end windows.

For supplied empty composites E = J o_eta U, check the first-window list inclusions and
exhibit cases where those inclusions fail after rotating E while keeping U fixed.
This tests the need to transport the marked frame.  It does not exhibit a counterexample
satisfying the original aligned source-minimal hypotheses.

The original-minimum cap lemma obtains one representative of the original full marked U
from its smaller-area fiber and uses that same representative at both ends.
"""
import random

from check_end_window_lists import compose
from check_row_probe_caps import (betas, connected, is_skew, legal_marks, normalize, random_skew)


def rot(S):
    return normalize({(-a, -b) for (a, b) in S})


def windows(E, U):
    xE, zE = betas(E)
    xU, zU = betas(U)
    q = xU[0]
    return all(x in set(xU) for x in xE if 0 < x < q) and set(zU) <= set(zE)


def main():
    rng = random.Random(11)
    ok, bad, example = 0, 0, None
    seen = set()
    for _ in range(4000):
        U = random_skew(rng, rng.randint(1, 4))
        if U in seen or not is_skew(U) or not connected(U) or not 2 <= len(U) <= 9:
            continue
        seen.add(U)
        for w, v, ph in legal_marks(U):
            if w != 0:
                continue
            for _ in range(3):
                J = random_skew(rng, rng.randint(1, 3))
                if not is_skew(J) or not connected(J):
                    continue
                xJ, _z = betas(J)
                if xJ[0] < 2:
                    continue
                E = compose(J, U, v)
                if not is_skew(E) or not connected(E):
                    continue
                assert windows(E, U)
                ok += 1
                if not windows(rot(E), U):
                    bad += 1
                    example = example or (sorted(U), sorted(J), v)
    assert ok > 50 and bad > 0, (ok, bad)
    print("unrotated windows hold in", ok, "composites; fail for the half-turn in", bad,
          "; first:", example)


if __name__ == "__main__":
    main()
