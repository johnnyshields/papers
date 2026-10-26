r"""Paper section `app:aligned` (prop:noncell-realization, eq:capped-core-quotient).

Residue extraction on supplied nested empty-mark composites.  With C_U(D) denoting
composition of D through the horizontal empty mark on U, form
E = C_U1(C_U2prime(J)), where U2prime is U2 or its half-turn.  Check that the entries of
both beta lists divisible by d1*d2 are exactly d1*d2 times the lists of J.

This models preservation of the empty residue invariant.  It does not assert that
prop:class-quotient alone produces a literal composite: that proposition gives a
whole-function equality, whereas the strengthened literal argument also retains matched
complete end windows.
"""
import random
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from check_empty_source_lists import (betas, compose_empty, is_skew_connected,  # noqa: E402
                                      random_skew, span)


def rot(cells):
    m = {(-i, -j) for i, j in cells}
    mi = min(i for i, _ in m)
    mj = min(j for _, j in m)
    return {(i - mi, j - mj) for i, j in m}


def main():
    rng = random.Random(5)
    n = [0, 0]
    for _ in range(8000):
        J = random_skew(rng, rng.randint(1, 3), 3)
        U1 = random_skew(rng, rng.randint(1, 3), 3)
        U2 = random_skew(rng, rng.randint(1, 3), 3)
        if len(U1) < 2 or len(U2) < 2:
            continue
        for k, U2p in enumerate((U2, rot(U2))):
            V, q2 = compose_empty(J, U2p)
            if not is_skew_connected(V):
                continue
            E, q1 = compose_empty(V, U1)
            if not is_skew_connected(E):
                continue
            q = q1 * q2
            XJ, YJ = betas(J)
            XE, YE = betas(E)
            assert span(E) == span(J) * q
            assert sorted(x for x in XE if x % q == 0) == sorted(q * x for x in XJ)
            assert sorted(y for y in YE if y % q == 0) == sorted(q * y for y in YJ)
            n[k] += 1
    assert n[0] > 300 and n[1] > 300, n
    print(f"ok: {n[0]} plain, {n[1]} rotated inner pairs")


if __name__ == "__main__":
    main()
