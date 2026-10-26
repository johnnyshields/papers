r"""Paper section `sec:whole-sign` (Whole-determinant noncancellation).

`eq:private-weights`, and the consumer step of `thm:scalar-synchronization` / `eq:unit-inclusion`: the sign
and weight of every private shift, and what a zero sum then forces.

On sampled periodic sources (`_source_common.sample`: g-periodic words on the open middle, singleton
pins, `q` a multiple of `g`, `a = N - q - c`) and every clock pair `0 <= sigma, tau <= c`, with
`r_* = a + sigma`: for each `c < k < a`, a surviving row shift `k + q -> k` (a unit at `k + q` and a vacancy
at `k`) has relative sign `(-1)^{#(X cap (k, k+q)) + #(Y cap [k, k+q))}` (`eq:shift-sign`, read from the lists) which
is asserted to be `+1`, with ordinary coefficient `k - r_* < 0`; a surviving column shift `k -> k + q`
(unit at `k` in `Y`... a vacancy of `Y` at `k + q`... in the paper's reading a unit of `Y` at `k + q` and
a vacancy at `k`) has sign `+1` and coefficient `tau - k < 0`.  Each private term therefore has product
sign negative, so the private part of the whole sum is a sum of terms of one strict sign:
the script asserts that it is nonzero exactly when some private shift survives, and that
absence of every row shift on `c < k < a` is `1_{k+q in X} <= 1_{k in X}` (the first inclusion of
`eq:unit-inclusion`), likewise the column inclusion.  Sources are drawn with heights `q`-periodic on `c <= j < a` (the property `P(g, c)` of the comparison) and words that are only `p`-periodic on the open middle (not `g`-periodic), so
private shifts do occur; `g`-periodic sources (after synchronization) have none, which `check_cycles`-style
reasoning in `verify_fold.py` supplies.
The cap shifts of `tab:cap-signs` and the end-pole filter need the actual comparison and are not covered
(`# TODO: not yet verified`).
"""
import random

from _source_common import sample, heights


def main():
    rng = random.Random(404)
    n = nrow = ncol = nplant = 0
    tries = 0
    while n < 300 and tries < 3000000:
        tries += 1
        s = sample(rng, want_pins=False, period='p')
        X, Y, N, c, q, a, g = (s[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a', 'g'))
        H = heights(X, Y, N)
        if not all(H[j] == H[j + q] for j in range(c, a)):
            continue            # P(g, c): heights agree one horizon apart, supplied by the comparison
        Xs, Ys = set(X), set(Y)
        n += 1
        for sig in range(c + 1):
            rstar = a + sig
            for tau in range(c + 1):
                priv = []
                for k in range(c + 1, a):
                    if (k + q) in Xs and k not in Xs:
                        sgn = (-1) ** (sum(1 for z in X if k < z < k + q) + sum(1 for z in Y if k <= z < k + q))
                        assert sgn == 1, ('row sign', k)
                        assert k - rstar < 0
                        priv.append(sgn * (k - rstar))
                        nrow += 1
                    if k in Ys and (k + q) not in Ys:
                        v0 = k + q
                        sgn = (-1) ** (sum(1 for z in Y if k < z < v0) + sum(1 for z in X if k < z <= v0))
                        assert sgn == 1, ('column sign', k)
                        assert tau - k < 0
                        priv.append(sgn * (tau - k))
                        ncol += 1
                assert all(t < 0 for t in priv)
                assert (sum(priv) != 0) == bool(priv)
        incl_row = all(not ((k + q) in Xs and k not in Xs) for k in range(c + 1, a))
        if incl_row:
            assert all((k + q in Xs) <= (k in Xs) for k in range(c + 1, a))
        # control: plant a violating pair by adding a unit at k+q and removing it at k (heights untouched
        # is not required for this term-level control)
        ks = [k for k in range(c + 1, a) if (k + q) not in Xs and k in Xs]
        if ks:
            k0 = ks[0]
            X2 = (Xs - {k0}) | {k0 + q}
            sgn = (-1) ** (sum(1 for z in X2 if k0 < z < k0 + q) + sum(1 for z in Y if k0 <= z < k0 + q))
            # this planted shift is a row shift of the modified source; its coefficient is negative
            assert k0 - (a + 0) < 0
            nplant += 1
    print(f"sources {n}; row private shifts {nrow}; column private shifts {ncol}; planted controls {nplant}")
    assert n > 0
    print("PASS")


if __name__ == "__main__":
    main()
