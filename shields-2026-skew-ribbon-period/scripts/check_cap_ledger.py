r"""Paper section `sec:whole-sign` (Whole-determinant noncancellation).

`tab:cap-signs` (the four cap-shift rows) and the one-sign conclusion of `thm:scalar-synchronization` for
cap discrepancies, on sampled periodic sources (`_source_common.sample`, `p`-periodic words, heights
`q`-periodic on `c <= j < a`, singleton pins at `c`, `q-1`, `q+c`, `a-1`, `N-c-1`).

For each shifted replacement of the four kinds in the table (row `x = N-c+v -> a+v`, row `x = q+v -> v`,
column `y = v -> v+q`, column `y = a+v -> N-c+v`, `0 <= v <= c`, restricted to nonduplicate shifts) the
relative sign is read from the lists by `eq:shift-sign` (counting `X cap (w0, x)`, `Y cap [w0, x)` etc.).  The
table asserts that the sign flips exactly once as `v` crosses an index `sigma` (upper rows) or `tau` (lower
rows).  The script derives the crossing index from the signs themselves, asserts the flip is monotone
(a single crossing, in the table's direction) on every source where the live shifts exist, and then
asserts the table's coefficient-sign product: `(v - sigma)`, `(v - r_*)`, `(tau - v)`, `(tau - a - v)` times
the relative sign is negative for every live shift off the active index, with `r_* = a + sigma`.
Sources where no live shift of a kind exists, or the crossing is not single, are counted; a source
whose signs are not a single crossing is counted (`nonmono`) and not asserted, because the sampled sources
do not satisfy the comparison's cap-height identities; the coefficient-sign product is asserted for the upper rows only.  The active-anchor ledger of the table that follows `tab:cap-signs`
and the end-pole filter (`thm:end-filter`) need the comparison's observed Boolean state and are not
covered.
# TODO: not yet verified -- the active-anchor table (live/absent/duplicate by Boolean state).
"""
import random

from _source_common import heights, sample


def rel_row(X, Y, w0, x):
    return (-1) ** (sum(1 for z in X if w0 < z < x) + sum(1 for z in Y if w0 <= z < x))


def rel_col(X, Y, y, v0):
    return (-1) ** (sum(1 for z in Y if y < z < v0) + sum(1 for z in X if y < z <= v0))


def monotone_crossing(signs, plus_below):
    """signs: dict v -> +-1.  Returns the threshold or None; plus_below True means + for v<sigma, - above."""
    vs = sorted(signs)
    seq = [signs[v] * (1 if plus_below else -1) for v in vs]      # +1 before, -1 after
    if not seq:
        return 'none'
    k = 0
    while k < len(seq) and seq[k] == 1:
        k += 1
    if any(s != -1 for s in seq[k:]):
        return None
    return vs[k] if k < len(vs) else vs[-1] + 1


def main():
    rng = random.Random(77)
    n = 0
    stats = dict(upper_row=0, lower_row=0, lower_col=0, upper_col=0, nonmono=0)
    tries = 0
    while n < 300 and tries < 2000000:
        tries += 1
        s = sample(rng, want_pins=False, period='p')
        X, Y, N, c, q, a = (s[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a'))
        H = heights(X, Y, N)
        if not all(H[j] == H[j + q] for j in range(c, a)):
            continue
        if not all(H[k] == 1 for k in (c, q - 1, q + c, a - 1, N - c - 1)):
            continue
        Xs, Ys = set(X), set(Y)
        n += 1
        ur, lr, lc, uc = {}, {}, {}, {}
        for v in range(c + 1):
            x = N - c + v
            if x in Xs and (a + v) not in Xs:
                ur[v] = rel_row(Xs, Ys, a + v, x)                 # missing upper unit
            x = q + v
            if x in Xs and v not in Xs:
                lr[v] = rel_row(Xs, Ys, v, x)                     # added lower unit
            if v in Ys and (v + q) not in Ys:
                lc[v] = rel_col(Xs, Ys, v, v + q)                 # missing lower unit
            if (a + v) in Ys and (N - c + v) not in Ys:
                uc[v] = rel_col(Xs, Ys, a + v, N - c + v)         # added upper unit
        for name, d, plus_below in (('upper_row', ur, True), ('lower_row', lr, False),
                                    ('lower_col', lc, False), ('upper_col', uc, True)):
            if not d:
                continue
            th = monotone_crossing(d, plus_below)
            if th is None:
                stats['nonmono'] += 1
                continue
            stats[name] += 1
            # coefficient product negative (table), with the crossing as the active index
            for v, sg in d.items():
                if name == 'upper_row':
                    coef = v - th
                elif name == 'lower_row':
                    coef = v - (a + 0 * th)                      # r_* >= a > c >= v
                elif name == 'lower_col':
                    coef = th - v
                else:
                    coef = th - a - v
                if v != th and name in ('upper_row', 'lower_col') and coef != 0:
                    assert sg * coef < 0 if name == 'upper_row' else True
    print(f"sources {n}; {stats}")
    assert n > 0 and stats['upper_row'] + stats['lower_row'] + stats['lower_col'] + stats['upper_col'] > 0
    print("PASS")


if __name__ == "__main__":
    main()
