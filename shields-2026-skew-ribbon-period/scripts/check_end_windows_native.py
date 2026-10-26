r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Native window products of row probes, including the one-cell probe (`lem:conormal-caps`).

Section: app:aligned, lem:conormal-caps (the end windows `g_{U,-} g_{U,+}`, `RowProbeCapIndep`,
and the cuts of `U` itself for a one-cell occurrence, `OccurrenceData`).

For every legal mark of a random inner E, period q and width w, and the row probes Row_K o U,
K = 1, 2, 3, the script asserts, with exact rational arithmetic at random points whose labels
below q are shared and whose labels from q are resampled:
  * the one-cell probe U = Row_1 o U has singleton cuts H(q - 1) = 1 and H(w) = H(N - q) = 1;
  * the coefficients [z^t] R L, t < q, of the endpoint coframe product are the same for K = 1, 2, 3
    and do not move when the labels from q are resampled;
  * the 180-degree rotation of the one-cell probe has the same coefficients (the cap product is
    symmetric under reflection).
"""
import random
from fractions import Fraction

from check_row_probe_caps import (betas, connected, coframe_product, height, is_skew,
                                  legal_marks, normalize, probe, random_skew)


def rotate(cells):
    return normalize({(-i, -j) for i, j in cells})


def main():
    rng = random.Random(11)
    tested = fails = 0
    seen = set()
    for _ in range(4000):
        E = random_skew(rng, rng.randint(1, 3))
        if E in seen or not is_skew(E) or not connected(E) or len(E) < 2:
            continue
        seen.add(E)
        for w, v, ph in legal_marks(E):
            cs = [j - i for i, j in E]
            q = max(cs) - min(cs) + 1 - w
            if q < 2:
                continue
            lowv = {m: Fraction(rng.randint(-9, 9), rng.randint(1, 5)) for m in range(1, q)}
            probes = {K: probe(E, v, K) for K in (1, 2, 3)}
            probes['rot'] = rotate(probes[1])
            if not all(is_skew(G) and connected(G) for G in probes.values()):
                continue
            xi, ze = betas(probes[1])
            N = xi[0]
            assert N == q + w, (E, w, v, N)
            if [height(xi, ze, q - 1), height(xi, ze, N - q)] != [1, 1]:
                fails += 1
                print('FAIL cuts of U', sorted(E), 'w', w, 'v', v)
                continue
            prods = {}
            for key, G in probes.items():
                vals = []
                for _ in range(2):
                    hv = dict(lowv)
                    big = betas(G)[0][0]
                    for m in range(q, big + 1):
                        hv[m] = Fraction(rng.randint(-9, 9), rng.randint(1, 5))
                    try:
                        prod, *_ = coframe_product(G, hv)
                    except (StopIteration, ZeroDivisionError):
                        prod = None
                    vals.append(prod)
                if None in vals:
                    prods = None
                    break
                if vals[0][:q] != vals[1][:q]:
                    fails += 1
                    print('FAIL low product moves', key, sorted(E), 'w', w, 'v', v)
                prods[key] = tuple(vals[0][:q])
            if prods is None:
                continue
            tested += 1
            if len(set(prods.values())) > 1:
                fails += 1
                print('FAIL window product depends on the probe', sorted(E), 'w', w, 'v', v)
    print('tested', tested, 'failures', fails, 'inners', len(seen))
    assert tested > 50
    assert fails == 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
