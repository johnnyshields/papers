r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Positive coincident section of prop:noncell-realization (eq:positive-section, eq:exact-corner-transport,
eq:phi).  Census of positive coincident legal marks (rho = tau, 0 < tau < u, ordinary reading).
Each mark is classified by the coordinate system in which Phi(c_j) = mu xi^j Y_j (c = h or e), and the
script asserts the DICHOTOMY: every mark calibrates in exactly one of the h-/e-coordinates, the ratio
Phi(c_1)/Y_1 is independent of the free data (S, Y), and the type is read off the mark by
v_0 = 1 - r(E) (e-coordinates) versus v_0 = 2 - r(E) (h-coordinates), r(E) = number of rows of E.
Also asserts the type is stable under a second choice of free data.
"""
import random
from fractions import Fraction as Fr
from check_positive_section import run, classify
from check_row_probe_caps import legal_marks, probe, is_skew, connected, random_skew, content


def ratios(phi, seed):
    rng = random.Random(seed)
    Y = [Fr(1)] + [Fr(rng.randint(1, 7), rng.randint(1, 3)) for _ in range(3)]
    S = [Fr(1)] + [Fr(rng.randint(-6, 6), rng.randint(1, 3)) for _ in range(3)]
    p = phi(Y, S)
    return p[0] / Y[1]


def main(marks=60):
    rng = random.Random(11); seen = set(); tries = 0
    stat = {'e': 0, 'h': 0, 'neither': 0, 'degenerate': 0}; bad = []
    while sum(stat.values()) < marks and tries < 200000:
        tries += 1
        E = random_skew(rng, rng.randint(2, 4))
        if E in seen or not is_skew(E) or not connected(E) or not 2 <= len(E) <= 9:
            continue
        seen.add(E)
        rows = len({x[0] for x in E})
        for w, v, ph in legal_marks(E):
            if ph is None or ph[0] != ph[1] or not 0 < ph[0] < w:
                continue
            if not all(is_skew(probe(E, v, j)) and connected(probe(E, v, j)) for j in (1, 2, 3)):
                continue
            phi = None
            for seed in range(1, 30):
                phi = run(E, w, v, ph[0], seed)
                if phi:
                    break
            if not phi:
                continue
            t = classify(phi, 5); t2 = classify(phi, 17)
            stat[t] += 1
            if t == 'neither' or t != t2 and 'degenerate' not in (t, t2):
                bad.append((sorted(E), w, v, ph, t, t2)); continue
            if t in ('e', 'h'):
                assert v[0] in (1 - rows, 2 - rows), (sorted(E), v, rows)
                assert t == ('e' if v[0] == 1 - rows else 'h'), (t, sorted(E), w, v)
                # ratio Phi(h_1)/Y_1 (resp. Phi(e_1)/Y_1 = same) independent of free data
                assert ratios(phi, 3) == ratios(phi, 4), (sorted(E), w, v)
    print('census', stat, 'marks classified, E seen', len(seen))
    if bad:
        bad.sort(key=lambda b: len(b[0]))
        print('COUNTEREXAMPLES (smallest first):', bad[:3])
    assert not bad and stat['e'] > 0 and stat['h'] > 0, (stat, bad[:1])
    print('PASS: dichotomy holds; type = e iff v_0 = 1 - r(E), h iff v_0 = 2 - r(E)')


if __name__ == '__main__':
    main()
