r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Low cap coefficients force singleton cuts.

Section: app:aligned, lem:conormal-caps (the residue paragraph after eq:whole-cap-product).

For a connected skew diagram F of span N with full beta lists X = (N, I), Y = (C, 0), the
endpoint coframes are R = 1 - sum u_j z^{C_j}, L = 1 - sum v_i z^{N - I_i}, with u = A^-1 (h_i),
v = (h_{N-c}) A^-1, A = JT(I, C).  For every q with 2 q <= N the script asserts that the
coefficients [z^t] R L, t < q, are unchanged by resampling every label h_m, m >= q (exact rational
arithmetic, three samples) exactly when the label heights at q - 1 and N - q are both one.  The
direction 'heights one => fixed' is profile_cap_low; the converse is CapLowCuts.
"""
import random
from fractions import Fraction

from check_row_probe_caps import random_skew, is_skew, connected, betas, coframe_product, height


def main():
    rng = random.Random(3)
    total = 0
    seen = set()
    for _ in range(6000):
        F = random_skew(rng, rng.randint(2, 5))
        if F in seen or not is_skew(F) or not connected(F):
            continue
        seen.add(F)
        xi, ze = betas(F)
        N = xi[0]
        for q in range(2, N // 2 + 1):
            lo = {m: Fraction(rng.randint(-9, 9), rng.randint(1, 5)) for m in range(1, q)}
            vals = []
            for _ in range(3):
                hv = dict(lo)
                for m in range(q, N + 1):
                    hv[m] = Fraction(rng.randint(-20, 20), rng.randint(1, 7))
                try:
                    vals.append(coframe_product(F, hv)[0][:q])
                except (StopIteration, ZeroDivisionError):
                    vals.append(None)
            if None in vals:
                continue
            fixed = vals[0] == vals[1] == vals[2]
            cuts = (height(xi, ze, q - 1), height(xi, ze, N - q)) == (1, 1)
            assert fixed == cuts, (sorted(F), q, fixed, cuts)
            total += 1
    print('cases', total, 'diagrams', len(seen))
    assert total > 1000
    print('ALL PASS')


if __name__ == '__main__':
    main()
