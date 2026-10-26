r"""Paper section `app:alternative` (An alternative geometric realization of the scalar).

`eq:modified-cap-table`, ordinary row `00`.  The table replaces the upper cap of `sminus` by
`(I_R + sigma, C_R)` and the lower cap of `splus` by `(I_L, C_L + tau)`.  `sigma`, `tau` are SOLVED from the
table's own requirement: the new upper difference `1_{I_R} - 1_{C_R} + 1_sigma` equals the original cap
difference `1_{U_cap} - 1_{C_+}` (dually below), solvable exactly when the original cap difference is
`1_{I_R} - 1_{C_R}` plus one point.

Construction attempt, backwards: sources are drawn with `p`-periodic words and, as the only filter, the
solvability condition above (the earlier forward search that also demanded every singleton pin of the
comparison found no solution in 60,000 samples, so the pins are NOT imposed here and the sources are
not comparison data).  On each solvable source the script asserts: the new lists are strictly decreasing
and `sigma notin I_R`, `tau notin C_L`; rectangular cardinalities are unchanged; the new differences equal
the old cap differences pointwise; and the modified upper block, spliced into the source's `sminus`
word at positions `a + u`, keeps the old coface's height word below `a`.
The mixed rows `10`, `01` and the identification of `sigma`, `tau` with the observed clocks need the comparison.
# TODO: not yet verified -- rows `mixed 10` and `mixed 01`; the height word of the modified coface above `a`.
"""
import random

from _source_common import heights, sample


def main():
    rng = random.Random(8)
    n = nsol = 0
    while nsol < 40 and n < 40000:
        n += 1
        s = sample(rng, want_pins=False, period='p')
        X, Y, N, c, q, a, m = (s[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a', 'm'))
        I, C = set(X) - {N}, set(Y) - {0}
        IR = {i - a for i in I if a <= i <= m}; CR = {j - a for j in C if a <= j <= m}
        IL = {i - q for i in I if q <= i <= q + c}; CL = {j - q for j in C if q <= j <= q + c}
        Ip = {i - (N - c) for i in I if N - c <= i < N}; Cp = {j - (N - c) for j in C if N - c <= j < N}
        Im = {i for i in I if 1 <= i <= c}; Cm = {j for j in C if 1 <= j <= c}
        Ucap, Vcap = {c} | Ip, {0} | Cm
        R = range(c + 1)
        dU = {u: (u in Ucap) - (u in Cp) for u in R}
        extra = {u: dU[u] - ((u in IR) - (u in CR)) for u in R}
        dV = {u: (u in Vcap) - (u in Im) for u in R}
        extraL = {u: dV[u] - ((u in CL) - (u in IL)) for u in R}
        pts = [u for u in R if extra[u] != 0]
        ptsL = [u for u in R if extraL[u] != 0]
        if not (len(pts) == 1 and extra[pts[0]] == 1 and len(ptsL) == 1 and extraL[ptsL[0]] == 1):
            continue
        sig, tau = pts[0], ptsL[0]
        if sig in IR or tau in CL:
            continue
        nsol += 1
        newIR, newCL = IR | {sig}, CL | {tau}
        assert len(newIR) - len(CR) == len(Ucap) - len(Cp)
        assert len(newCL) - len(IL) == len(Vcap) - len(Im)
        assert all(((u in newIR) - (u in CR)) == dU[u] for u in R)
        assert all(((u in newCL) - (u in IL)) == dV[u] for u in R)
        # modified upper block of sminus (positions a + u), the old block replaced
        H = heights(X, Y, N)
        Xm = set(X) - {x for x in X if a <= x <= m} | {a + u for u in newIR}
        Ym = set(Y) - {y for y in Y if a <= y <= m} | {a + u for u in CR}
        Hm = [sum(y <= k for y in Ym) - sum(x <= k for x in Xm) for k in range(a)]
        assert Hm == H[:a], ('height word below a changed', sorted(newIR))
    print(f"sources scanned {n}; solvable {nsol}")
    assert nsol > 0
    print("PASS")


if __name__ == "__main__":
    main()
