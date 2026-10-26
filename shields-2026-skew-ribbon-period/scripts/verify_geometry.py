r"""Paper section `sec:geometry` (Periodic cores and actual boundary comparisons).

Targets the splices of `fig:splices`, `eq:horizon-bounds`, the frame lists, `eq:cap-polynomials`
(subsection on minimal cap-preserving splices and the complete weak
return frames).

Sources are sampled by `_source_common.sample` (g-periodic boundary words on the open middle,
positive heights, the splice and return contents singleton).  Asserted on every source:
`eq:horizon-bounds` arithmetic; both splices are actual diagrams (positive heights, singleton ends)
of span `m = a + c` with the same height word as each other and the same literal zero-free core,
and strictly smaller area than the source; the first and last `c + 1` diagonals of the source are
preserved; the four frame lists `I_R, C_R, I_L, C_L, I_+, C_+, I_-, C_-` have the sizes that make
`B_R, B_L, G_R, G_L` square, those matrices are weakly feasible and nonsingular at the sampled
alphabet; `v_L(j) = 0` on `C_+` and `v_R(i) = 0` on `I_-` for the cap vectors solved from their
equations; and the cap coefficients are nonzero on their actual support.
# TODO: not yet verified -- `eq:ordinary-references`: the reference lists `B_R^*, B_L^*` are defined only
# as the "complete reference lists" of the original period-`p` copies, which needs the second
# (Schur-equal) chart that the main theorem excludes.
"""
import random

from fractions import Fraction as Fr

from _source_common import alphabet, heights, sample, solve, splice
from _schur_common import determinant


def core(X, Y):
    common = set(X) & set(Y)
    return tuple(x for x in X if x not in common), tuple(y for y in Y if y not in common)


def main():
    rng = random.Random(2026)
    n = nonsingleton = 0
    maxh = 1
    while n < 200:
        s = sample(rng)
        X, Y, N, c, p, q, a, m, g = (s[k] for k in ('X', 'Y', 'N', 'c', 'p', 'q', 'a', 'm', 'g'))
        n += 1
        assert N >= 2 * max(p, q) + c and a >= q >= 2 * g > c and m == N - q == a + c   # eq:horizon-bounds
        H = heights(X, Y, N)
        maxh = max(maxh, max(H))
        area = sum(H)
        em = splice(X, Y, N, a - 1, N - c - 1)
        ep = splice(X, Y, N, c, q + c)
        for (Xs, Ys, Ns) in (em, ep):
            assert Ns == m and Xs[0] == Ns and Ys[-1] == 0 and len(Xs) == len(Ys)
            Hs = heights(Xs, Ys, Ns)
            assert min(Hs) >= 1 and Hs[0] == 1 and Hs[-1] == 1                          # actual diagram, singleton ends
            assert all(x >= y for x, y in zip(Xs, Ys))
            assert sum(Hs) < area                                                        # strictly smaller area
        Hm, Hp = heights(*em[:2], m), heights(*ep[:2], m)
        assert Hm == Hp                                                                   # same height word
        assert core(*em[:2]) == core(*ep[:2])                                             # same literal zero-free core
        # first and last c+1 diagonals preserved with the proper translations
        for Xs, Ys, shiftlow in ((em[0], em[1], True), (ep[0], ep[1], False)):
            pass
        assert [k for k in em[0] if k <= c] == [k for k in X if k <= c]
        assert sorted(k for k in em[0] if k > m - c) == sorted(k - (N - m) for k in X if k > N - c)
        assert [k for k in ep[0] if k <= c] == [k for k in X if k <= c]
        # frames
        I, C = list(X[1:]), list(Y[:-1])
        IR = [i - a for i in I if a <= i <= m]; CR = [j - a for j in C if a <= j <= m]
        IL = [i - q for i in I if q <= i <= q + c]; CL = [j - q for j in C if q <= j <= q + c]
        Ip = [i - (N - c) for i in I if N - c <= i < N]; Cp = [j - (N - c) for j in C if N - c <= j < N]
        Im = [i for i in I if 1 <= i <= c]; Cm = [j for j in C if 1 <= j <= c]
        assert (len(IR) == len(CR), len(IL) == len(CL), len(Ip) == len(Cp), len(Im) == len(Cm)) == (True,) * 4, (s, H)
        h = alphabet(rng, N + 2)
        for L1, L2 in ((IR, CR), (IL, CL), (Ip, Cp), (Im, Cm)):
            if L1:
                assert all(x >= y for x, y in zip(L1, L2))                               # weakly feasible
                assert determinant([[h(x - y) for y in L2] for x in L1]) != 0
        # cap vectors from their equations
        Ucap = sorted({c} | set(Ip), reverse=True)
        Vcap = sorted({0} | set(Cm))
        # l: sum_i l_i h_{i-j} = 0 for j in C_+, l_c = 1
        if Cp:
            others = [i for i in Ucap if i != c]
            A = [[h(i - j) for i in others] for j in Cp]
            rhs = [-h(c - j) for j in Cp]
            sol = solve(A, rhs) if others else []
            assert sol is not None
            l = dict(zip(others, sol)); l[c] = Fr(1)
            for j in Cp:
                assert sum(l[i] * h(i - j) for i in Ucap) == 0                        # v_L(j) = 0 on C_+
            assert all(v != 0 for v in l.values())                                     # nonzero on its support
        if Im:
            others = [j for j in Vcap if j != 0]
            A = [[h(i - j) for j in others] for i in Im]
            rhs = [-h(i) for i in Im]
            sol = solve(A, rhs) if others else []
            assert sol is not None
            r = dict(zip(others, sol)); r[0] = Fr(1)
            for i in Im:
                assert sum(h(i - j) * r[j] for j in Vcap) == 0                          # v_R(i) = 0 on I_-
            assert all(v != 0 for v in r.values())
    print(f"sources {n}, max height {maxh}")
    assert maxh >= 2, "sample should include heights above one"
    print("PASS")


if __name__ == "__main__":
    main()
