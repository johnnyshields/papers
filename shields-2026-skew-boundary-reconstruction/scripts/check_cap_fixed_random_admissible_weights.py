r"""`def:convex-weight`, `prop:synchronization`, `cor:first-split-anchor`, `lem:tropical-balancing`,
`lem:tail-increase`, `thm:no-backflow`, `lem:marching`, `thm:cap-fixed-rigidity`,
`thm:equal-pair-rigidity`, `prop:monomial-prefix`: the cap-fixed statements at weights drawn at random
from the admissible class, so that no conclusion rests on the four named weights.

An admissible weight is fixed by positive increments that strictly increase.  Here the increments are
drawn as D(k) = D(k-1) + e_k with e_1 >= 1 and e_k >= 1 random integers (seeded, from 1 to 40), so each
omega is an exact integer function and the floor antecedent splits the population in both directions.
The population is every pair of distinct connected diagrams with a common inner boundary, row count and
top row, with no filter on row-length multisets.  Every weight is first validated by `admissible`.
"""
import random
from collections import defaultdict

from _census_common import Pair, admissible, argmin, buckets, gen_shapes, init_face, rows

SIZE_CAP = 12
ROW_CAP = 5
N_WEIGHTS = 24
SEED = 20260101


def random_weight(rng, kmax=40):
    inc, tot, vals = 0, 0, [0]
    for _ in range(kmax):
        inc += rng.randint(1, 40)
        tot += inc
        vals.append(tot)
    return lambda k, vals=vals: vals[k]


def main():
    rng = random.Random(SEED)
    weights = [random_weight(rng) for _ in range(N_WEIGHTS)]
    for om in weights:
        assert admissible(om, kmax=30)

    shapes = gen_shapes(SIZE_CAP, ROW_CAP)
    pairs = []
    for key, mem in sorted(buckets(shapes, lambda s: (s[1], s[0][0], len(s[0]))).items()):
        for a in range(len(mem)):
            for b in range(a + 1, len(mem)):
                pairs.append(Pair(mem[a], mem[b]))

    n_sync = n_back = n_chain = n_other = n_equal = 0
    by_v = defaultdict(int)
    for P in pairs:
        n, d, v, q = P.n, P.d, P.v, P.q
        same_multiset = sorted(rows(P.X)) == sorted(rows(P.Y))
        for om in weights:
            al = P.alpha(om)
            pos = [j for j in range(1, n + 1) if al[j] is not None]
            m_plus = min(al[j] for j in pos)
            if same_multiset:
                sx, sy = P.sigma("X", om), P.sigma("Y", om)
                for j in range(v + 1):
                    assert sx[j] == sy[j], ("synchronization", P.X, P.Y, j)
                assert sx[q] != sy[q]
                assert al[q] == min(sx[q], sy[q]), ("anchor", P.X, P.Y)
                n_sync += 1
                mins = []
                for i in range(v):
                    Fi = P.F(i, om, al)
                    mn, M = argmin(Fi)
                    assert len(M) >= 2 and max(M) <= q, ("balancing", P.X, P.Y, i, M)
                    mins.append(M)
                    for l in range(q + 1, n + 1):
                        if l in Fi:
                            assert Fi[l] > Fi[q], ("no-backflow", P.X, P.Y, i, l)
                            n_back += 1
                for i in range(v - 1):
                    assert max(mins[i + 1]) > max(mins[i]) and min(mins[i + 1]) >= max(mins[i])
                for sg, A in ((sx, P.AX), (sy, P.AY)):
                    for i in range(v):
                        for k in range(q, n):
                            f = lambda j: sg[j] + om(d[j] - A[i]) - om(d[j])
                            assert f(k + 1) > f(k), ("tail increase", P.X, P.Y, i, k)
            if al[0] is None or al[0] > m_plus:
                # thm:cap-fixed-rigidity: the floor antecedent alone supplies the multisets
                assert same_multiset, ("antecedent without equal multisets", P.X, P.Y)
                for i in range(v):
                    assert argmin(P.F(i, om, al))[1] == [i + 1, i + 2], ("chain", P.X, P.Y, i)
                assert [j for j in pos if al[j] == m_plus] == [1, 2]
                assert all(al[j] is not None for j in range(1, v + 2))
                assert al[1] == al[2]
                for j in range(2, v + 1):
                    assert al[j] < al[j + 1]
                for j in range(v + 2, n + 1):
                    if al[j] is not None:
                        assert al[j] > al[v + 1]
                n_chain += 1
                by_v[v] += 1
                if al[0] is None:
                    n_equal += 1
                    for j in range(1, q + 1):
                        w, fc = init_face(P.G[j], om)
                        assert len(fc) == 1 and list(fc.values())[0] in (1, -1), ("single monomial", P.X, P.Y, j)
            else:
                n_other += 1
    assert n_chain > 0 and n_other > 0 and n_equal > 0 and n_back > 0
    print("pairs %d, random admissible weights %d" % (len(pairs), N_WEIGHTS))
    print("synchronization / no-backflow comparisons : %d / %d" % (n_sync, n_back))
    print("floor antecedent holds %d (by v: %s), fails %d, actual equal pairs %d" % (n_chain, dict(sorted(by_v.items())), n_other, n_equal))
    print("ALL PASS")


if __name__ == "__main__":
    main()
