r"""Paper section `sec:boundary` (Boundary comparisons and actual marked factors), ge:signed-cap.

The lemma is a statement about binary words, so it is checked by enumerating every word.

Literal reading used for "native g-periodic away from their respective variable phases p, q":
U(x + g) = U(x) whenever 0 <= x, x + g <= H and x is not congruent to the phase modulo g.  The
positions congruent to the phase are the variable ones; they are free subject to the caps
U_S(p) = U_T(q) = 0 and U_S(mg + p) = U_T(mg + q) = 1.  The zero-filled (one-filled) native word of U
sets every variable position to 0 (1).  A "proper" port is a variable position other than the two
cap positions.  The "filled native cardinality" is the number of ones of the filled word on one
period [0, g).

For every g in 2..GMAX, m in 2..MMAX, 0 <= a < g, 0 <= p, q <= a, 0 < u < H = m g + a, and every pair
of words satisfying the hypotheses with some 0 <= e <= V = H - u, the conclusions of the lemma are
asserted in both cases p != q - u and p = q - u (mod g).  The case split is checked non-vacuous.
"""
import itertools

GMAX = 5
MMAX = 3


def words(g, m, a, ph):
    H = m * g + a
    var = [x for x in range(H + 1) if x % g == ph % g]
    caps = {ph: 0, m * g + ph: 1}
    free = [x for x in var if x not in caps]
    base = [x for x in range(H + 1) if x % g != ph % g and x < g]
    for fbits in itertools.product((0, 1), repeat=len(free)):
        for bbits in itertools.product((0, 1), repeat=len(base)):
            U = [None] * (H + 1)
            for x, b in zip(base, bbits):
                U[x] = b
            for x in range(H + 1):
                if x % g != ph % g and x >= g:
                    U[x] = U[x - g]
            for x, b in caps.items():
                U[x] = b
            for x, b in zip(free, fbits):
                U[x] = b
            yield U


def filled(U, g, ph, val):
    return [val if x % g == ph % g else U[x] for x in range(len(U))]


def main():
    cases = alt_zero = alt_one = same_phase = 0
    for g in range(2, GMAX + 1):
        for m in range(2, MMAX + 1):
            for a in range(g):
                H = m * g + a
                for p in range(a + 1):
                    for q in range(a + 1):
                        S = list(words(g, m, a, p))
                        T = list(words(g, m, a, q))
                        for u in range(1, H):
                            V = H - u
                            for US in S:
                                for UT in T:
                                    diff = [UT[x + u] - US[x] for x in range(V + 1)]
                                    if sorted(diff) != sorted([0] * V + [1]):
                                        continue
                                    e = diff.index(1)
                                    cases += 1
                                    var_s = [x for x in range(V + 1) if x % g == p
                                             and x not in (p, m * g + p)]
                                    var_t = [x for x in range(u, H + 1) if x % g == q % g
                                             and x not in (q, m * g + q)]
                                    if (p - (q - u)) % g != 0:
                                        if e >= g:
                                            assert e == V - a + q, (g, m, a, p, q, u, e)
                                            z_s, z_t = filled(US, g, p, 0), filled(UT, g, q, 0)
                                            assert all(z_t[x + u] == z_s[x] for x in range(V + 1))
                                            assert all(US[x] == 0 for x in var_s)
                                            assert all(UT[x] == 0 for x in var_t)
                                            assert sum(z_s[:g]) == sum(z_t[:g])
                                            alt_zero += 1
                                        if e <= V - g:
                                            assert e == p, (g, m, a, p, q, u, e)
                                            o_s, o_t = filled(US, g, p, 1), filled(UT, g, q, 1)
                                            assert all(o_t[x + u] == o_s[x] for x in range(V + 1))
                                            assert all(US[x] == 1 for x in var_s)
                                            assert all(UT[x] == 1 for x in var_t)
                                            assert sum(o_s[:g]) == sum(o_t[:g])
                                            alt_one += 1
                                    else:
                                        if e >= g or e <= V - g:
                                            o_s, o_t = filled(US, g, p, 1), filled(UT, g, q, 1)
                                            assert all(o_t[x + u] == o_s[x]
                                                       for x in range(V + 1)), \
                                                (g, m, a, p, q, u, e)
                                            same_phase += 1
    assert alt_zero > 0 and alt_one > 0 and same_phase > 0
    print(f'ge:signed-cap: {cases} word pairs with a unit error; e >= g: {alt_zero}, '
          f'e <= V - g: {alt_one}, congruent phases: {same_phase}')
    print('ALL PASS')


if __name__ == '__main__':
    main()
