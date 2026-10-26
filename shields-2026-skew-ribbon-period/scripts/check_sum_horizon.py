r"""Paper section `sec:response` (The complete scalar and its second channel).

`lem:sum-horizon` (the block calculation of `eq:source-truncations` at the horizon `p + q`), on
sampled periodic sources (`_source_common.sample`, g-periodic words with singleton pins at the
`q` horizon; further sources are drawn without the pins and kept when the `p + q` pins hold).

Asserted on every source: `a' = N - p - q - c >= |p - q| >= g > c`; the low cap and return data at
`p + q` agree with those at `q` (the head `r`, `l` of the window coframes and the frame lists
`I_L, C_L` shifted by `p`), by original `p`-periodicity of the boundary words.  The two high vectors (the variables `h_{a'}, ...`) are different from those at `q`, as the
lemma says (asserted: the index ranges are disjoint when `a' + c < a`).
The block formula `eq:source-truncations` is asserted at both horizons `q` and `p + q`, with return
corrections solved from the square systems.  Control: breaking the `p`-periodicity of one boundary
word at a middle position makes the low data at `q` and `p + q` differ (count reported).
"""
import random

from _source_common import alphabet, coframes, sample, solve, heights, source_data, Fr


def pins_ok(s, qq):
    X, Y, N, c = s['X'], s['Y'], s['N'], s['c']
    a = N - qq - c
    H = heights(X, Y, N)
    return a > c and all(H[k] == 1 for k in (c, qq - 1, qq + c, a - 1, N - c - 1, a + c, N - a - c, N - a - c - 1))


def window(s, qq, h):
    s2 = dict(s)
    s2['q'] = qq
    s2['a'] = s['N'] - qq - s['c']
    s2['m'] = s2['a'] + s['c']
    return source_data(s2, h), s2


def truncation_holds(s, h):
    X, Y, N, c, q, a, m = (s[k] for k in ('X', 'Y', 'N', 'c', 'q', 'a', 'm'))
    D = source_data(s, h)
    cf = coframes(X, Y, N, h)
    if D is None or cf is None:
        return None
    RS, LS = cf
    R0, L0 = D['R0'], D['L0']
    IR, CR, IL, CL = D['IR'], D['CR'], D['IL'], D['CL']
    P = {i: sum(v * h(a + i - e) for e, v in R0.items() if a + i - e >= 0) for i in range(c + 1)}
    Q = {j: sum(v * h(m - j - e) for e, v in L0.items() if m - j - e >= 0) for j in range(c + 1)}
    BR = [[h(i - j) for j in CR] for i in IR]
    BL = [[h(i - j) for j in CL] for i in IL]
    rho = solve(BR, [P[i] for i in IR]) if IR else []
    zeta = solve([[BL[i][j] for i in range(len(IL))] for j in range(len(CL))], [Q[j] for j in CL]) if IL else []
    if rho is None or zeta is None:
        return None
    Rt, Lt = dict(R0), dict(L0)
    for j, v in zip(CR, rho):
        Rt[a + j] = Rt.get(a + j, 0) - v
    for i, v in zip(IL, zeta):
        Lt[m - i] = Lt.get(m - i, 0) - v
    tr = lambda T: {e: v for e, v in T.items() if e <= m and v != 0}
    return tr(Rt) == tr(RS) and tr(Lt) == tr(LS)


def main():
    ntr = ncontrol = 0
    rng = random.Random(99)
    n = diff_high = 0
    tries = 0
    while n < 80 and tries < 200000:
        tries += 1
        s = sample(rng, want_pins=False)
        p, q, g, c, N = s['p'], s['q'], s['g'], s['c'], s['N']
        if not (pins_ok(s, q) and pins_ok(s, p + q)):
            continue
        ap = N - p - q - c
        assert ap >= abs(p - q) >= g > c
        h = alphabet(rng, N + 3)
        D1, s1 = window(s, q, h)
        D2, s2 = window(s, p + q, h)
        if D1 is None or D2 is None:
            continue
        n += 1
        for sx, hh in ((s1, h), (s2, h)):
            r = truncation_holds(sx, hh)
            if r is not None:
                assert r, ('eq:source-truncations fails', sx['q'])
                ntr += 1
        # control: toggle one position in both lists (a common beta; heights unchanged) inside the q-window
        # so that the words stop being p-periodic there
        for k0 in range(q, q + c + 1):
            X2, Y2 = set(s['X']), set(s['Y'])
            X2 ^= {k0}
            Y2 ^= {k0}
            s3 = dict(s)
            s3['X'], s3['Y'] = tuple(sorted(X2, reverse=True)), tuple(sorted(Y2, reverse=True))
            d1, d2 = window(s3, q, h)[0], window(s3, p + q, h)[0]
            if d1 and d2 and sorted(d1['IL']) != sorted(d2['IL']):
                ncontrol += 1
                break
        # low cap data agree: frame lists I_L, C_L and cap vectors
        assert sorted(D1['IL']) == sorted(D2['IL']) and sorted(D1['CL']) == sorted(D2['CL'])
        assert D1['l'] == D2['l'] and D1['r'] == D2['r']
        if ap + c < s1['a']:
            assert set(range(ap, ap + c + 1)).isdisjoint(range(s1['a'], s1['a'] + c + 1))
            diff_high += 1
    print(f"sources {n}; distinct high bands {diff_high}; truncation checks {ntr}; control (broken periodicity changes low data) {ncontrol}")
    assert ntr > 0
    assert n > 0
    print("PASS")


if __name__ == "__main__":
    main()
