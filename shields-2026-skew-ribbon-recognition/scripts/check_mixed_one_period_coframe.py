"""The one-period reading of the mixed numerator response against the left coframe.

Paper section `sec:comparison` (Finite comparisons on actual composition charts), ph:mixed-flags, ph:mixed-native.

`ph:mixed-native` reads the numerator response `F_{P_i} = l_{i-delta}` (with
`Lambda_{b+r} = u Lambda_b`) at one period and identifies it with `eta * C_{N_J+delta-i}`, the
left coframe of the finer `J` at the reflected position.  Here `l = e_s^T D_s(u)^{-1}` on the
native rows `X_W + B_-` and the columns `(Y_W - t) + C_- + {s}`, with the flags of
`ph:mixed-flags`, and `C` is the left coframe of `J` normalized at the top row.

Checked over random rational letters, with one constant `eta` per sample:

* at a high mark row `r + b`: `[u^0] l_b = eta * C_{N_J - r - b}`;
* at a private row `b`: `[u^1] l_b = eta * C_{N_J - b}`;
* at a low mark row `b`, when `t = 0`: `[u^1] l_b = eta * C_{N_J - b}`.

At a low mark row `b < v` with `t > 0` the identity fails in every sample below, while
`[u^1] l_b` stays nonzero.  The flag configurations are taken from the shape of
`ph:mixed-flags`; whether each is realized by a legal case-(d) mark is not checked here.
"""
import random

from sympy import Matrix, Rational


def sample(r, v, XW, YW, s, t, Bm, Cm, seed):
    rnd = random.Random(seed)
    rows = sorted(XW + Bm)
    cols = sorted([c for c in YW if c != t] + Cm + [s])
    XJ = sorted(rows + [r + x for x in XW])
    YJ = sorted(YW + [s] + Cm + [r + c for c in YW if c != t])
    NJ = r + v
    assert len(rows) == len(cols) and len(XJ) == len(YJ) and max(XJ) == NJ
    hv = {k: Rational(rnd.randint(-9, 9), rnd.randint(1, 5)) for k in range(4 * r + 4)}
    hv[0] = Rational(rnd.randint(1, 9), rnd.randint(1, 3))
    h = lambda k: hv[k] if k >= 0 else 0
    k = len(rows)
    D = [Matrix(k, k, lambda i, j: h(n * r + rows[i] - cols[j])) for n in range(2)]
    D0i = D[0].inv()
    l0 = D0i.row(cols.index(s))
    l1 = (-D0i * D[1] * D0i).row(cols.index(s))
    ycols = [y for y in YJ if y != 0]
    Mt = Matrix(len(XJ), len(ycols), lambda i, j: h(XJ[i] - ycols[j]))
    top = XJ.index(NJ)
    others = [i for i in range(len(XJ)) if i != top]
    c = -Mt.row(top) * Mt.extract(others, list(range(len(ycols)))).inv()
    C = {NJ - XJ[others[i]]: c[i] for i in range(len(others))}
    C[0] = Rational(1)
    eta = l0[rows.index(v)]  # the top: [u^0] l_v = eta * C_0
    low_ok = []
    for i, b in enumerate(rows):
        if b in XW:
            assert l0[i] == eta * C[NJ - r - b], (b, "high")
        if b in Bm:
            assert l1[i] == eta * C[NJ - b], (b, "private")
        if b in XW and b < v:
            low_ok.append(l1[i] == eta * C[NJ - b])
            assert l1[i] != 0
    return low_ok


def main():
    for seed in range(3):
        # t = 0: the identity holds at every native row
        assert all(sample(4, 2, [1, 2], [0, 1], 2, 0, [3], [3], seed))
        assert all(sample(5, 2, [1, 2], [0, 1], 2, 0, [3, 4], [3, 4], seed))
        # t > 0: it fails at the low mark rows
        assert not any(sample(4, 2, [1, 2], [0, 1], 2, 1, [3], [3], seed))
        assert not any(sample(5, 3, [2, 3], [0, 1], 2, 1, [4], [4], seed))
        assert not any(sample(5, 3, [2, 3], [0, 1], 3, 1, [4], [4], seed))
    print("check_mixed_one_period_coframe: PASS")


if __name__ == "__main__":
    main()
