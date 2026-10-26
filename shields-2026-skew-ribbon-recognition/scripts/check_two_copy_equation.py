r"""Two-copy flags, cut words and private-pair arithmetic of a mixed finer
(ph:two-copy-equation, ph:vanishing, ph:first-response, ph:intercept-exclusion).

Paper section `app:cofaces` (Cofaces, two-copy identities, and native residues) and
`sec:comparison` (Finite comparisons on actual composition charts); labels ph:two-copy-equation,
ph:private-two, ph:CF0, ph:vanishing.

Reading: these statements concern an active mixed pair, which exists only inside a comparison the
main theorem excludes.  The finite data they consume are assembled from real marks.  For every
connected J up to J_CELLS cells and every legal case (d) mark of period r, width v > 0, phases
(t, s), with Z = Row_2 o_mu J, N_J = r + v, X_W = X_J on [0, v], B_- = X_J on (v, r),
Y_W = (Y_J on [0, v]) minus {s}, C_- = Y_J on (v, r):

* the flags of Z are exactly X_Z = union_{l=0..2} (l r + X_W) u union_{l=0..1} (l r + B_-) and
  Y_Z = union_{l=0..2} (l r + (Y_W minus t)) u union_{l=0..1} (l r + C_-) u {t, s, r+s}, all
  disjoint unions, and the span is 2r + v;
* the original end comparison on [0, v]: X_J(x + r) = X_J(x) and Y_J(x + r) - Y_J(x) =
  -[x = t] - [x = s];
* for every private active pair (v < j, k, j - delta, k - delta < r, j + k = r + s + t + delta,
  either sign of delta) and every head h with max(j, k, N_J - (j-delta), N_J - (k-delta)) <= h < r,
  L = N_J - h: the cuts X_S = X_Z on (0, r+h], Y_S = Y_Z on [0, r+h] minus {r+k},
  X_T = (X_Z on [L, 2r+v]) - L, Y_T = ((Y_Z on [L, 2r+v)) u {j - delta}) - L, wherever they are
  connected diagrams' flags, have closed row defect zero and column defect [x = j-delta] +
  [x = r+k] on [L, r+h]; and then both children have area strictly below |Z|;
* a_j = N_J + delta - j = k + epsilon with epsilon = v - s - t, b_j = j - delta;
* ph:vanishing: the second-response weight w_f = 2r + s + delta - j = r + k - t exceeds
  2 rho, rho = s - t, so a rho = w_f forces a >= 3 whenever rho divides w_f, and the first-intercept
  weight r + s + delta - j = k - t exceeds rho (so p >= 2), over the whole box
  0 <= t < s <= v < r, v < j, k < r, v < j - delta, k - delta < r.

The control is the count of flag sets rejected as diagrams: most head choices do not give a
connected pair, so the connectedness hypothesis is restrictive.

Uncovered: the response coefficients b_{2,j}, the fine-field homogeneity argument, and the
cleared product identity with its component products.
"""
from _gluing_common import compose, intersection_mark, legal
from check_two_copy_flags import betas, diagrams, phases

J_CELLS = 9
BOX = 12
ROW2 = frozenset({(0, 0), (0, 1)})


def valid(X, Y):
    X, Y = sorted(X, reverse=True), sorted(Y, reverse=True)
    if len(X) != len(Y) or len(set(X)) != len(X) or len(set(Y)) != len(Y):
        return False
    n = len(X)
    return all(Y[i] < X[i] for i in range(n)) and all(Y[i] <= X[i + 1] for i in range(n - 1))


def main():
    flags = pairs = rejected = accepted = 0
    for J in diagrams(J_CELLS):
        for cell in J:
            try:
                mk = intersection_mark(J, cell)
            except AssertionError:
                continue
            if mk.case != 'd' or not legal(mk) or mk.width == 0:
                continue
            r, v = mk.period, mk.width
            s, t = phases(mk)
            N = r + v
            X, Y = betas(J)
            XW = [x for x in X if x <= v]
            Bm = [x for x in X if v < x < r]
            YW = [y for y in Y if y <= v and y != s]
            Cm = [y for y in Y if v < y < r]
            Z = compose(ROW2, mk)
            XZ, YZ = betas(Z)
            S2 = 2 * r + v
            assert XZ[0] == S2
            expectX = sorted([l * r + x for l in range(3) for x in XW] + [l * r + b for l in range(2) for b in Bm])
            expectY = sorted([l * r + y for l in range(3) for y in YW if y != t]
                             + [l * r + c for l in range(2) for c in Cm] + [t, s, r + s])
            assert sorted(XZ) == expectX and sorted(YZ) == expectY, (sorted(J), r, v)
            flags += 1
            for x in range(0, v + 1):
                assert (x + r in X) == (x in X)
                assert (x + r in Y) - (x in Y) == -(x == t) - (x == s)
            for delta in range(-r + 1, r):
                if delta == 0:
                    continue
                for j in range(v + 1, r):
                    k = r + s + t + delta - j
                    if not (v < k < r and v < j - delta < r and v < k - delta < r):
                        continue
                    eps = v - s - t
                    assert N + delta - j == k + eps
                    pairs += 1
                    for h in range(max(j, k, N - (j - delta), N - (k - delta)), r):
                        L = N - h
                        XS = [x for x in XZ if 0 < x <= r + h]
                        YS = [y for y in YZ if 0 <= y <= r + h and y != r + k]
                        XT = [x - L for x in XZ if L <= x <= S2]
                        YT = [y - L for y in YZ if L <= y < S2] + [j - delta - L]
                        if not (valid(XS, YS) and valid(XT, YT)):
                            rejected += 1
                            continue
                        accepted += 1
                        for x in range(L, r + h + 1):
                            assert (x - L in XT) == (x in XS)
                            assert (x - L in YT) - (x in YS) == (x == j - delta) + (x == r + k)
                        assert sum(XS) - sum(YS) < len(Z) and sum(XT) - sum(YT) < len(Z)
    print(f'case (d) marks: {flags}; private pairs {pairs}; head choices rejected {rejected}, '
          f'accepted {accepted}')
    assert flags > 20 and accepted > 100 and rejected > 0

    box = 0
    for r in range(3, BOX + 1):
        for v in range(1, r):
            for s in range(1, v + 1):
                for t in range(0, s):
                    rho = s - t
                    for delta in range(-r + 1, r):
                        for j in range(v + 1, r):
                            k = r + s + t + delta - j
                            if not (v < k < r and v < j - delta < r and v < k - delta < r):
                                continue
                            wf = 2 * r + s + delta - j
                            assert wf == r + k - t and wf > 2 * rho
                            assert r + s + delta - j == k - t and k - t > rho
                            if wf % rho == 0:
                                assert wf // rho >= 3
                            box += 1
    print(f'private-pair parameter box: {box}')
    assert box > 1000
    print('ALL PASS')


if __name__ == '__main__':
    main()
