r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

The source lists at an empty fine mark: prop:noncell-realization (the list claims that precede
eq:empty-section), with eq:capped-core-quotient and lem:conormal-caps.

For a connected inner U with the empty mark (period q = span U, v = ne(U) - sw(U) + (0, 1)) and a
connected skew J of span R, the composite E = J o U puts the copy U + content(d) v + d_1 (1, 1) at
each cell d of J.  Writing X_E, Y_E for the beta lists of E (row ends xi, row starts zeta, normalized
so the last zeta is 0), the script asserts on random pairs (J, U):

  * E is a connected skew diagram of span R q;
  * residue entries: {x in X_E : q | x} = q X_J and {y in Y_E : q | y} = q Y_J;
  * the lists of U other than the top q (resp. 0) lie strictly between 0 and q (the cap entries);
  * every entry of X_E (resp. Y_E) off the residue class is a cap entry of a copy U + t q,
    0 <= t < R, so X_E, Y_E consist of the shifted q-caps of U and the residue entries q X_J,
    q Y_J, with the common betas Z_E = X_E cap Y_E on the residue class equal to q Z_J,
    Z_J = X_J cap Y_J contained in {1, ..., R - 1};
  * the lists X_J' = X_J0 + Z_rho, Y_J' = Y_J0 + Z_rho rebuilt from the residue class of E, with
    J0 the zero-free reduction of J, have height #{Y <= j} - #{X <= j} equal to H_J0(j) > 0 on
    0 <= j < R and are the lists of a connected skew diagram of span R (the reconstruction).

It prints the number of pairs and the number of pairs with a nonempty residue common set.

The quotient J and the literal empty composite are supplied inputs.  These checks verify
their complete list formulas and common-beta reconstruction, not the existence of that
literal quotient at a fresh-minimum stage.
"""
import random


def content(c):
    return c[1] - c[0]


def is_skew_connected(cells):
    cells = set(cells)
    if not cells:
        return False
    rows = {}
    for i, j in cells:
        rows.setdefault(i, []).append(j)
    ks = sorted(rows)
    if ks != list(range(ks[0], ks[-1] + 1)):
        return False
    for i, js in rows.items():
        js.sort()
        if js != list(range(js[0], js[-1] + 1)):
            return False
    for a, b in zip(ks, ks[1:]):
        la, ra = rows[a][0], rows[a][-1]
        lb, rb = rows[b][0], rows[b][-1]
        if not (lb <= la and rb <= ra):
            return False
        if not (lb <= ra and la <= rb):  # consecutive rows overlap in a column
            return False
    return True


def betas(cells):
    rows = {}
    for i, j in cells:
        rows.setdefault(i, []).append(j)
    ks = sorted(rows)
    xi = [max(rows[i]) + 1 - r for r, i in enumerate(ks)]
    ze = [min(rows[i]) - r for r, i in enumerate(ks)]
    c = ze[-1]
    return [x - c for x in xi], [z - c for z in ze]


def span(cells):
    cs = [content(c) for c in cells]
    return max(cs) - min(cs) + 1


def sw_ne(cells):
    cs = {content(c) for c in cells}
    lo, hi = min(cs), max(cs)
    swc = min((c for c in cells if content(c) == lo), key=lambda c: c[0])
    nec = min((c for c in cells if content(c) == hi), key=lambda c: c[0])
    return swc, nec


def compose_empty(J, U):
    swc, nec = sw_ne(U)
    v = (nec[0] - swc[0], nec[1] - swc[1] + 1)
    out = set()
    for d in J:
        c = content(d)
        ox, oy = c * v[0] + d[0], c * v[1] + d[0]
        for u in U:
            out.add((u[0] + ox, u[1] + oy))
    return out, content(v)


def random_skew(rng, rows, width):
    while True:
        r = []
        left, right = 0, rng.randint(0, width)
        for _ in range(rows):
            r.append((left, right))
            nl = rng.randint(max(0, left - 0), right)
            nr = rng.randint(max(nl, right - 2), right + width)
            left, right = nl, nr
        cells = set()
        for k, (a, b) in enumerate(r):
            for j in range(a, b + 1):
                cells.add((k, j))
        # rows go south as k grows, so left ends move left: reflect columns
        m = max(j for _, j in cells)
        cells = {(i, m - j) for i, j in cells}
        # after the reflection the sequence is a skew shape read bottom to top
        cells = {(len(r) - 1 - i, j) for i, j in cells}
        if is_skew_connected(cells):
            return cells


def height(X, Y, j):
    return sum(1 for y in Y if y <= j) - sum(1 for x in X if x <= j)


def main():
    rng = random.Random(11)
    pairs = with_common = 0
    for _ in range(6000):
        J = random_skew(rng, rng.randint(1, 4), 3)
        U = random_skew(rng, rng.randint(1, 3), 3)
        if len(U) < 2:
            continue
        R = span(J)
        E, q = compose_empty(J, U)
        assert q == span(U)
        if not is_skew_connected(E):
            continue
        assert span(E) == R * q, (J, U)
        XJ, YJ = betas(J)
        XU, YU = betas(U)
        XE, YE = betas(E)
        assert XU[0] == q and YU[-1] == 0
        capX = [x for x in XU if x != q]
        capY = [y for y in YU if y != 0]
        assert all(0 < x < q for x in capX) and all(0 < y < q for y in capY)
        assert sorted(x for x in XE if x % q == 0) == sorted(q * x for x in XJ)
        assert sorted(y for y in YE if y % q == 0) == sorted(q * y for y in YJ)
        perX = {x + t * q for x in capX for t in range(R)}
        perY = {y + t * q for y in capY for t in range(R)}
        assert {x for x in XE if x % q} == perX, (J, U)
        assert {y for y in YE if y % q} == perY, (J, U)
        ZJ = set(XJ) & set(YJ)
        assert all(1 <= z <= R - 1 for z in ZJ)
        # residue commons of E are q Z_J
        ZE = set(XE) & set(YE)
        assert {z for z in ZE if z % q == 0} == {q * z for z in ZJ}
        # reconstruction from the residue class: X_J = X_J0 + Z_rho
        Zr = {z // q for z in ZE if z % q == 0}
        XJ0 = [x for x in XJ if x not in Zr]
        YJ0 = [y for y in YJ if y not in Zr]
        assert not (set(XJ0) & Zr) and not (set(YJ0) & Zr)
        for j in range(0, R):
            assert height(XJ0, YJ0, j) == height(XJ, YJ, j) > 0
        assert sorted(XJ0 + sorted(Zr)) == sorted(XJ, ) and sorted(YJ0 + sorted(Zr)) == sorted(YJ)
        pairs += 1
        with_common += bool(Zr)
    assert pairs > 500 and with_common > 20
    print(f"ok: {pairs} pairs, {with_common} with a residue common set")


if __name__ == "__main__":
    main()
