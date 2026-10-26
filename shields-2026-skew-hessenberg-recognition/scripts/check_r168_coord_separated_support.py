"""Coordinator's independent check of lane H's separated-support theorem (round 168).

CLAIM (r168-h.md, "heterogeneous reconstruction from disjoint gap supports"):
zero-free multirow blocks with pairwise disjoint nonempty internal gap supports,
joined at zero gaps, form a rotation-rigid parent whenever their total merger is
rotation-rigid.  Individual block rigidity is not assumed.

MECHANISM, sharing nothing with H's scripts:
  * Equal skew Schur functions force equal multisets of row lengths and of adjacent
    gaps, so every possible connected mate is an arrangement of the source's rows
    with an arrangement of its gaps.  All arrangements are enumerated by a pruned
    depth-first search (a gap must be below both adjacent row lengths).
  * Each candidate's Jacobi-Trudi determinant is evaluated at random points modulo
    2^61 - 1.  One differing value PROVES the polynomials differ.  A candidate
    outside {D, D*} that matches at every point is reported as a mate.

Notation: (row lengths; gaps), gap = adjacent overlap minus one, rows top to bottom,
as in the ledger and r168-h.md.

Assertions:
  (1) H's eight-row three-block example D and its merger C are both rotation-rigid.
  (2) The k = 2 member of H's strengthened family, B_1 = (9,6,5;4,4) joined to
      B_2 = (5,6,6;2,2), and its merger, are both rotation-rigid.
  (3) Hypotheses of the theorem hold on the sources tested: zero gaps split them
      into multirow blocks, the blocks are zero-free, and their gap supports are
      disjoint and nonempty.
  (4) CONTROL that must FIRE: the 19-cell pair of C.1628, fed to the same mate
      finder, returns its known nonrotation mate.
"""
import random
from collections import Counter

P = (1 << 61) - 1
rng = random.Random(20260923)
NPTS, HMAX = 3, 400
POINTS = [[rng.randrange(1, P) for _ in range(HMAX)] for _ in range(NPTS)]


def betas(rows, gaps):
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return x, y


def det_mod(rows, gaps, pt):
    x, y = betas(rows, gaps)
    n = len(rows)

    def hv(k):
        if k < 0:
            return 0
        if k == 0:
            return 1
        assert k <= HMAX, "raise HMAX"
        return pt[k - 1]
    M = [[hv(x[i] - y[j]) for j in range(n)] for i in range(n)]
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det = det * M[c][c] % P
        inv = pow(M[c][c], P - 2, P)
        for r in range(c + 1, n):
            f = M[r][c] * inv % P
            if f:
                M[r] = [(a - f * b) % P for a, b in zip(M[r], M[c])]
    return det % P


def arrangements(rows, gaps):
    """Every (R, G) with R a rearrangement of rows, G of gaps, 0 <= G_i < min(R_i, R_{i+1})."""
    n = len(rows)
    rc, gc = Counter(rows), Counter(gaps)
    R, G = [], []
    out = []

    def dfs():
        if len(R) == n:
            out.append((tuple(R), tuple(G)))
            return
        for r in list(rc):
            if not rc[r]:
                continue
            if R:
                for g in list(gc):
                    if gc[g] and 0 <= g < min(R[-1], r):
                        rc[r] -= 1
                        gc[g] -= 1
                        R.append(r)
                        G.append(g)
                        dfs()
                        R.pop()
                        G.pop()
                        rc[r] += 1
                        gc[g] += 1
            else:
                rc[r] -= 1
                R.append(r)
                dfs()
                R.pop()
                rc[r] += 1
    dfs()
    return out


def rot(rows, gaps):
    return tuple(reversed(rows)), tuple(reversed(gaps))


def nonrotation_mates(rows, gaps):
    src = (tuple(rows), tuple(gaps))
    sig = [det_mod(*src, pt) for pt in POINTS]
    cands = arrangements(*src)
    extra = []
    for c in cands:
        if c in (src, rot(*src)):
            continue
        if all(det_mod(*c, pt) == s for pt, s in zip(POINTS, sig)):
            extra.append(c)
    return len(cands), extra


def blocks(rows, gaps):
    out, start = [], 0
    for i, g in enumerate(gaps):
        if g == 0:
            out.append((rows[start:i + 1], gaps[start:i]))
            start = i + 1
    out.append((rows[start:], gaps[start:]))
    return out


def zero_free(rows, gaps):
    x, y = betas(rows, gaps)
    return not (set(x) & set(y))


def merge(bl):
    """Total merger: each zero gap is contracted, the two adjacent endpoint rows fused."""
    rows, gaps = list(bl[0][0]), list(bl[0][1])
    for r, g in bl[1:]:
        rows[-1] = rows[-1] + r[0]
        rows += list(r[1:])
        gaps += list(g)
    return tuple(rows), tuple(gaps)


def check_hypotheses(rows, gaps):
    bl = blocks(rows, gaps)
    assert len(bl) >= 2 and all(len(r) >= 2 for r, _ in bl), "not multirow blocks"
    assert all(zero_free(*b) for b in bl), "a block is not zero-free"
    sup = [set(g) for _, g in bl]
    assert all(sup), "an empty gap support"
    for i in range(len(sup)):
        for j in range(i + 1, len(sup)):
            assert not (sup[i] & sup[j]), "gap supports overlap"
    return bl


def main():
    D = ((13, 10, 5, 5, 7, 13, 14, 14), (4, 4, 0, 2, 0, 6, 6))
    C = ((13, 10, 10, 20, 14, 14), (4, 4, 2, 6, 6))
    K2 = ((9, 6, 5, 5, 6, 6), (4, 4, 0, 2, 2))
    for name, src, merger in (("eight-row example", D, C), ("family, k = 2", K2, None)):
        bl = check_hypotheses(*src)
        m = merge(bl)
        if merger is not None:
            assert m == merger, (m, merger)
        print(f"PASS (3): {name} {src}: {len(bl)} zero-free multirow blocks, "
              f"supports {[sorted(set(g)) for _, g in bl]} disjoint; merger {m}")
        for what, obj in (("source", src), ("merger", m)):
            n, extra = nonrotation_mates(*obj)
            assert not extra, (name, what, "NONROTATION MATE", extra[:3])
            print(f"PASS: {name} {what} ({sum(obj[0])} cells): rotation-rigid against all "
                  f"{n} arrangements of its rows and gaps")

    W = ((4, 5, 4, 3, 2, 1), (2, 3, 2, 1, 0))
    known = ((1, 2, 3, 4, 4, 5), (0, 1, 2, 2, 3))
    n, extra = nonrotation_mates(*W)
    assert known in extra or rot(*known) in extra, "CONTROL DID NOT FIRE"
    print(f"PASS (4, control fires): the 19-cell source returns its known mate among "
          f"{len(extra)} nonrotation match(es) out of {n} arrangements")
    print("ALL PASS")


if __name__ == "__main__":
    main()
