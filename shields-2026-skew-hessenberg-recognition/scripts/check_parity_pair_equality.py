"""The zero-free hypothesis cannot be dropped: the witness pair has equal functions.

The obstruction remark displays two connected profiles,

    F = (4,5,4,3,2,1; 2,3,2,1,0)
    H = (1,2,3,4,4,5; 0,1,2,2,3)

and rests on their skew Schur functions being equal while their zero-cut block
functions differ.  This script establishes the equality directly, from the
definitions, so the remark does not depend on a result proved elsewhere.

Everything is built here: a profile is converted to its beta lists by
r_i = x_i - y_i and g_i = x_{i+1} - y_i with y_n = 0, and the determinant
det(h_{x_i - y_j}) is expanded as a signed sum over the 720 permutations, with
exponents carried as integer multisets.  No module in this directory is
imported.

`check_parity_pair_determinant.py` establishes the same equality by forming the
Jacobi-Trudi matrix over symbolic generators and calling a general determinant
routine.  The two share no code and no algorithm, so a defect in either would
have to be reproduced independently in the other to escape both.
"""
from fractions import Fraction
from itertools import permutations

F_ROWS, F_GAPS = (4, 5, 4, 3, 2, 1), (2, 3, 2, 1, 0)
H_ROWS, H_GAPS = (1, 2, 3, 4, 4, 5), (0, 1, 2, 2, 3)


def connected(rows, gaps):
    """g_i is the overlap minus one, so 0 <= g_i < min(r_i, r_{i+1})."""
    return all(0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps))


def betas(rows, gaps):
    n = len(rows)
    x = [0] * n
    y = [0] * n
    x[n - 1] = rows[n - 1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    return tuple(x), tuple(y)


def schur(x, y):
    """det(h_{x_i-y_j}) as a dict from exponent-multiset to integer coefficient.

    h_0 = 1 and h_k = 0 for k < 0.  Expanded by permutations: n = 6 here, so the
    720 terms are cheap and the routine needs no linear algebra.
    """
    n = len(x)
    out = {}
    for p in permutations(range(n)):
        sign = 1
        seen = [0] * n
        # permutation sign by cycle parity
        visited = [False] * n
        for s in range(n):
            if visited[s]:
                continue
            length = 0
            t = s
            while not visited[t]:
                visited[t] = True
                t = p[t]
                length += 1
            if length % 2 == 0:
                sign = -sign
        idx = []
        ok = True
        for i in range(n):
            k = x[i] - y[p[i]]
            if k < 0:
                ok = False
                break
            if k > 0:
                idx.append(k)
        if not ok:
            continue
        key = tuple(sorted(idx))
        out[key] = out.get(key, 0) + sign
    return {k: v for k, v in out.items() if v != 0}


def main():
    checks = 0
    assert connected(F_ROWS, F_GAPS), "F is not connected"
    assert connected(H_ROWS, H_GAPS), "H is not connected"
    assert sum(F_ROWS) == sum(H_ROWS) == 19, "areas differ"
    checks += 3

    xF, yF = betas(F_ROWS, F_GAPS)
    xH, yH = betas(H_ROWS, H_GAPS)
    sF, sH = schur(xF, yF), schur(xH, yH)

    assert sF == sH, "THE WITNESS EQUALITY FAILS"
    assert len(sF) > 0, "empty function"
    checks += 2

    # The pair must be a genuine nonrotation equality, or the remark is vacuous.
    rot = (tuple(reversed(F_ROWS)), tuple(reversed(F_GAPS)))
    assert rot != (H_ROWS, H_GAPS), "H is merely the rotation of F"
    checks += 1

    # Firing controls: each perturbation must break the equality.
    fired = 0
    for rows, gaps, name in (
        ((1, 2, 3, 4, 5, 5), H_GAPS, "row perturbation"),
        (H_ROWS, (0, 1, 2, 2, 2), "gap perturbation"),
        ((4, 5, 4, 3, 2, 2), F_GAPS, "F perturbation"),
    ):
        if not connected(rows, gaps):
            continue
        xB, yB = betas(rows, gaps)
        if schur(xB, yB) != sF:
            fired += 1
    assert fired == 3, "a control did not fire: the comparison cannot detect a change"
    checks += fired

    print("F profile %s;%s  betas x=%s y=%s" % (F_ROWS, F_GAPS, xF, yF))
    print("H profile %s;%s  betas x=%s y=%s" % (H_ROWS, H_GAPS, xH, yH))
    print("area 19 each; %d monomials each; equal: True; rotation of each other: False"
          % len(sF))
    print("firing controls that broke the equality: %d of 3" % fired)
    print("checks: %d" % checks)
    print("ALL PASS")


if __name__ == "__main__":
    main()
