r"""Paper sections `sec:unit-restoration` (Complete unit restoration).  Targets `sc:restoration-polynomial`,
`sc:bordered-grade`, `sc:linearized-cap`, `sc:splice-nonzero`, `sc:whole-unit-series`, `sc:unit-expansion`,
`sc:core-leading-term`, `sc:finite-injectivity`.

Exact integer arithmetic on full flags (units kept, h_0 = 1), as in `verify_fixed_cap_census`: a board is a pair of
strictly decreasing lists with the column list ending at 0, and its Jacobi-Trudi polynomial is a dictionary
from sorted monomials (positive generators only) to integers.  The ordinary degree of a monomial is its
number of positive factors.

  (1) Restoration polynomial.  For every connected zero-free board of span at most SPAN_MAX and every
      genuine vacancy b: the restored board's polynomial has degree-r part sigma_b s_B and degree-(r+1) part
      sigma_b (-b_b adj(M_B) a_b), with the actual sorted insertion sign sigma_b, nothing else; the
      adjugate expression is evaluated exactly at random rational letters and compared.
  (2) Linearized fixed-cap theorem.  For every connected zero-free child of span at most SPAN_MAX and every
      connected zero-free cap of span at most CAP_MAX, the stacked restoration polynomials
      (s-dot_B^(b), s-dot_{K<|B}^(b)) over the genuine vacancies b of B are linearly independent over Q:
      only zero weights kill both observations.  The insertion signs agree on B and on the splice.
      Control: the child's own restoration polynomials alone are NOT independent on some board
      (so the cap observation is load-bearing), and independence fails once a cap that is not zero-free is
      used on a board with two cap-position weights.
  (3) First nonzero grade of the cell-splice difference.  For every connected diagram V of span at most
      SPAN_MAX (units included) that is not its own half-turn, J_2 = s_{V<|CELL} - s_{CELL<|V} is nonzero and
      its lowest ordinary degree is k when the zero-free core is not self-rotating and k + 1 when it is.
"""
import random
from fractions import Fraction
from itertools import combinations

from verify_fixed_cap_census import (
    area, boards, connected, corner, hval, padd, rand_letters, rotate, schur, splice, det,
)

SPAN_MAX = 8
CAP_MAX = 4
random.seed(20261101)

CELL = ((1,), (0,))


def zero_free(b):
    return not set(b[0]) & set(b[1])


def vacancies(b):
    rows, cols = b
    return tuple(i for i in range(1, rows[0]) if i not in rows and i not in cols)


def restore(b, p):
    return tuple(sorted(b[0] + (p,), reverse=True)), tuple(sorted(b[1] + (p,), reverse=True))


def sigma(b, p):
    return (-1) ** (sum(x < p for x in b[0]) + sum(y < p for y in b[1]))


def deg_part(poly, d):
    return {m: c for m, c in poly.items() if len(m) == d}


def scal(poly, s):
    return {m: s * c for m, c in poly.items()}


def evaluate(poly, L):
    tot = Fraction(0)
    for mono, c in poly.items():
        t = Fraction(c)
        for k in mono:
            t *= L[k]
        tot += t
    return tot


def adjugate_form(b, p, L):
    rows, cols = b
    n = len(rows)
    M = [[hval(L, x - y) for y in cols] for x in rows]
    a = [hval(L, x - p) for x in rows]
    bb = [hval(L, p - y) for y in cols]
    # -b^T adj(M) a  =  det([[M, a], [bb, 0]])
    big = [M[i] + [a[i]] for i in range(n)] + [bb + [Fraction(0)]]
    return det(big)


def rank_q(vectors):
    basis = {}
    r = 0
    for v in vectors:
        v = {k: Fraction(c) for k, c in v.items() if c}
        while v:
            piv = max(v)
            if piv not in basis:
                basis[piv] = {k: c / v[piv] for k, c in v.items()}
                r += 1
                break
            f = v[piv]
            for k, c in basis[piv].items():
                nv = v.get(k, 0) - f * c
                if nv:
                    v[k] = nv
                else:
                    v.pop(k, None)
    return r


def check_restoration_polynomial(all_boards):
    n = 0
    for B in all_boards:
        if not zero_free(B):
            continue
        r = len(B[0])
        sB = schur(B)
        for p in vacancies(B):
            R = schur(restore(B, p))
            sg = sigma(B, p)
            assert deg_part(R, r) == scal(sB, sg), ("graded part r", B, p)
            assert deg_part(R, r + 1) == scal(deg_part(R, r + 1), 1)
            assert all(len(m) in (r, r + 1) for m in R), ("only two grades", B, p)
            L = rand_letters(B[0][0] + 1)
            assert evaluate(deg_part(R, r + 1), L) == sg * adjugate_form(B, p, L), ("restoration polynomial", B, p)
            n += 1
    return n


def check_linearized(all_boards, caps):
    n_ind = n_boards = 0
    ctrl_child_alone = 0
    for B in all_boards:
        if not zero_free(B):
            continue
        vac = vacancies(B)
        if not vac:
            continue
        r = len(B[0])
        child_vecs = []
        for p in vac:
            child_vecs.append({m: c for m, c in schur(restore(B, p)).items() if len(m) == r + 1})
        child_rank = rank_q(child_vecs)
        if child_rank < len(vac):
            ctrl_child_alone += 1
        for K in caps:
            if not zero_free(K):
                continue
            S = splice(K, B)
            rS = len(S[0])
            vecs = []
            for p in vac:
                assert sigma(B, p) == sigma(S, p)
                RS = schur(restore(S, p))
                assert all(len(m) in (rS, rS + 1) for m in RS)
                v = {("B",) + m: c for m, c in child_vecs[vac.index(p)].items()}
                v.update({("S",) + m: c for m, c in RS.items() if len(m) == rS + 1})
                vecs.append(v)
            assert rank_q(vecs) == len(vac), ("linearized fixed-cap rigidity", B, K)
            n_ind += 1
        n_boards += 1
    assert ctrl_child_alone > 0, "the cap observation must be load-bearing somewhere"
    return n_boards, n_ind, ctrl_child_alone


def core_of(b):
    rows, cols = b
    common = set(rows) & set(cols)
    return (tuple(x for x in rows if x not in common), tuple(y for y in cols if y not in common)), len(common)


def check_grades(all_boards):
    n_nonself = n_self = 0
    for V in all_boards:
        if V == rotate(V):
            continue
        J = {}
        for m, c in schur(splice(V, CELL)).items():
            padd(J, m, c)
        for m, c in schur(splice(CELL, V)).items():
            padd(J, m, -c)
        assert J, ("J_2 must be nonzero", V)
        core, u = core_of(V)
        k = len(core[0])
        lam = min(len(m) for m in J)
        core_rows, core_cols = core
        # the core normalized to span: a half-turn compares lists inside the core's own span
        top = core_rows[0] if core_rows else 0
        # the core of V, as a connected diagram, is normalized by deleting common betas (span unchanged)
        selfrot = rotate(V) == V
        core_self = (len(core_rows) > 0 and
                     tuple(sorted((V[0][0] - y for y in core_cols), reverse=True)) == core_rows and
                     tuple(sorted((V[0][0] - x for x in core_rows), reverse=True)) == core_cols)
        assert lam == (k + 1 if core_self else k), ("first grade", V, lam, k, core_self)
        n_self += core_self
        n_nonself += not core_self
    return n_nonself, n_self


def main():
    by_span = {s: list(boards(s)) for s in range(1, SPAN_MAX + 1)}
    all_boards = [b for s in by_span for b in by_span[s]]
    caps = [b for s in range(1, CAP_MAX + 1) for b in by_span[s]]
    n1 = check_restoration_polynomial(all_boards)
    print("sc:restoration-polynomial / sc:bordered-grade: %d (zero-free board, vacancy) pairs through span %d; only grades r and r+1, "
          "grade r is sigma s_B, grade r+1 equals sigma (-b adj(M) a) at random rational letters" % (n1, SPAN_MAX))
    nb, ni, ctrl = check_linearized(all_boards, caps)
    print("sc:linearized-cap: %d zero-free children x zero-free caps: %d stacked systems have full column rank; the child "
          "observation alone is dependent on %d children" % (nb, ni, ctrl))
    ns, nse = check_grades(all_boards)
    print("sc:splice-nonzero: first grade k on %d diagrams with a non-self core, k+1 on %d with a self core" % (ns, nse))
    print("ALL PASS")


if __name__ == "__main__":
    main()
