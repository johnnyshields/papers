r"""Paper section `app:coincident` (Positive coincident attachment phases).

The signed coincident charge on line counterparts (`app:coincident`, `eq:coincident-charge`,
`lem:one-coincident-entry`, `eq:all-coincident-clocks`).

For every legal ordinary mark `omega` (cases (a) and (b)) on a small connected skew `E`:

* the read-outer offset `theta` is read off the inner alone, `V_p s_E = theta delta_p s_E`;
* in case (a), `theta = s - t` for the phases of the middle;
* on a row outer of `J` cells the clock `D_p(lam) = V_p - lam delta_p` kills the composite
  function at `lam = eps p (J - 1) + theta`, with `eps = 1` in case (a) (read-outer `h_J`) and
  `eps = -1` in case (b) (read-outer `omega(h_J)`), and at no other `lam`;
* with `u = w - |theta|`, that clock is `eps (N - p - u)` when `theta` is zero or has the sign
  `eps`, and `eps (N - p - u - 2 |theta|)` otherwise, so the sign clause of the charge is what
  makes the clock one of the three whole equations.  The paper settles the sign by the low
  corner; on these boards every ordinary mark already has `theta` of sign `eps` or zero.

Cells are `(i, j)` with rows increasing southward; `content (i, j) = j - i`.
"""

import sys

import sympy as sp

from check_chart_witnesses import schur
from check_regroup_mixed import (content, legal_marks, max_content, min_content, skew_shapes,
                                 span)

DEG = 24
h = {0: sp.Integer(1)}
h.update({j: sp.Symbol(f"h{j}") for j in range(1, DEG + 1)})


def hall(f, q):
    return sp.expand(sum(sp.diff(f, h[j]) * h[j - q] for j in range(q, DEG + 1)))


def weighted(f, q):
    return sp.expand(sum(sp.diff(f, h[j]) * (j - q) * h[j - q] for j in range(q, DEG + 1)))


def offset_from_inner(m):
    """The unique `theta` with `V_p s_E = theta delta_p s_E`."""
    p = m.period()
    sE = schur(set(m.E), h)
    xi = hall(sE, p)
    assert xi != 0, "ordinary marks have nonzero Hall response"
    th = sp.Symbol("th")
    sol = sp.solve(sp.Poly(weighted(sE, p) - th * xi, *[h[j] for j in range(1, DEG + 1)]).coeffs(),
                   th)
    assert len(sol) == 1
    return int(sol[th])


def phases(m):
    O = m.middle()
    s = min_content(O) - min_content(m.E)
    t = max_content(O) - min_content(m.E) - m.period() + 1
    return s, t


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    n_marks = n_comp = match = opposite = zero = 0
    for E in skew_shapes(nmax, 3, 4):
        for m in legal_marks(E):
            if m.case not in "ab":
                continue
            n_marks += 1
            p, w = m.period(), m.width()
            theta = offset_from_inner(m)
            assert abs(theta) < p
            if m.case == "a":
                s, t = phases(m)
                assert theta == s - t, (sorted(E), sorted(m.W), m.v, theta, s, t)
            eps = 1 if m.case == "a" else -1
            for J in (2, 3):
                D = frozenset((0, j) for j in range(J))
                P = m.compose(D)
                sP = schur(set(P), h)
                N = span(P)
                assert N == J * p + w
                lam_line = eps * p * (J - 1) + theta
                assert sp.expand(weighted(sP, p) - lam_line * hall(sP, p)) == 0
                # no other clock value kills the composite
                assert hall(sP, p) != 0
                n_comp += 1
                u = w - abs(theta)
                if theta == 0:
                    zero += 1
                    assert lam_line == eps * (N - p - u)
                elif (theta > 0) == (eps > 0):
                    match += 1
                    assert lam_line == eps * (N - p - u)
                else:
                    opposite += 1
                    assert lam_line == eps * (N - p - u - 2 * abs(theta))
                    assert abs(lam_line) != N - p - u
    print(f"ordinary marks {n_marks}, composites {n_comp}: theta = 0 {zero}, "
          f"sign matches read-outer {match}, opposite {opposite}")
    assert n_marks > 0 and match > 0 and zero > 0
    print("PASS")


if __name__ == "__main__":
    main()
