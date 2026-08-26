#!/usr/bin/env python3
r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude),
`fig:decomposition-and-defect` caption.

Consistency audit: verify every numeric claim in the caption of
fig:decomposition-and-defect, and the statement/proof bookkeeping that
depends on those numbers.

Every literal compared against here is READ OUT OF THE MANUSCRIPT, never kept
beside it: the plotted coordinate lists, the axis ticks, the caption's
truncated endpoints and cor:panel-B-attractor's digits for z_*.  Drift between
the manuscript and the figure generator is what this script exists to catch, so
a second copy of any of them would defeat it.  make_figure_pole_geom.py must
therefore run first, and run_all.sh orders them that way.

Paper: shields-2026-forgacs-tran-numerators.tex
Figure setting throughout: Q(t) = (1-t)(1-t/2)(1-t/4), r = 1.

Claims checked (caption text in quotes):
  C0  the manuscript's `fig:decomposition-and-defect` is make_figure_pole_geom.py's current output,
      verbatim -- which is why that generator must run first
  C1  "I_{Q,r} = (0.0559..., 3.7466...)" truncates the computed endpoints, and
      panel B's `extra x ticks` are those endpoints to their printed places
  C2  lem:laurent-reduction leaves N = 7t^2+8 unshifted: lambda_N = 0 and
      B_N = N, so P_m = F_m
  C3  "t_+(pi/2) = i sqrt(8/7) and z(pi/2) = 45/28", so B(t_+(pi/2)) = 0
  C4  the lower/upper endpoint exponent p = -1, so the envelope |W| -> infinity
  C5  panel B: N = (1+z+z^2) + t(2-z) has lambda_N = -2, so
      eq:exact-eventual-degree-shift gives deg P_m = (m - lambda_N)/r = m+2
  C6  panel B: at m = 14 and m = 38, exactly m simple zeros in I_{Q,r} and
      exactly two elsewhere, one conjugate pair, "agreeing to thirteen decimals
      at the two indices"; the pair matches every marker the manuscript plots
      for it and truncates to cor:panel-B-attractor's printed digits for z_*
  C7  panel B's plotted zero lists, parsed from the manuscript, match the
      computed zeros to each coordinate's own printed precision
  C8  eq:dominance-bound |R_M| <= |W|/2 fails only within 1e-11 of theta_1 at M=14
"""

import re
from pathlib import Path

import mpmath as mp

from render_figures import FIGURES, find_environment

mp.mp.dps = 60

R = 1  # r = 1 throughout the figure

PAPER = (Path(__file__).resolve().parent.parent
         / "shields-2026-forgacs-tran-numerators.tex")
GENERATED = Path(__file__).resolve().parent / "figure_pole_geom.tex"
FIGURE_LABEL = "fig:decomposition-and-defect"


# ------------------------------------------ the manuscript's own figure block
# The figure float, its two axis environments and their \addplot payloads are
# walked by brace depth, through render_figures.find_environment -- the same
# route render_figures.py takes to typeset the panels, so both scripts see the
# same structure.  The only regexes below run INSIDE a coordinate group or on a
# numeric option value, never over LaTeX at large, and each one asserts that it
# matched: a regex over LaTeX that silently matches nothing is exactly how a
# check like this passes while testing nothing.
def _match_brace(text, i):
    """Index just past the '}' that closes the '{' at text[i]."""
    assert text[i] == "{", text[i:i + 20]
    depth, j = 1, i + 1
    while depth:
        assert j < len(text), "unterminated brace group"
        depth += {"{": 1, "}": -1}.get(text[j], 0)
        j += 1
    return j


def figure_block(path):
    """(whole file, the `figure` environment holding `fig:decomposition-and-defect`) of a .tex."""
    text = path.read_text(encoding="utf-8")
    figure, _ = find_environment(text, "figure", must_contain=FIGURE_LABEL)
    return text, figure


def axis_bodies(figure):
    """The axis environments of a figure float, in source order."""
    picture, _ = find_environment(figure, "tikzpicture")
    panels, pos = [], 0
    while True:
        try:
            body, (_, j) = find_environment(picture, "axis", start=pos)
        except LookupError:
            break
        panels.append(body)
        pos = j
    return panels


def addplot_blocks(axis_body):
    """[(legend, [(x, y), ...])] for each \addplot of an axis, in source order.

    Coordinates come back as the manuscript's own decimal STRINGS, since how
    many places a coordinate is printed to is what bounds its error.
    """
    starts = [i for i in range(len(axis_body))
              if axis_body.startswith(r"\addplot", i)]
    assert starts, "axis carries no \\addplot"
    blocks = []
    for k, i in enumerate(starts):
        stop = starts[k + 1] if k + 1 < len(starts) else len(axis_body)
        chunk = axis_body[i:stop]
        c = chunk.find("coordinates")
        assert c >= 0, f"\\addplot {k} does not plot a coordinate list"
        b = chunk.index("{", c)
        end = _match_brace(chunk, b)
        pts = [tuple(v.strip() for v in m.group(1).split(","))
               for m in re.finditer(r"\(([^()]*)\)", chunk[b + 1:end - 1])]
        assert pts, f"\\addplot {k} parsed to an empty coordinate list"
        assert all(len(pt) == 2 for pt in pts), f"\\addplot {k} is not planar"
        rest = chunk[end:]
        li = rest.find(r"\addlegendentry")
        legend = None
        if li >= 0:
            lb = rest.index("{", li)
            legend = rest[lb + 1:_match_brace(rest, lb) - 1]
        blocks.append((legend, pts))
    return blocks


def half_ulp(printed):
    """Half a unit in the last printed place of a decimal literal.

    A coordinate written with k decimals is within 5e-(k+1) of whatever it was
    rounded from, so this is the bound the manuscript's own digits promise.  It
    is per-coordinate rather than one blanket tolerance, so it tightens by
    itself when a value is printed to more places.
    """
    frac = printed.split(".")[1] if "." in printed else ""
    return mp.mpf(5) * mp.mpf(10) ** -(len(frac) + 1)


def truncates_to(value, printed):
    """Does `value` truncate to the decimal literal `printed`, at its places?"""
    k = len(printed.split(".")[1]) if "." in printed else 0
    return mp.floor(value * 10**k) / 10**k == mp.mpf(printed)


TEX, FIGURE_BODY = figure_block(PAPER)
PANELS = axis_bodies(FIGURE_BODY)
_EXPECTED = dict(FIGURES)[FIGURE_LABEL]
assert len(PANELS) == len(_EXPECTED), (
    f"`fig:decomposition-and-defect` should carry {len(_EXPECTED)} panels, found {len(PANELS)}")
PANEL_A, PANEL_B = (addplot_blocks(body) for body in PANELS)
for _k, (_blocks, _want) in enumerate(zip((PANEL_A, PANEL_B), _EXPECTED)):
    assert len(_blocks) == _want, (
        f"panel {_k + 1}: expected {_want} \\addplot blocks, parsed "
        f"{len(_blocks)} -- the figure changed, or the parse is wrong")
print(f"read `fig:decomposition-and-defect` from {PAPER.name}: "
      f"{len(PANEL_A)} + {len(PANEL_B)} plotted coordinate blocks")

# Q(t) = (1-t)(1-t/2)(1-t/4) = 1 - (7/4)t + (7/8)t^2 - (1/8)t^3
XS = [mp.mpf(1), mp.mpf(2), mp.mpf(4)]
QC = [mp.mpf(1), -mp.mpf(7) / 4, mp.mpf(7) / 8, -mp.mpf(1) / 8]  # ascending


def poly(coeffs, t):
    """Evaluate sum coeffs[k] t^k."""
    return sum(c * t**k for k, c in enumerate(coeffs))


def Q(t):
    return poly(QC, t)


def dQ(t):
    return sum(k * c * t ** (k - 1) for k, c in enumerate(QC) if k >= 1)


def check_Q_expansion():
    prod = lambda t: (1 - t) * (1 - t / 2) * (1 - t / 4)
    for t in [mp.mpf("0.3"), mp.mpf("2.7"), mp.mpf(-1), mp.mpc(0, 1)]:
        assert abs(prod(t) - Q(t)) < mp.mpf(10) ** -40, t
    print("Q expansion 1 - 7t/4 + 7t^2/8 - t^3/8 .......... OK")


def check_C0():
    """`fig:decomposition-and-defect` in the manuscript is make_figure_pole_geom.py's current output.

    The generator writes the whole float -- axes, coordinates, caption -- and
    the manuscript inlines it verbatim, so byte equality of the two `figure`
    environments is the invariant, and a regenerated figure that was never
    re-inlined fails here rather than silently disagreeing with the caption.
    This is what makes make_figure_pole_geom.py a prerequisite of this script
    rather than merely something run before it.
    """
    assert GENERATED.exists(), (
        f"{GENERATED.name} is missing -- run make_figure_pole_geom.py first")
    _, generated = figure_block(GENERATED)
    assert generated == FIGURE_BODY, (
        f"the manuscript's `fig:decomposition-and-defect` and {GENERATED.name} differ: re-run "
        "make_figure_pole_geom.py and re-inline its output")
    print(f"C0  manuscript's `fig:decomposition-and-defect` is {GENERATED.name} verbatim ... OK")


# ---------------------------------------------------------------- C1: a and b
def endpoints():
    """t_a = smallest positive critical point of g = -Q/t^r; t_b = the
    negative one (r = 1).  Critical points solve r Q(t) - t Q'(t) = 0."""
    crit = lambda t: R * Q(t) - t * dQ(t)
    # r Q - t Q' = 1 - (7/8)t^2 + (1/4)t^3  (r = 1)
    cc = [mp.mpf(1), mp.mpf(0), -mp.mpf(7) / 8, mp.mpf(1) / 4]
    for t in [mp.mpf("0.5"), mp.mpf("3.1"), mp.mpf(-2)]:
        assert abs(poly(cc, t) - crit(t)) < mp.mpf(10) ** -40
    roots = mp.polyroots([c for c in reversed(cc)], maxsteps=200, extraprec=200)
    real = sorted(mp.re(z) for z in roots if abs(mp.im(z)) < mp.mpf(10) ** -30)
    pos = [t for t in real if t > 0]
    neg = [t for t in real if t < 0]
    t_a, t_b = min(pos), max(neg)
    g = lambda t: -Q(t) / t**R
    return t_a, t_b, g(t_a), g(t_b)


T_A, T_B, A_END, B_END = endpoints()


def check_C1():
    print(f"  t_a = {mp.nstr(T_A, 12)}   t_b = {mp.nstr(T_B, 12)}")
    print(f"  a   = {mp.nstr(A_END, 12)}   b   = {mp.nstr(B_END, 12)}")
    # panel B's endpoint ticks, as the manuscript prints them
    m = re.search(r"extra x ticks=\{([^}]*)\}", PANELS[1])
    assert m, "panel B carries no `extra x ticks` option"
    ticks = [v.strip() for v in m.group(1).split(",")]
    assert len(ticks) == 2, ticks
    for name, printed, computed in (("a", ticks[0], A_END),
                                    ("b", ticks[1], B_END)):
        err = abs(mp.mpf(printed) - computed)
        assert err <= half_ulp(printed), (name, printed, mp.nstr(err, 8))
        print(f"  axis tick {name} = {printed} (manuscript), "
              f"|tick - computed| = {mp.nstr(err, 4)} of a permitted "
              f"{mp.nstr(half_ulp(printed), 4)}")
    # the caption's truncated interval, also as the manuscript prints it
    m = re.search(r"I_\{Q,r\}=\(([0-9.]+)\\ldots,([0-9.]+)\\ldots\)", FIGURE_BODY)
    assert m, "the caption does not state I_{Q,r} in the expected form"
    a_cap, b_cap = m.groups()
    assert truncates_to(A_END, a_cap), (a_cap, mp.nstr(A_END, 12))
    assert truncates_to(B_END, b_cap), (b_cap, mp.nstr(B_END, 12))
    assert A_END > 0, "smallest zero of Q simple => a > 0"
    print(f"C1  caption's I_(Q,r) = ({a_cap}..., {b_cap}...) truncates "
          "the computed endpoints  OK")


# ------------------------------------------------- C2/C5: the Laurent reduction
def shifted_restriction(N_coeffs, E):
    """A(t) = t^{rE} L_N(t), where L_N(t) = N(t, -Q(t)/t^r) is the Laurent
    restriction of eq:Laurent-restriction and E = deg_z N.

    Multiplying by t^{rE} clears the negative powers, so A is a polynomial.
    The canonical factorization L_N = t^{lambda_N} B_N of
    lem:laurent-reduction is then read off it: with mu = ord_0 A,

        lambda_N = mu - rE,     B_N(t) = A(t)/t^mu,

    and B_N(0) != 0 by construction.

    N_coeffs[beta] is the list of t-coefficients of the z^beta part.
    Returns ascending coefficient list of A.
    """
    # work with polynomials as ascending coefficient lists
    def pmul(p, q):
        out = [mp.mpf(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return out

    def padd(p, q):
        n = max(len(p), len(q))
        return [
            (p[i] if i < len(p) else mp.mpf(0)) + (q[i] if i < len(q) else mp.mpf(0))
            for i in range(n)
        ]

    total = [mp.mpf(0)]
    for beta, nb in enumerate(N_coeffs):
        if all(c == 0 for c in nb):
            continue
        # term: t^{alpha} * (-1)^beta Q^beta * t^{r(E-beta)}
        Qb = [mp.mpf(1)]
        for _ in range(beta):
            Qb = pmul(Qb, QC)
        sign = mp.mpf(-1) ** beta
        shift = R * (E - beta)
        piece = pmul(nb, [sign * c for c in Qb])
        piece = [mp.mpf(0)] * shift + piece
        total = padd(total, piece)
    while len(total) > 1 and total[-1] == 0:
        total.pop()
    return total


def check_C2():
    # N = 7t^2 + 8 is free of z, so E = 0 and A = L_N is already a polynomial
    # with mu = 0.  Hence lambda_N = mu - rE = 0 and B_N = N, and
    # eq:reduction-coeff reads P_m = F_{m - lambda_N} = F_m.
    N = [[mp.mpf(8), mp.mpf(0), mp.mpf(7)]]  # z^0 part only
    A = shifted_restriction(N, E=0)
    assert [mp.nstr(c, 8) for c in A] == ["8.0", "0.0", "7.0"], A
    mu = next(i for i, c in enumerate(A) if c != 0)
    assert mu == 0 and A[0] != 0
    lam = mu - R * 0
    assert lam == 0, ("lambda_N must vanish here", lam)
    print("C2  lambda_N = 0, B_N = 7t^2+8, so P_m = F_m ... OK")
    return A


def check_C5():
    # N = (1 + z + z^2) + t(2 - z):  z^0 -> 1 + 2t, z^1 -> 1 - t, z^2 -> 1
    N = [
        [mp.mpf(1), mp.mpf(2)],
        [mp.mpf(1), -mp.mpf(1)],
        [mp.mpf(1)],
    ]
    E = 2
    A = shifted_restriction(N, E)
    mu = next(i for i, c in enumerate(A) if c != 0)
    lam = mu - R * E                       # lambda_N of lem:laurent-reduction
    d = max(len(QC) - 1, R)
    assert d == 3
    assert max(len(part) - 1 for part in N) < d, "properness deg_t N < d"
    assert mu == 0, mu
    assert lam == -2, lam
    B_N = A[mu:]
    assert B_N[0] != 0, "B_N(0) != 0 is part of the canonical factorization"
    print(f"  A(0) = {mp.nstr(A[0], 8)}, mu = {mu}, lambda_N = {lam}, "
          f"deg B_N = {len(B_N) - 1}")
    print(f"C5  P_m = F_(m-lambda_N) = F_(m+{-lam}), so "
          f"deg P_m = floor((m-lambda_N)/r) = m+{-lam} ... OK")
    return B_N, lam


# ------------------------------------------- C3: the amplitude zero at theta_1
def principal_pair(theta):
    """Solve for tau > 0 and z real with Q(tau e^{i theta}) + z (tau e^{i
    theta})^r = 0.  Im part determines tau, Re part then gives z."""
    e = mp.expjpi(theta / mp.pi)

    def imres(tau):
        t = tau * e
        return mp.im(Q(t) / t**R)

    lo, hi = mp.mpf("1e-8"), mp.mpf(50)
    tau = mp.findroot(imres, mp.mpf("1.0"), solver="secant", tol=mp.mpf(10) ** -50)
    if not (tau > 0):
        tau = mp.findroot(imres, [lo, hi], solver="bisect")
    t = tau * e
    z = -mp.re(Q(t) / t**R)
    assert abs(Q(t) + z * t**R) < mp.mpf(10) ** -40, abs(Q(t) + z * t**R)
    return tau, z, t


def check_C3():
    tau, z, tp = principal_pair(mp.pi / 2)
    print(f"  tau(pi/2) = {mp.nstr(tau, 20)}   sqrt(8/7) = {mp.nstr(mp.sqrt(mp.mpf(8)/7), 20)}")
    print(f"  z(pi/2)   = {mp.nstr(z, 20)}   45/28     = {mp.nstr(mp.mpf(45)/28, 20)}")
    assert abs(tau - mp.sqrt(mp.mpf(8) / 7)) < mp.mpf(10) ** -40
    assert abs(z - mp.mpf(45) / 28) < mp.mpf(10) ** -40
    assert abs(tp - mp.mpc(0, 1) * mp.sqrt(mp.mpf(8) / 7)) < mp.mpf(10) ** -40
    B = lambda t: 7 * t**2 + 8
    assert abs(B(tp)) < mp.mpf(10) ** -40, abs(B(tp))
    assert A_END < z < B_END, "theta_1 must sit inside the parameter interval"
    print("C3  t_+(pi/2)=i sqrt(8/7), z=45/28, B(t_+)=0 ... OK")
    return tau, z, tp


# ------------------------------------------------- C4: the endpoint exponent p
def check_C4():
    """p = nu - (k-1) at a finite endpoint; k = max{rho,2} (lower), 2 (upper);
    nu = order of vanishing of B at t_e."""
    B = lambda t: 7 * t**2 + 8
    rho = sum(1 for x in XS if x == min(XS))
    assert rho == 1, "smallest zero of Q is simple"
    for name, t_e in (("lower", T_A), ("upper", T_B)):
        k = max(rho, 2) if name == "lower" else 2
        assert k == 2
        nu = 0 if abs(B(t_e)) > mp.mpf(10) ** -30 else None
        assert nu == 0, f"B({name} endpoint) = {mp.nstr(B(t_e), 8)} != 0"
        p = nu - (k - 1)
        assert p == -1, p
        print(f"  {name} endpoint: t_e={mp.nstr(t_e,8)}, k={k}, nu={nu}, p={p}")
    print("C4  p = -1 at both endpoints, so |W| -> infinity  OK")


# -------------------------------------------- C6/C7: the panel-B zero pictures
def coeff_series(Bco, z, nmax):
    """[t^n] B(t)/(Q(t)+z t^r) for n = 0..nmax, by long division."""
    D = [c for c in QC]
    while len(D) <= R:
        D.append(mp.mpf(0))
    D[R] = D[R] + z
    out = []
    num = list(Bco) + [mp.mpf(0)] * (nmax + 1 + len(D))
    for n in range(nmax + 1):
        c = num[n] / D[0]
        out.append(c)
        for j, dj in enumerate(D):
            num[n + j] -= c * dj
    return out


def P_m_coeffs(Bco, lam, m, deg):
    """Coefficients of P_m(z) = F_{m-lambda_N}(z), degree deg, by interpolation
    at deg+1 nodes -- each node is one exact power-series division."""
    M = m - lam
    nodes = [mp.mpf(2) * j / (deg + 1) - 1 for j in range(deg + 1)]
    nodes = [n + mp.mpf("0.37") for n in nodes]  # avoid symmetric cancellation
    vals = [coeff_series(Bco, zz, M)[M] for zz in nodes]
    # Lagrange -> monomial coefficients via Vandermonde solve
    Amat = mp.matrix(deg + 1, deg + 1)
    for i, zz in enumerate(nodes):
        for j in range(deg + 1):
            Amat[i, j] = zz**j
    sol = mp.lu_solve(Amat, mp.matrix(vals))
    return [sol[j] for j in range(deg + 1)]


def check_C6_C7(Bco, lam):
    tol_in = mp.mpf(10) ** -25
    pair_by_m = {}
    for m in (14, 38):
        deg = m - lam
        co = P_m_coeffs(Bco, lam, m, deg)
        assert abs(co[deg]) > mp.mpf(10) ** -30, "leading coefficient must not vanish"
        roots = mp.polyroots(
            [co[k] for k in range(deg, -1, -1)], maxsteps=400, extraprec=400
        )
        inside, outside = [], []
        for zz in roots:
            if abs(mp.im(zz)) < tol_in and A_END < mp.re(zz) < B_END:
                inside.append(mp.re(zz))
            else:
                outside.append(zz)
        inside.sort()
        print(f"  m={m}: deg P_m = {deg}, |inside I| = {len(inside)}, "
              f"|outside| = {len(outside)}")
        assert deg == m + 2, deg
        assert len(inside) == m, (m, len(inside))
        assert len(outside) == 2, (m, len(outside))
        # simple zeros inside: consecutive gaps well above numerical noise
        gaps = [inside[i + 1] - inside[i] for i in range(len(inside) - 1)]
        assert min(gaps) > mp.mpf(10) ** -6, min(gaps)
        # the outside pair is a conjugate pair
        o = sorted(outside, key=lambda w: mp.im(w))
        assert abs(o[0] - mp.conj(o[1])) < mp.mpf(10) ** -25
        pair_by_m[m] = o[1]
        print(f"        exceptional pair = {mp.nstr(mp.re(o[1]), 16)} "
              f"+- {mp.nstr(mp.im(o[1]), 16)} i")
        # cor:panel-B-attractor's printed digits for z_*, read from the .tex
        d = re.search(r"z_\*=-([0-9]+\.[0-9]+)\\ldots\+([0-9]+\.[0-9]+)\\ldots i",
                      TEX)
        assert d, "cor:panel-B-attractor does not state z_* in the expected form"
        re_lit, im_lit = d.groups()
        assert truncates_to(-mp.re(o[1]), re_lit), (re_lit, mp.nstr(mp.re(o[1]), 18))
        assert truncates_to(mp.im(o[1]), im_lit), (im_lit, mp.nstr(mp.im(o[1]), 18))
        # every marker the manuscript plots for the pair, at its own precision
        marks = [pts for _, pts in PANEL_B
                 if all(mp.mpf(x) < 0 and mp.mpf(y) != 0 for x, y in pts)]
        assert len(marks) == 3, (
            f"expected three plotted markers for the exceptional pair, "
            f"parsed {len(marks)}")
        for pts in marks:
            assert len(pts) == 2, pts
            for x, y in pts:
                want = o[1] if mp.mpf(y) > 0 else mp.conj(o[1])
                for printed, computed in ((x, mp.re(want)), (y, mp.im(want))):
                    err = abs(mp.mpf(printed) - computed)
                    assert err <= half_ulp(printed), (
                        m, printed, mp.nstr(err, 8))
        globals().setdefault("_INSIDE", {})[m] = inside
    d = abs(pair_by_m[14] - pair_by_m[38])
    print(f"  |pair(14) - pair(38)| = {mp.nstr(d, 6)}")
    assert d < mp.mpf("1e-13"), mp.nstr(d, 6)
    print(f"  the pair matches all {len(marks)} plotted markers and "
          "cor:panel-B-attractor's digits, each to its own printed place")
    print("C6  m simple zeros in I + exactly one conjugate pair,")
    print("    agreeing to 13 decimals across m=14,38 ......... OK")


def check_C7_plotted():
    for m in (14, 38):
        legend = r"\(m=%d\)" % m
        found = [pts for leg, pts in PANEL_B if leg == legend]
        assert len(found) == 1, (
            f"panel B should carry exactly one plot legended {legend}, "
            f"parsed {len(found)}")
        plotted = found[0]
        assert len(plotted) == m, (m, len(plotted))
        computed = _INSIDE[m]
        assert len(computed) == m, (m, len(computed))
        xs = [mp.mpf(x) for x, _ in plotted]
        assert all(xs[i] < xs[i + 1] for i in range(m - 1)), \
            f"m={m}: the manuscript's zeros are not in ascending order"
        worst = mp.mpf(0)
        for (x, y), c in zip(plotted, computed):
            assert mp.mpf(y) == 0, (m, x, y)          # the bulk is real
            assert A_END < mp.mpf(x) < B_END, (m, x)
            err = abs(mp.mpf(x) - c)
            assert err <= half_ulp(x), (m, x, mp.nstr(err, 8))
            worst = max(worst, err / half_ulp(x))
        print(f"  m={m}: {len(plotted)} zeros read from the manuscript, all in "
              f"I, worst error {mp.nstr(worst, 4)} of its own printed half-ulp")
    print("C7  manuscript's plotted zeros match computed zeros  OK")


# ------------------------------- C8: where the dominance inequality really fails
def W_and_R(Bco, theta, M):
    """Return |W(theta)| and |R_M(theta)| for the decomposition
    tau^{M+1} F_M(z(theta)) = 2 Re(W e^{-i(M+1)theta}) + R_M."""
    tau, z, tp = principal_pair(theta)
    Bv = lambda t: poly(Bco, t)
    dD = dQ(tp) + R * z * tp ** (R - 1)
    W = -Bv(tp) / dD
    full = tau ** (M + 1) * coeff_series(Bco, z, M)[M]
    principal = 2 * mp.re(W * mp.expjpi(-(M + 1) * theta / mp.pi))
    return abs(W), abs(full - principal)


def check_C8(Bco):
    M = 14
    th1 = mp.pi / 2
    print("  offset from theta_1   |R_M|/|W|   dominance |R|<=|W|/2 ?")
    prev_bad = None
    for e in range(4, 15):
        off = mp.mpf(10) ** -e
        for s in (+1, -1):
            aW, aR = W_and_R(Bco, th1 + s * off, M)
            ratio = aR / aW
            ok = ratio <= mp.mpf("0.5")
            if s == +1:
                print(f"    1e-{e:<2d}            {mp.nstr(ratio, 6):>12}   "
                      f"{'yes' if ok else 'NO'}")
            if not ok:
                prev_bad = max(prev_bad or 0, e)
    # claim: fails only within 1e-11 of theta_1
    aW, aR = W_and_R(Bco, th1 + mp.mpf(10) ** -11, M)
    assert aR / aW <= mp.mpf("0.5"), "should already hold at 1e-11"
    aW, aR = W_and_R(Bco, th1 + mp.mpf(10) ** -13, M)
    assert aR / aW > mp.mpf("0.5"), "should fail well inside 1e-11"
    print("C8  dominance holds at 1e-11, fails by 1e-13 .... OK")
    print("    (caption's 'fails only within 1e-11' is an upper bound: sound)")


if __name__ == "__main__":
    check_C0()
    check_Q_expansion()
    check_C1()
    B1 = check_C2()
    check_C3()
    check_C4()
    B2, lam2 = check_C5()
    check_C6_C7(B2, lam2)
    check_C7_plotted()
    check_C8(B1)
    print("\nALL PASS: consistency_figure_claims")
