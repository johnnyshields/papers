#!/usr/bin/env python3
r"""Paper section `sec:consequences` (Global and local zero laws),
`fig:clock-collapse` caption.

Consistency audit: verify every numeric claim in the caption of
fig:clock-collapse, and the plotted data those claims are about.

Every literal compared against here is READ OUT OF THE MANUSCRIPT, never kept
beside it: the denominator and r (taken from the caption of the figure this one
names as its source), the weight, the subarc J, the rescaling exponent, the
three indices, the percentage, the plotted marker and curve coordinates, and
the axis window and ticks.  Drift between the manuscript and the figure
generator is what this script exists to catch, so a second copy of any of them
would defeat it.  make_figure_clock_collapse.py must therefore run first, and
run_all.sh orders them that way.

The zeros, the amplitude and psi' are recomputed here from the coefficient
recurrence through check_local_clock.py -- the script that verifies
`prop:local-strong-clock` -- so the caption is audited against the proposition's
own machinery and never against the plotted numbers it is describing.

Paper: shields-2026-forgacs-tran-numerators.tex

Claims checked (caption text in quotes):
  C0  the manuscript's `fig:clock-collapse` is make_figure_clock_collapse.py's
      current output, verbatim -- which is why that generator must run first
  C1  "for the denominator of `fig:decomposition-and-defect` and the weight
      B(t)=1+t": that denominator and its r, parsed from the other figure's own
      caption, satisfy `eq:Q-hypotheses`, and J is a compact subarc of (0,pi/r)
  C2  "on which the principal residue amplitude does not vanish": min |W| over J
      is positive, W being `eq:residue-amplitude` at the principal pair, which is
      verified to be the minimum-modulus pair
  C3  "at three indices": the caption's and the body sentence's word agrees with
      the number of plotted marker series, whose M values are the legends
  C4  "over the consecutive bulk zero angles with theta_{k,M} and theta_{k+1,M}
      both in J": the plotted abscissas are exactly those zero angles, to each
      coordinate's own printed precision, with none omitted and none added
  C5  the caption's S_{k,M} formula, recomputed from the recurrence at each
      plotted gap, matches every plotted ordinate to its printed precision
  C6  "the solid curve is psi', computed from that amplitude alone": every
      plotted curve coordinate is psi'(theta) to its printed precision, and psi'
      genuinely varies across J
  C7  "the markers tighten onto the curve as M grows", at the O(M^-1) the
      caption attributes to `prop:local-strong-clock`; and the agreement is not
      fitted -- the least-squares affine map from psi' to the markers tends to
      the identity as M grows, rather than being tuned to it
  C8  "the correction is under 4% of the clock pi/(M+1) itself": the printed
      integer bounds every plotted gap and is the least integer that does
  C9  the axis window holds every plotted coordinate (`clip=true` would hide
      one that escaped it) and all of J, and every tick lies inside its range

Cost: about 40 s, dominated by the M = 44 zero hunt at 50 digits.
"""

import re
from pathlib import Path

import mpmath
import sympy as sp
from mpmath import mp, mpf

import check_local_clock as clk
from render_figures import FIGURES, find_environment

mp.dps = 50

PAPER = (Path(__file__).resolve().parent.parent
         / "shields-2026-forgacs-tran-numerators.tex")
GENERATED = Path(__file__).resolve().parent / "figure_clock_collapse.tex"
FIGURE_LABEL = "fig:clock-collapse"

_t = sp.symbols("t")


# ------------------------------------------------- the manuscript's own figure
# The figure float, its axis environment, the \addplot payloads and the caption
# are walked by brace depth, through render_figures.find_environment -- the same
# route render_figures.py takes to typeset the panel.  Every regex below runs
# INSIDE a caption, a coordinate group or a numeric option value, never over
# LaTeX at large, and each one asserts that it matched: a regex over LaTeX that
# silently matches nothing is exactly how a check like this passes while testing
# nothing.
def _match_brace(text, i):
    """Index just past the '}' that closes the '{' at text[i]."""
    assert text[i] == "{", text[i:i + 20]
    depth, j = 1, i + 1
    while depth:
        assert j < len(text), "unterminated brace group"
        depth += {"{": 1, "}": -1}.get(text[j], 0)
        j += 1
    return j


def figure_block(path_or_text, label=FIGURE_LABEL):
    """(whole text, the `figure` environment carrying `label`)."""
    text = (path_or_text.read_text(encoding="utf-8")
            if isinstance(path_or_text, Path) else path_or_text)
    figure, _ = find_environment(text, "figure", must_contain=label)
    return text, figure


def caption_of(figure):
    i = figure.find(r"\caption")
    assert i >= 0, "figure carries no \\caption"
    b = figure.index("{", i)
    return figure[b + 1:_match_brace(figure, b) - 1]


def axis_body(figure):
    picture, _ = find_environment(figure, "tikzpicture")
    body, _ = find_environment(picture, "axis")
    return body


def addplot_blocks(axis):
    r"""[(legend, [(x, y), ...])] for each \addplot, in source order.

    Coordinates come back as the manuscript's own decimal STRINGS, since how
    many places a coordinate is printed to is what bounds its error.
    """
    starts = [i for i in range(len(axis)) if axis.startswith(r"\addplot", i)]
    assert starts, "axis carries no \\addplot"
    blocks = []
    for k, i in enumerate(starts):
        stop = starts[k + 1] if k + 1 < len(starts) else len(axis)
        chunk = axis[i:stop]
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
        assert li >= 0, f"\\addplot {k} carries no legend entry"
        lb = rest.index("{", li)
        blocks.append((rest[lb + 1:_match_brace(rest, lb) - 1], pts))
    return blocks


def option(axis, name):
    """The value of a `name=<number>` axis option, as the manuscript writes it."""
    m = re.search(rf"\b{name}=(-?[0-9.]+)\s*,", axis)
    assert m, f"axis carries no `{name}` option"
    return m.group(1)


def tick_list(axis, name):
    m = re.search(rf"\b{name}=\{{([^}}]*)\}}", axis)
    assert m, f"axis carries no `{name}` option"
    ticks = [v.strip() for v in m.group(1).split(",")]
    assert ticks and all(ticks), f"`{name}` parsed to an empty list"
    return ticks


def half_ulp(printed):
    """Half a unit in the last printed place of a decimal literal.

    A coordinate written with k decimals is within 5e-(k+1) of whatever it was
    rounded from, so this is the bound the manuscript's own digits promise.  It
    is per-coordinate rather than one blanket tolerance, so it tightens by
    itself when a value is printed to more places.
    """
    frac = printed.split(".")[1] if "." in printed else ""
    return mpf(5) * mpf(10) ** -(len(frac) + 1)


def coeffs(expr_text):
    """Ascending mpmath coefficient list of a polynomial written in the .tex."""
    p = sp.Poly(sp.sympify(expr_text.replace(")(", ")*("), locals={"t": _t}), _t)
    out = []
    for k in range(p.degree() + 1):
        c = sp.Rational(p.nth(k))
        out.append(mpf(int(c.p)) / mpf(int(c.q)))
    return out


TEX, FIGURE = figure_block(PAPER)
CAPTION = caption_of(FIGURE)
AXIS = axis_body(FIGURE)
BLOCKS = addplot_blocks(AXIS)
_EXPECTED = dict(FIGURES)[FIGURE_LABEL]
assert len(BLOCKS) == _EXPECTED[0], (
    f"`fig:clock-collapse` should carry {_EXPECTED[0]} \\addplot blocks, "
    f"parsed {len(BLOCKS)} -- the figure changed, or the parse is wrong")

CURVE_LEGEND = r"\(\psi'(\theta)\)"
CURVE = [pts for leg, pts in BLOCKS if leg == CURVE_LEGEND]
assert len(CURVE) == 1, (
    f"expected exactly one plot legended {CURVE_LEGEND}, parsed {len(CURVE)}")
CURVE = CURVE[0]
SERIES = {}
for _leg, _pts in BLOCKS:
    m = re.fullmatch(r"\\\(M=(\d+)\\\)", _leg)
    if m:
        assert int(m.group(1)) not in SERIES, f"two series legended {_leg}"
        SERIES[int(m.group(1))] = _pts
assert len(SERIES) + 1 == len(BLOCKS), (
    "every \\addplot must be either the psi' curve or an M-indexed marker "
    f"series; parsed {len(BLOCKS)} blocks, {len(SERIES)} of them markers")
MS = sorted(SERIES)
print(f"read `fig:clock-collapse` from {PAPER.name}: {len(CURVE)} curve points "
      f"and marker series at M = {', '.join(str(M) for M in MS)}")


# ------------------------------------------------------ the caption's literals
def caption_number(pattern, what):
    m = re.search(pattern, CAPTION)
    assert m, f"the caption does not state {what} in the expected form"
    return m.groups()


SOURCE_LABEL, = caption_number(r"\\Cref\{(fig:[A-Za-z0-9:-]+)\}", "its source figure")
_, SOURCE_FIGURE = figure_block(TEX, SOURCE_LABEL)
SOURCE_CAPTION = caption_of(SOURCE_FIGURE)
_mq = re.search(r"\\\(Q\(t\)=(.+?)\\\)", SOURCE_CAPTION)
assert _mq, f"`{SOURCE_LABEL}` does not state its denominator in the expected form"
QC = coeffs(_mq.group(1))
_mr = re.search(r"\\\(r=(\d+)\\\)", SOURCE_CAPTION)
assert _mr, f"`{SOURCE_LABEL}` does not state r in the expected form"
R_EXP = int(_mr.group(1))
BC = coeffs(caption_number(r"\\\(B\(t\)=([^\\]+)\\\)", "its weight")[0])
J_LO_S, J_HI_S = caption_number(
    r"\\mathcal J=\[([0-9.]+),\s*([0-9.]+)\]", "the subarc J")
J_LO, J_HI = mpf(J_LO_S), mpf(J_HI_S)
EXPO, = caption_number(
    r"\\mathcal S_\{k,M\}=\(M\+1\)\^\{?(\d)\}?\\bigl\(\\theta_\{k\+1,M\}"
    r"-\\theta_\{k,M\}-\\pi/\(M\+1\)\\bigr\)/\\pi", "the rescaling")
EXPO = int(EXPO)
RATE, = caption_number(r"\+O\(M\^\{-(\d)\}\)", "the error term of the spacing law")
RATE = int(RATE)
PCT, = caption_number(r"correction is under\s*(\d+)\\%", "the percentage")
PCT = int(PCT)
WORDS = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5}
INDEX_WORD, = caption_number(r"at (\w+) indices", "how many indices it shows")

print(f"  caption literals: Q(t)={_mq.group(1)}, r={R_EXP}, "
      f"B = {[mpmath.nstr(c, 6) for c in BC]} (ascending), "
      f"J=[{J_LO_S},{J_HI_S}], exponent {EXPO}, O(M^-{RATE}), {PCT}%, "
      f"{INDEX_WORD} indices")


# ----------------------------------------------------------- the recomputation
# tau_of_theta brackets outward from a seed; the seed is a solver input, not a
# claim, and is taken as the smallest positive critical point of g = -Q/t^r,
# which is where tau(theta) starts as theta -> 0.  That the branch found really
# is the minimum-modulus pair is asserted below (C2), not assumed.
def tau_seed():
    n1 = [(R_EXP - k) * c for k, c in enumerate(QC)]      # rQ - tQ'
    while len(n1) > 1 and n1[-1] == 0:
        n1.pop()
    roots = mpmath.polyroots(list(reversed(n1)), maxsteps=400, extraprec=400)
    pos = [mpmath.re(u) for u in roots
           if abs(mpmath.im(u)) < mpf(10) ** -30 and mpmath.re(u) > 0]
    assert pos, "g has no positive critical point"
    return min(pos)


# The search arc is padded so the zeros just outside J are found too; the pad is
# a computation width, not a claim, and C4 asserts it really did bracket J.
PAD = mpmath.pi / (min(MS) + 1)
CFG = clk.Config("fig-clock", QC, R_EXP, BC, (J_LO - PAD, J_HI + PAD), tau_seed())


def rescaled(M, th, nxt):
    return (M + 1) ** EXPO * ((nxt - th) - mpmath.pi / (M + 1)) / mpmath.pi


ZEROS, GAPS = {}, {}
for _M in MS:
    ZEROS[_M] = clk.zeros_of_G(CFG, _M)
    GAPS[_M] = [(ZEROS[_M][i], ZEROS[_M][i + 1])
                for i in range(len(ZEROS[_M]) - 1)
                if ZEROS[_M][i] >= J_LO and ZEROS[_M][i + 1] <= J_HI]


# --------------------------------------------------------------------- C0
def check_C0():
    """`fig:clock-collapse` in the manuscript is the generator's current output.

    The generator writes the whole float -- axis, coordinates, caption -- and the
    manuscript inlines it verbatim, so byte equality of the two `figure`
    environments is the invariant, and a regenerated figure that was never
    re-inlined fails here rather than silently disagreeing with the caption.
    This is what makes make_figure_clock_collapse.py a prerequisite of this
    script rather than merely something run before it.
    """
    assert GENERATED.exists(), (
        f"{GENERATED.name} is missing -- run make_figure_clock_collapse.py first")
    _, generated = figure_block(GENERATED)
    assert generated == FIGURE, (
        f"the manuscript's `fig:clock-collapse` and {GENERATED.name} differ: "
        "re-run make_figure_clock_collapse.py and re-inline its output")
    print(f"C0  manuscript's `fig:clock-collapse` is {GENERATED.name} verbatim ... OK")


# --------------------------------------------------------------------- C1
def check_C1():
    """The denominator named by the caption, and J compact in (0, pi/r)."""
    assert abs(QC[0] - 1) < mpf(10) ** -40, "Q(0) = 1 is the paper's normalization"
    roots = mpmath.polyroots(list(reversed(QC)), maxsteps=400, extraprec=400)
    xs = sorted(mpmath.re(u) for u in roots)
    assert all(abs(mpmath.im(u)) < mpf(10) ** -30 for u in roots), \
        "`eq:Q-hypotheses` requires real zeros"
    assert all(x > 0 for x in xs), "`eq:Q-hypotheses` requires positive zeros"
    assert R_EXP >= 1, R_EXP
    assert 0 < J_LO < J_HI < mpmath.pi / R_EXP, (J_LO, J_HI, R_EXP)
    clear = min(J_LO, mpmath.pi / R_EXP - J_HI)
    print(f"  zeros of Q: {', '.join(mpmath.nstr(x, 8) for x in xs)}; "
          f"deg B = {len(BC) - 1}, B(0) = {mpmath.nstr(BC[0], 6)}")
    print(f"C1  J = [{J_LO_S},{J_HI_S}] is compact in (0,pi/r) = (0,"
          f"{mpmath.nstr(mpmath.pi / R_EXP, 6)}), clear of both endpoints by "
          f"{mpmath.nstr(clear, 4)} ... OK")


# --------------------------------------------------------------------- C2
def check_C2():
    """The principal residue amplitude does not vanish on J."""
    nroots = clk.assert_principal_branch(CFG)
    grid = [J_LO + (J_HI - J_LO) * mpf(i) / 200 for i in range(201)]
    mods = [abs(CFG.zW(th)[2]) for th in grid]
    wmin = min(mods)
    # W is `eq:residue-amplitude` at the principal root; recompute one value
    # from the factored denominator, so the amplitude the caption names is not
    # taken on trust from a single routine.
    th = grid[100]
    tau, z, W = CFG.zW(th)
    D = list(QC) + [mpf(0)] * max(0, R_EXP + 1 - len(QC))
    D[R_EXP] = D[R_EXP] + z
    while len(D) > 1 and D[-1] == 0:
        D.pop()
    rts = mpmath.polyroots(list(reversed(D)), maxsteps=400, extraprec=400)
    pr = max([u for u in rts if abs(abs(u) - tau) < mpf(10) ** -30],
             key=lambda u: mpmath.im(u))
    lead = D[-1]
    dD = lead * mpmath.fprod([pr - u for u in rts if abs(u - pr) > mpf(10) ** -30])
    W_fac = -clk.poly_val(BC, pr) / dD
    assert abs(W_fac - W) < mpf(10) ** -35 * max(1, abs(W)), (W_fac, W)
    assert wmin > mpf(10) ** -6, "W comes too close to zero on the plotted arc"
    print(f"  D(.,z) has {nroots} roots, so a nonprincipal root is present and "
          f"R_M is a genuine remainder; W from the factored denominator agrees "
          f"to {mpmath.nstr(abs(W_fac - W), 3)}")
    print(f"C2  min |W| on J is {mpmath.nstr(wmin, 6)} > 0, so the caption's "
          "nonvanishing amplitude holds ... OK")


# --------------------------------------------------------------------- C3
def check_C3():
    """"at three indices", in the caption and wherever the body repeats it.

    The body is read through a window after each reference to the figure rather
    than through one fixed sentence, so a reworded paragraph does not fail the
    harness -- but a count or a weight restated there and disagreeing with the
    plot does.  The caption's own statement is not optional: it is asserted
    above, at parse time.
    """
    assert INDEX_WORD in WORDS, INDEX_WORD
    assert WORDS[INDEX_WORD] == len(MS), (INDEX_WORD, MS)
    flat = " ".join(TEX.split())
    refs = [m.end() for m in re.finditer(r"\\Cref\{" + FIGURE_LABEL + r"\}", flat)]
    assert refs, "nothing in the body refers to `fig:clock-collapse`"
    restated = 0
    for i in refs:
        window = flat[i:i + 300]
        for m in re.finditer(r"at (\w+) indices", window):
            assert m.group(1) in WORDS and WORDS[m.group(1)] == len(MS), \
                (m.group(1), MS)
            restated += 1
        for m in re.finditer(r"weight \\\(B\(t\)=([^\\]+)\\\)", window):
            assert coeffs(m.group(1)) == BC, (m.group(1), BC)
            restated += 1
    print(f"C3  the caption says `{INDEX_WORD} indices` for the {len(MS)} plotted "
          f"series M = {MS}; {len(refs)} body reference(s) restate {restated} of "
          "its literals, all agreeing ... OK")


# --------------------------------------------------------------------- C4/C5
def check_C4_C5():
    """The plotted abscissas are the bulk zero angles; the ordinates are S."""
    for M in MS:
        plotted = SERIES[M]
        zs = ZEROS[M]
        assert min(zs) < J_LO and max(zs) > J_HI, (
            f"M={M}: the search arc did not bracket J, so a gap straddling an "
            "endpoint could have been missed")
        gaps = GAPS[M]
        assert len(plotted) == len(gaps), (
            f"M={M}: manuscript plots {len(plotted)} markers against "
            f"{len(gaps)} consecutive gaps inside J")
        xs = [mpf(x) for x, _ in plotted]
        assert all(xs[i] < xs[i + 1] for i in range(len(xs) - 1)), \
            f"M={M}: the plotted markers are not in ascending theta"
        worst_x = worst_y = mpf(0)
        for (x, y), (th, nxt) in zip(plotted, gaps):
            assert J_LO <= mpf(x) <= J_HI, (M, x)
            ex = abs(mpf(x) - th)
            assert ex <= half_ulp(x), (M, x, mpmath.nstr(ex, 8))
            ey = abs(mpf(y) - rescaled(M, th, nxt))
            assert ey <= half_ulp(y), (M, y, mpmath.nstr(ey, 8))
            worst_x = max(worst_x, ex / half_ulp(x))
            worst_y = max(worst_y, ey / half_ulp(y))
        print(f"  M={M}: {len(zs)} zeros on the padded arc, {len(gaps)} gaps "
              f"inside J, worst error {mpmath.nstr(worst_x, 4)} (theta) and "
              f"{mpmath.nstr(worst_y, 4)} (S) of its own printed half-ulp")
    print("C4  plotted abscissas are exactly the consecutive bulk zero angles "
          "with both ends in J ... OK")
    print(f"C5  plotted ordinates are (M+1)^{EXPO}(gap - pi/(M+1))/pi at those "
          "angles ... OK")


# --------------------------------------------------------------------- C6
def check_C6():
    """The curve is psi', computed from the amplitude alone.

    The abscissas are an equally spaced sample of J, so each one is recovered
    from J and the number of points rather than read back off the plot: psi' is
    then evaluated at the sample point itself, not at its rounded printout,
    whose own error would otherwise ride into the ordinate through psi''.
    """
    worst_x = worst = mpf(0)
    n = len(CURVE)
    vals = []
    for i, (x, y) in enumerate(CURVE):
        th = J_LO + (J_HI - J_LO) * mpf(i) / (n - 1)
        ex = abs(mpf(x) - th)
        assert ex <= half_ulp(x), (x, mpmath.nstr(ex, 8))
        worst_x = max(worst_x, ex / half_ulp(x))
        d = CFG.psi_and_deriv(th)[1]
        vals.append(d)
        err = abs(mpf(y) - d)
        assert err <= half_ulp(y), (x, y, mpmath.nstr(err, 8))
        worst = max(worst, err / half_ulp(y))
    assert mpf(CURVE[0][0]) == J_LO and mpf(CURVE[-1][0]) == J_HI, \
        "the curve does not run from one end of J to the other"
    spread = max(vals) / min(vals)
    assert spread > 2, f"psi' varies by only a factor {spread}: the curve is flat"
    print(f"  psi' ranges over [{mpmath.nstr(min(vals), 5)}, "
          f"{mpmath.nstr(max(vals), 5)}] on J, a factor of "
          f"{mpmath.nstr(spread, 4)}, so the curve carries information")
    print(f"C6  all {len(CURVE)} curve points are psi'(theta) from W alone on "
          f"the uniform grid of J, worst {mpmath.nstr(worst_x, 4)} (theta) and "
          f"{mpmath.nstr(worst, 4)} (psi') of its printed half-ulp ... OK")


# --------------------------------------------------------------------- C7
def check_C7():
    """The markers tighten onto the curve at O(M^-1), and are not fitted to it."""
    dev, fits = {}, {}
    for M in MS:
        pts = [(CFG.psi_and_deriv(th)[1], rescaled(M, th, nxt))
               for th, nxt in GAPS[M]]
        dev[M] = max(abs(s - d) for d, s in pts)
        n = len(pts)
        mx = sum(d for d, _ in pts) / n
        my = sum(s for _, s in pts) / n
        num = sum((d - mx) * (s - my) for d, s in pts)
        den = sum((d - mx) ** 2 for d, _ in pts)
        a = num / den
        fits[M] = (a, my - a * mx)
        print(f"  M={M}: max |S - psi'| = {mpmath.nstr(dev[M], 4)}, "
              f"least-squares psi' -> S is S = {mpmath.nstr(a, 6)} psi' "
              f"{'+' if fits[M][1] >= 0 else '-'} "
              f"{mpmath.nstr(abs(fits[M][1]), 4)}")
    assert all(dev[MS[i]] > dev[MS[i + 1]] for i in range(len(MS) - 1)), \
        f"the deviation does not decrease monotonically in M: {dev}"
    prod = [M * dev[M] for M in MS]
    assert max(prod) / min(prod) < 2, f"M x deviation is not bounded: {prod}"
    # not fitted: a fitted curve would sit at slope 1 and intercept 0 for every
    # M; psi' is computed from W, so the affine map REACHES the identity only as
    # M grows, and both of its coefficients must move monotonically toward it.
    slope_err = [abs(fits[M][0] - 1) for M in MS]
    off_err = [abs(fits[M][1]) for M in MS]
    assert all(slope_err[i] > slope_err[i + 1] for i in range(len(MS) - 1)), \
        f"the fitted slope does not approach 1 monotonically: {slope_err}"
    assert all(off_err[i] > off_err[i + 1] for i in range(len(MS) - 1)), \
        f"the fitted intercept does not approach 0 monotonically: {off_err}"
    assert slope_err[-1] < mpf('0.05') and off_err[-1] < mpf('0.02'), \
        (slope_err[-1], off_err[-1])
    print(f"C7  deviation falls monotonically with M x deviation in "
          f"[{mpmath.nstr(min(prod), 4)}, {mpmath.nstr(max(prod), 4)}] -- the "
          f"O(M^-{RATE}) of `prop:local-strong-clock` -- and the affine map from "
          "psi' to the markers tends to the identity, so nothing is fitted ... OK")


# --------------------------------------------------------------------- C8
def check_C8():
    """"the correction is under 4% of the clock pi/(M+1) itself"."""
    frac = max(abs(rescaled(M, th, nxt)) / (M + 1)
               for M in MS for th, nxt in GAPS[M])
    assert 100 * frac <= PCT, (mpmath.nstr(100 * frac, 6), PCT)
    assert 100 * frac > PCT - 1, (
        f"{PCT}% is loose: the true worst is {mpmath.nstr(100 * frac, 6)}%")
    print(f"C8  worst correction is {mpmath.nstr(100 * frac, 5)}% of pi/(M+1), "
          f"so the caption's {PCT}% bounds it and is the least integer that "
          "does ... OK")


# --------------------------------------------------------------------- C9
def check_C9():
    """The axis window holds the data and J; the ticks lie inside it."""
    assert "clip=true" in AXIS, (
        "the axis no longer clips, so a coordinate outside the window would "
        "still print and this check would be about nothing")
    xlo, xhi = (mpf(option(AXIS, k)) for k in ("xmin", "xmax"))
    ylo, yhi = (mpf(option(AXIS, k)) for k in ("ymin", "ymax"))
    assert xlo < J_LO and J_HI < xhi, (xlo, xhi)
    for leg, pts in BLOCKS:
        for x, y in pts:
            assert xlo <= mpf(x) <= xhi, (leg, x)
            assert ylo <= mpf(y) <= yhi, (leg, y)
    for name, lo, hi in (("xtick", xlo, xhi), ("ytick", ylo, yhi)):
        vals = [mpf(v) for v in tick_list(AXIS, name)]
        assert all(lo <= v <= hi for v in vals), (name, vals)
        assert all(vals[i] < vals[i + 1] for i in range(len(vals) - 1)), vals
        print(f"  {name} = {[mpmath.nstr(v, 4) for v in vals]} inside "
              f"[{mpmath.nstr(lo, 4)}, {mpmath.nstr(hi, 4)}]")
    n = sum(len(pts) for _, pts in BLOCKS)
    print(f"C9  all {n} plotted coordinates and all of J lie inside the "
          "clipped window ... OK")


if __name__ == "__main__":
    check_C0()
    check_C1()
    check_C2()
    check_C3()
    check_C4_C5()
    check_C6()
    check_C7()
    check_C8()
    check_C9()
    print("\nALL PASS: consistency_clock_figure_claims")
