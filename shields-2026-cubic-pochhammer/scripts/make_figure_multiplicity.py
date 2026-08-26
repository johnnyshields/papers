#!/usr/bin/env python3
r"""Paper section `sec:threshold` (The sharp multiplicity threshold), `prop:multiplicity-threshold`:
the figure `fig:multiplicity-threshold`.

Verifies every claim the figure and its caption make about the degree-three
constant-weight kernels, and emits the pgfplots coordinate block the figure
inlines:

  * G^{(r)}_3 re-derived from the constant-weight kernel of section `subsec:constant-weight-kernel` at m = 3,
    against the closed form C(3r-2,r-1) [p(1-p)]^r (p^r + (1-p)^r);
  * the q-form Ghat^{(r)}_3, by substituting q = p(1-p) into the power sum, and
    the central value Ghat^{(r)}_3(1/4) = C(3r-2,r-1) 2^{1-3r} that normalizes
    the plot;
  * that the normalization turns `eq:r-central-slope` into the endpoint slope
    2r(3-r) exactly -- the binomial and the power of two cancel;
  * that the normalized kernel is 2^{3r-1} q^r (p^r + (1-p)^r), so the four
    plotted curves carry the integer prefactors 32, 256, 2048, 16384;
  * r = 2 and r = 3: no interior maximum, the derivative being positive
    throughout (0,1/4), so the central endpoint is the maximum;
  * r = 4 and r = 5: the interior maxima 5/6 - sqrt(13)/6 and 3/7 - sqrt(2)/7
    in closed form, and the overshoots the caption prints to two decimals;
  * the r = 3 tangency: 1/4 - q = (p-1/2)^2, the expansion
    1 - 96y^2 + 512y^3 - 768y^4 in y = 1/4 - q, hence
    1 - 96x^4 + 512x^6 - 768x^8 in x = p - 1/2, cross-checked against the
    quartically flat expansion of `prop:multiplicity-threshold`;
  * the figure's own marker literals, to the digits it prints;
  * every one of the 484 inlined curve coordinates, character for character:
    the four `\addplot` lines the manuscript carries are parsed back out and
    compared against the strings `emit()` builds, so `emit()` formats both sides
    and a hand edit to either cannot survive;
  * that no plotted sample falls outside the axis limits the figure declares,
    read out of its own `axis[...]` options rather than written down here.

Symbolic work is SymPy over the rationals; sampling is mpmath at arbitrary
precision (no floating-point arithmetic in the loops).  Run with no arguments
to check only; run with --emit to also print the coordinate blocks to stdout.
"""

import os
import re
import sys

import sympy as sp
from mpmath import mp

mp.dps = 40

PAPER = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir,
                     'shields-2026-cubic-pochhammer.tex')

R_PLOT = (2, 3, 4, 5)
QMAX = sp.Rational(1, 4)
SAMPLES = 120

# cool for the multiplicities where coefficientwise log-concavity is universal,
# warm for those where it fails; r = 3 carries the heaviest stroke as the
# critical case.  These are the option strings the figure's four data curves
# carry, and they are what identifies a curve in the manuscript.
STYLES = {2: 'blue!65!black, line width=0.9pt',
          3: 'black, line width=1.4pt',
          4: 'red!45!black, dashed, line width=1.0pt',
          5: 'red!75!black, dotted, line width=1.3pt'}

p, q, x, y = sp.symbols('p q x y')


def power_sum_in_q(r):
    """p^r + (1-p)^r written in q = p(1-p), by the Newton recursion."""
    pw = [sp.Integer(2), sp.Integer(1)]
    for k in range(2, r + 1):
        pw.append(sp.expand(pw[k - 1] - q * pw[k - 2]))
    return pw[r]


def kernel_p(r):
    """G^{(r)}_3(p), summed from the constant-weight kernel definition at m = 3."""
    return sum(sp.binomial(3 * r - 2, r * k - 1) * p**(r * k) * (1 - p)**(r * (3 - k))
               for k in (1, 2))


def kernel_q(r):
    """Ghat^{(r)}_3(q)."""
    return sp.binomial(3 * r - 2, r - 1) * q**r * power_sum_in_q(r)


def normalized(r):
    """Ghat^{(r)}_3(q) / Ghat^{(r)}_3(1/4), which is 1 at the central endpoint."""
    G = kernel_q(r)
    return sp.expand(G / G.subs(q, QMAX))


def round_exact(value, places):
    """value rounded to `places` decimals, as an exact Rational.

    `value` is an exact algebraic expression, so the rounding is done with
    sympy's floor on `value*10^places + 1/2` rather than through a float; a
    float64 round would be the one place in this file where the printed digits
    were decided by binary arithmetic.
    """
    scale = sp.Integer(10) ** places
    return sp.Rational(sp.floor(sp.nsimplify(value) * scale + sp.Rational(1, 2)), scale)


def check_closed_forms():
    for r in range(2, 13):
        direct = sp.expand(kernel_p(r))
        closed = sp.expand(sp.binomial(3 * r - 2, r - 1) * (p * (1 - p))**r
                           * (p**r + (1 - p)**r))
        assert sp.expand(direct - closed) == 0, r
        # the q-form reproduces the p-form
        assert sp.simplify(kernel_q(r).subs(q, p * (1 - p)) - closed) == 0, r
        # central value
        central = kernel_q(r).subs(q, QMAX)
        assert sp.simplify(central - sp.binomial(3 * r - 2, r - 1)
                           * sp.Integer(2)**(1 - 3 * r)) == 0, r
    print("PASS  G^(r)_3 summed from the m=3 constant-weight kernel equals "
          "C(3r-2,r-1)[p(1-p)]^r(p^r+(1-p)^r), its q-form agrees, and "
          "Ghat^(r)_3(1/4) = C(3r-2,r-1) 2^{1-3r}, r = 2..12")


def check_normalized_slope():
    for r in range(2, 13):
        N = normalized(r)
        assert sp.simplify(N.subs(q, QMAX) - 1) == 0, r
        slope = sp.simplify(sp.diff(N, q).subs(q, QMAX))
        assert sp.simplify(slope - 2 * r * (3 - r)) == 0, (r, slope)
        # consistency with `eq:r-central-slope` divided by the central value
        paper = sp.binomial(3 * r - 2, r - 1) * r * (3 - r) * sp.Integer(2)**(2 - 3 * r)
        assert sp.simplify(paper / kernel_q(r).subs(q, QMAX) - slope) == 0, r
        # the prefactor of the normalized kernel
        pref = sp.simplify(N / (q**r * power_sum_in_q(r)))
        assert sp.simplify(pref - sp.Integer(2)**(3 * r - 1)) == 0, (r, pref)
    print("PASS  the normalization turns `eq:r-central-slope` into the endpoint "
          "slope 2r(3-r) exactly (4, 0, -8, -20 at r = 2,3,4,5), with "
          "prefactor 2^{3r-1} = 32, 256, 2048, 16384, r = 2..12")


def interior_maximum(r):
    """The interior maximizer of the normalized kernel on (0,1/4), or None."""
    N = normalized(r)
    crit = [c for c in sp.solve(sp.diff(N, q), q)
            if c.is_real and 0 < c < QMAX]
    if not crit:
        return None
    return max(crit, key=lambda c: sp.N(N.subs(q, c)))


def check_shapes():
    # r = 2, 3: the endpoint is the maximum, the derivative positive throughout
    for r in (2, 3):
        assert interior_maximum(r) is None, r
        d = sp.factor(sp.diff(normalized(r), q))
        assert all(sp.N(d.subs(q, QMAX * sp.Rational(j, 100))) > 0
                   for j in range(1, 100)), r
    print("PASS  r = 2 and r = 3 have no interior maximum and a positive "
          "derivative throughout (0,1/4): the central endpoint is the maximum")

    expect = {4: sp.Rational(5, 6) - sp.sqrt(13) / 6,
              5: sp.Rational(3, 7) - sp.sqrt(2) / 7}
    # the two percentages are READ OUT of the caption, not written down here:
    # a literal in this file would let the caption drift while the check passed
    caption = re.search(r'exceed the central values by(.*?)\.\}', figure_block(), re.S)
    assert caption, 'the caption no longer states the two overshoots'
    pct = re.findall(r'\\\(([0-9.]+)\\%\\\)', caption.group(1))
    assert len(pct) == 2, (pct, caption.group(1))
    printed = {4: pct[0], 5: pct[1]}
    for r in (4, 5):
        c = interior_maximum(r)
        assert c is not None and sp.simplify(c - expect[r]) == 0, (r, c)
        over = sp.nsimplify(normalized(r).subs(q, c)) - 1
        assert sp.N(over, 20) > 0, r
        # the caption's two-decimal percentage, as a ROUNDING rather than as a
        # prefix of the printed digits -- a prefix test accepts 6.594 printed
        # as 6.59 and also accepts 6.596, only one of which is correct
        places = len(printed[r].split('.')[1])
        assert round_exact(over * 100, places) == sp.Rational(printed[r]), \
            (r, sp.N(over * 100, 12), printed[r])
        print(f"PASS  r = {r}: interior maximum at q* = {sp.nsimplify(c)} "
              f"= {mp.nstr(mp.mpf(str(sp.N(c, 30))), 9)}, overshoot "
              f"{mp.nstr(mp.mpf(str(sp.N(over * 100, 30))), 8)}% -- the caption "
              f"prints {printed[r]}%")


def check_tangency():
    assert sp.expand(QMAX - p * (1 - p) - (p - sp.Rational(1, 2))**2) == 0
    N3 = normalized(3)
    in_y = sp.expand(N3.subs(q, QMAX - y))
    assert sp.expand(in_y - (1 - 96 * y**2 + 512 * y**3 - 768 * y**4)) == 0, in_y
    in_x = sp.expand(in_y.subs(y, x**2))
    assert sp.expand(in_x - (1 - 96 * x**4 + 512 * x**6 - 768 * x**8)) == 0, in_x
    # cross-check against the expansion `prop:multiplicity-threshold` states
    paper = sp.Rational(21, 256) - sp.Rational(63, 8) * x**4 + 42 * x**6 - 63 * x**8
    assert sp.simplify(in_x - paper / sp.Rational(21, 256)) == 0
    print("PASS  1/4 - q = (p-1/2)^2, so the normalized r = 3 kernel is "
          "1 - 96y^2 + 512y^3 - 768y^4 in y = 1/4 - q and "
          "1 - 96x^4 + 512x^6 - 768x^8 in x = p - 1/2, matching the "
          "quartically flat expansion of `prop:multiplicity-threshold`")


def samples(r):
    """Plotted samples, mpmath at arbitrary precision."""
    N = sp.lambdify(q, normalized(r), 'mpmath')
    out = []
    for j in range(SAMPLES + 1):
        qq = mp.mpf(j) / (4 * SAMPLES)
        out.append((qq, N(qq)))
    return out


def figure_block():
    """The one figure environment carrying `fig:multiplicity-threshold`."""
    chunks = open(PAPER, encoding='utf-8').read().split(r'\begin{figure}')
    fig = [c for c in chunks if r'\label{fig:multiplicity-threshold}' in c]
    assert len(fig) == 1, '`fig:multiplicity-threshold` is not in exactly one figure'
    return fig[0]


def axis_limits():
    """(ymin, ymax) as exact rationals, read off the figure's own axis options."""
    opts = re.search(r'\\begin\{axis\}\[(.*?)\n\]', figure_block(), re.S)
    assert opts, 'no axis options found'
    got = {}
    for key in ('ymin', 'ymax'):
        m = re.search(key + r'=([0-9.]+)', opts.group(1))
        assert m, key
        got[key] = sp.Rational(m.group(1))
    assert got['ymin'] < got['ymax'], got
    return got['ymin'], got['ymax']


def check_no_clipping():
    ymin, ymax = axis_limits()
    lo, hi = mp.mpf(str(ymin)), mp.mpf(str(ymax))
    worst = mp.mpf(0)
    for r in R_PLOT:
        for qq, hh in samples(r):
            assert lo <= hh <= hi, (r, mp.nstr(qq, 8), mp.nstr(hh, 8))
            worst = max(worst, hh)
    # the ceiling is not slack by an order of magnitude either, or the check
    # would pass whatever the curves did
    assert worst > mp.mpf(str(ymax)) * mp.mpf(9) / 10, mp.nstr(worst, 8)
    print(f"PASS  no plotted sample is clipped: every value lies in "
          f"[{float(ymin):g}, {float(ymax):g}] as the figure's own axis options "
          f"declare, the largest being {mp.nstr(worst, 8)}")


def addplot_lines():
    """The four data curves, exactly as the manuscript inlines them."""
    out = {}
    for r in R_PLOT:
        coords = ' '.join(f'({mp.nstr(qq, 8, strip_zeros=False)},'
                          f'{mp.nstr(hh, 8, strip_zeros=False)})'
                          for qq, hh in samples(r))
        out[r] = f'\\addplot[{STYLES[r]}] coordinates {{{coords}}};'
    return out


def check_inlined_coordinates():
    """Every inlined curve coordinate, against the block emit() builds.

    The four `\addplot` lines carry 484 of the figure's 486 coordinates; the
    other two are the markers checked above.  Nothing in a LaTeX build compares
    them with the mathematics, so they are parsed back out of the manuscript and
    required to match the strings `emit()` produces, character for character --
    which makes `emit()` the single formatter for both sides.
    """
    fig = figure_block()
    found = {}
    for opts, coords in re.findall(r'\\addplot\[([^\]]*)\]\s*coordinates \{([^}]*)\}',
                                   fig, re.S):
        found.setdefault(opts.strip(), []).append(coords)
    built = addplot_lines()
    total = 0
    for r in R_PLOT:
        got = found.get(STYLES[r])
        assert got and len(got) == 1, (r, STYLES[r], list(found))
        want = built[r][built[r].index('{') + 1:built[r].rindex('}')]
        assert got[0] == want, (r, len(got[0]), len(want),
                                got[0][:80], want[:80])
        total += len(re.findall(r'\(', got[0]))
    assert total == 4 * (SAMPLES + 1), total
    print(f"PASS  all {total} inlined curve coordinates in the manuscript are "
          f"exactly the ones emit() builds, on all four \\addplot lines")


def check_marker_literals():
    """The coordinates the figure prints for the two interior maxima."""
    lit = {4: ('0.2324081', '1.0659009'), 5: ('0.2265409', '1.2112178')}
    for r in (4, 5):
        c = interior_maximum(r)
        h = normalized(r).subs(q, c)
        for got, want in ((c, lit[r][0]), (h, lit[r][1])):
            places = len(want.split('.')[1])
            assert round_exact(got, places) == sp.Rational(want), \
                (r, sp.N(got, 12), want)
    print("PASS  the marker literals (0.2324081, 1.0659009) and "
          "(0.2265409, 1.2112178) are the interior maxima, correctly rounded")

    # and the manuscript marks exactly those two points -- the curves it inlines
    # are compared separately, in check_inlined_coordinates
    fig = [figure_block()]
    drawn = set()
    for coords in re.findall(r'mark=\*.*?coordinates \{([^}]*)\}', fig[0], re.S):
        drawn |= set(re.findall(r'\(([^,]+),([^)]+)\)', coords))
    assert drawn == {lit[4], lit[5]}, sorted(drawn)
    print(f"PASS  the figure in {os.path.basename(PAPER)} marks exactly those two "
          f"points and no others")


def emit():
    print('\n% ---- coordinate blocks for `fig:multiplicity-threshold` ----')
    for r, line in addplot_lines().items():
        print(line)


def main():
    check_closed_forms()
    check_normalized_slope()
    check_shapes()
    check_tangency()
    check_no_clipping()
    check_marker_literals()
    check_inlined_coordinates()
    print('ALL PASS')
    if '--emit' in sys.argv:
        emit()


if __name__ == '__main__':
    main()
