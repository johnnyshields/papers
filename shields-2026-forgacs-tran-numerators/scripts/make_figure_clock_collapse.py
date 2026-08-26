#!/usr/bin/env python3
r"""Paper section `sec:consequences` (Global and local zero laws), section `subsec:strong-clock`
`subsec:strong-clock`, `fig:clock-collapse`.

Generates `figure_clock_collapse.tex`, the pgfplots block inlined as `fig:clock-collapse`,
and asserts every claim its caption makes.

The figure shows the content of `prop:local-strong-clock` that the theorem
statement alone does not make visible.  Raw spacings would be uninformative:
they differ from the universal clock pi/(M+1) by only a few percent at these
indices.  After the rescaling

    S_{k,M} = (M+1)^2/pi * ( theta_{k+1,M} - theta_{k,M} - pi/(M+1) )

the leading term is gone and what remains converges to psi'(theta), the
derivative of the phase of the principal residue amplitude.  Three indices
collapse onto one curve that was computed from W alone -- there is no fitted
parameter anywhere in the picture, which is the point of the figure and is
asserted below.

Denominator is `fig:decomposition-and-defect`'s, so the two figures share their geometry; only the
canonical weight differs.  It has to: on `fig:decomposition-and-defect`'s own weight 7t^2+8, psi'
varies by about 7% over the arc and the curve is visually flat.  With B = 1+t
it varies by a factor of three.

The zero-finding and amplitude routines are imported from
`check_local_clock.py`, the script that verifies the proposition, so the figure
cannot drift from the statement it illustrates.
"""

from mpmath import mp, mpf
import mpmath

import check_local_clock as clk

mp.dps = 40

# ---------------------------------------------------------------- configuration

QC = [mpf(1), mpf(-7) / 4, mpf(7) / 8, mpf(-1) / 8]   # (1-t)(1-t/2)(1-t/4)
R_EXP = 1
BC = [mpf(1), mpf(1)]                                  # B(t) = 1 + t
J_LO, J_HI = mpf('0.40'), mpf('2.40')                  # the plotted compact subarc
MS = (16, 28, 44)
PAD = mpf('0.30')          # J_0 slack, so zeros just outside J are still found

cfg = clk.Config('fig2', QC, R_EXP, BC, (J_LO - PAD, J_HI + PAD), mpf('1.05'))


def rescaled(M, th, nxt):
    return (M + 1) ** 2 / mpmath.pi * ((nxt - th) - mpmath.pi / (M + 1))


# ---------------------------------------------------------------- the data

series, worst = {}, {}
for M in MS:
    zs = clk.zeros_of_G(cfg, M)
    pts = []
    for i in range(len(zs) - 1):
        th, nxt = zs[i], zs[i + 1]
        if th < J_LO or nxt > J_HI:      # both endpoints of the gap must lie in J
            continue
        pts.append((th, rescaled(M, th, nxt), cfg.psi_and_deriv(th)[1]))
    assert pts, f'M={M} contributed no plotted gap'
    series[M] = pts
    worst[M] = max(abs(s - d) for _, s, d in pts)

NCURVE = 241
curve = []
for i in range(NCURVE):
    th = J_LO + (J_HI - J_LO) * mpf(i) / (NCURVE - 1)
    curve.append((th, cfg.psi_and_deriv(th)[1]))

# ---------------------------------------------------------------- caption claims

print('`fig:clock-collapse` caption claims')

# (F1) J is a compact subarc of (0, pi/r), strictly inside it.
assert 0 < J_LO < J_HI < mpmath.pi / R_EXP
print(f'  (F1) J = [{J_LO}, {J_HI}] is compact in (0, pi/r) = (0, '
      f'{mpmath.nstr(mpmath.pi / R_EXP, 6)}), clear of both endpoints by '
      f'{mpmath.nstr(min(J_LO, mpmath.pi / R_EXP - J_HI), 3)}')

# (F2) W does not vanish on J -- the proposition's hypothesis, checked not assumed.
wmin = min(abs(cfg.zW(J_LO + (J_HI - J_LO) * mpf(i) / 200)[2]) for i in range(201))
assert wmin > mpf('1e-3'), 'W comes too close to zero on the plotted arc'
print(f'  (F2) min |W| on J is {mpmath.nstr(wmin, 5)} > 0, so '
      f'prop:local-strong-clock applies on the whole plotted arc')

# (F3) the principal branch is the minimum-modulus pair across J.
nroots = clk.assert_principal_branch(cfg)
print(f'  (F3) principal branch verified at 9 sample angles; D has {nroots} roots, '
      f'so a nonprincipal root is present and R_M is a genuine remainder')

# (F4) psi' actually varies -- otherwise the curve carries no information.
cvals = [c for _, c in curve]
spread = max(cvals) / min(cvals)
assert spread > 2, f'psi\' varies by only a factor {spread}; the curve would look flat'
print(f'  (F4) psi\' ranges over [{mpmath.nstr(min(cvals), 4)}, '
      f'{mpmath.nstr(max(cvals), 4)}] on J, a factor of {mpmath.nstr(spread, 3)}')

# (F5) the curve is not fitted: it is psi', computed from W, and the markers are
# zero spacings.  Nothing is tuned -- so the agreement is a claim, and it holds.
for M in MS:
    assert worst[M] < mpf('0.05'), f'M={M} deviates from psi\' by {worst[M]}'
print('  (F5) markers agree with the independently computed curve: max deviation '
      + ', '.join(f'{mpmath.nstr(worst[M], 3)} (M={M})' for M in MS))

# (F6) the collapse tightens with M at the theorem's O(M^-1), so the caption may
# say the markers converge.  Monotone decrease AND a bounded M x deviation.
assert worst[MS[0]] > worst[MS[1]] > worst[MS[2]], \
    'the deviation does not decrease monotonically in M'
prod = [M * worst[M] for M in MS]
assert max(prod) / min(prod) < 2, f'M x deviation is not bounded: {prod}'
print(f'  (F6) deviation decreases monotonically in M, with M x deviation in '
      f'[{mpmath.nstr(min(prod), 3)}, {mpmath.nstr(max(prod), 3)}] -- the O(M^-1) '
      f'of prop:local-strong-clock, not a faster or slower rate')

# (F7) the rescaling is what makes the effect visible: before it, the correction
# is a few percent of the leading clock and the plot would be a flat line.
frac = max((abs(s) / (M + 1)) for M in MS for _, s, _ in series[M])
print(f'  (F7) before rescaling the correction is at most '
      f'{mpmath.nstr(100 * frac, 3)}% of the leading clock, which is why the '
      f'figure plots the rescaled quantity')

# ---------------------------------------------------------------- emit

def fmt(x, y, digits=6):
    return f'({mp.nstr(x, digits, strip_zeros=False)},{mp.nstr(y, digits, strip_zeros=False)})'


def wrap(pairs, per_line=6, indent='  '):
    out, cur = [], []
    for p in pairs:
        cur.append(p)
        if len(cur) == per_line:
            out.append(indent + ' '.join(cur))
            cur = []
    if cur:
        out.append(indent + ' '.join(cur))
    return '\n'.join(out)


ylo = mp.floor(min(min(cvals), min(s for M in MS for _, s, _ in series[M])) * 10) / 10 - mpf('0.05')
yhi = mp.ceil(max(max(cvals), max(s for M in MS for _, s, _ in series[M])) * 10) / 10 + mpf('0.05')

# shape AND color per series: the shapes are what keep the panel readable in
# grayscale, the colors are what make it readable at a glance in print
# The square is solid mkgreen, fill and outline the same -- chosen deliberately.
# Measured tradeoff: against the solid mkblue triangle that is 59.5% ink against
# 73.8%, and at the ~1.2mm the marks print, a monochrome copy separates them by
# shape rather than by tone.  A lightened fill was tried and widens the gap to
# 42% against 74%; it was reverted on purpose, so do not re-apply it as a
# grayscale fix.  A green cross was tried too, and withdrawn.  If a monochrome
# proof ever reads muddy the intended lever is `square*` -> `square`, which
# separates by fill state instead.
MARKS = {MS[0]: ('o', '2.0pt', 'mkred', 'line width=0.9pt'),
         MS[1]: ('square*', '1.8pt', 'mkgreen', 'line width=0.5pt'),
         MS[2]: ('triangle*', '2.4pt', 'mkblue', 'line width=0.5pt')}

# Draw order is back to front: the psi' curve first, then M = 44, 28, 16, so
# the open red circles are never covered by a filled mark.  `reverse legend`
# then puts the legend back into ascending M with the curve last.
blocks = []
for M in reversed(MS):
    mk, size, col, opts = MARKS[M]
    blocks.append(
        f'\\addplot[{col}, only marks, mark={mk}, mark size={size}, '
        f'{opts}] coordinates {{\n'
        + wrap([fmt(th, s) for th, s, _ in series[M]]) + '\n};\n'
        + f'\\addlegendentry{{\\(M={M}\\)}}')

TEMPLATE = r"""% Generated by scripts/make_figure_clock_collapse.py -- do not edit by hand.
\begin{figure}[!tp]
\centering
\begin{tikzpicture}
\begin{axis}[
    width=12.7cm, height=5.4cm,
    xlabel={\(\theta\)}, ylabel={\(\mathcal S_{k,M}\)},
    xmin=@@XLO@@, xmax=@@XHI@@, ymin=@@YLO@@, ymax=@@YHI@@,
    xtick={0.5,1.0,1.5,2.0},
    ytick={0.3,0.5,0.7},
    tick label style={font=\footnotesize}, label style={font=\small},
    legend style={at={(0.985,0.96)}, anchor=north east, draw=black!40,
                  font=\footnotesize, row sep=-1pt, inner sep=2pt},
    legend cell align=left, reverse legend,
    axis lines=left, axis on top, clip=true,
]
\addplot[black!85, line width=0.8pt] coordinates {
@@CURVE@@
};
\addlegendentry{\(\psi'(\theta)\)}
@@SERIES@@
\end{axis}
\end{tikzpicture}
\caption{Local strong-clock collapse, for the denominator of
\Cref{fig:decomposition-and-defect} and the weight \(B(t)=1+t\).  Markers show
\(\mathcal S_{k,M}=(M+1)^2\bigl(\theta_{k+1,M}-\theta_{k,M}-\pi/(M+1)\bigr)/\pi\)
at three indices, over the consecutive bulk zero angles with
\(\theta_{k,M}\) and \(\theta_{k+1,M}\) both in the compact subarc
\(\mathcal J=[@@JLO@@,@@JHI@@]\), on which the principal residue amplitude does
not vanish.  The solid curve is \(\psi'\), computed from that amplitude alone
and not fitted to the spacings.  \Cref{prop:local-strong-clock} gives
\(\mathcal S_{k,M}=\psi'(\theta_{k,M})+O(M^{-1})\), and the markers tighten onto
the curve as \(M\) grows.  Before this rescaling the correction is under
@@FRAC@@\% of the clock \(\pi/(M+1)\) itself.}
\label{fig:clock-collapse}
\end{figure}
"""

out = TEMPLATE
for tok, val in {
    '@@XLO@@': mp.nstr(J_LO - mpf('0.06'), 4, strip_zeros=False),
    '@@XHI@@': mp.nstr(J_HI + mpf('0.06'), 4, strip_zeros=False),
    '@@YLO@@': mp.nstr(ylo, 4, strip_zeros=False),
    '@@YHI@@': mp.nstr(yhi, 4, strip_zeros=False),
    '@@JLO@@': mp.nstr(J_LO, 3, strip_zeros=False),
    '@@JHI@@': mp.nstr(J_HI, 3, strip_zeros=False),
    '@@FRAC@@': str(int(mp.ceil(100 * frac))),
    '@@CURVE@@': wrap([fmt(th, c) for th, c in curve]),
    '@@SERIES@@': '\n'.join(blocks),
}.items():
    out = out.replace(tok, val)

OUT = 'figure_clock_collapse.tex'
with open(OUT, 'w') as f:
    f.write(out)
print(f'\nwrote {OUT}  ({sum(len(series[M]) for M in MS)} markers over three indices, '
      f'{NCURVE} curve points)')
print('ALL PASS: make_figure_clock_collapse')
