#!/usr/bin/env python3
r"""Paper section 3 (Pole geometry and the weighted principal amplitude), Figure 1.

Generates the two-panel figure inlined as Figure 1 (fig:decomposition-and-defect).
The figure sits in section 3, but its caption also draws on Lemma 2.2 (the index
shift), eq. (3.7)/(3.8), eq. (3.11), Theorem 4.1 with eqs. (4.1)-(4.3),
Proposition 5.1 and Proposition 6.3.

Emits the pgfplots coordinate blocks for the figure and asserts every claim its
caption makes.  Symbolic work uses SymPy over the rationals; numerical work uses
mpmath at arbitrary precision (no floating-point arithmetic in the loops).

Both panels use the same denominator

    Q(t) = (1-t)(1-t/2)(1-t/4),   r = 1,   d = max{deg Q, r} = 3,

so I_{Q,r} = (a,b) is bounded (b = g(t_b) is finite precisely when r = 1) and
the smallest zero of Q is simple, giving a > 0.

Panel A -- the weighted principal decomposition (3.8) for the proper numerator
N(t,z) = B(t) = 7t^2 + 8, at m = M = 14:

  * Lemma 2.2 with E = deg_z N = 0 gives A = B and mu = 0, so P_m = F_m and the
    index shift is trivial; asserted, not assumed.
  * The arc point at theta = pi/2 is t_+ = i sqrt(8/7) with z = 45/28 exactly,
    so B(t_+(pi/2)) = 0 and W of (3.7) has an amplitude zero at theta_1 = pi/2
    of multiplicity nu_1 = 1 (Lemma 3.6).  Both values asserted in closed form.
  * eq. (3.8): tau^{M+1} F_M(z(theta)) = 2 Re(W e^{-i(M+1)theta}) + R_M.
  * Theorem 4.1, eq. (4.2): |R_M| <= |W|/2 on the plotted range.  The window
    around theta_1 where dominance FAILS is measured on both sides by bisection
    and asserted below 1e-11 -- the caption's "too narrow to draw".  This is not
    Theta_{1,M} of eq. (4.1), whose width turns on the unpinned constant c; the
    caption must not attribute the measured number to (4.1).
  * Proposition 5.1: the sign changes of the plotted curve are counted and
    matched against the real zeros of F_M in z([theta_L, theta_R]).

Panel B -- zeros of P_m in the z-plane for the genuinely bivariate numerator
N(t,z) = (1+z+z^2) + t(2-z), at m = 14 and m = 38:

  * The index shift of Lemma 2.2 is r E - mu = 2, so deg P_m = m + 2, with
    exactly m simple zeros in I_{Q,r} and exactly 2 elsewhere: the bulk grows
    while the defect does not (Theorem 1.1).  The degree is predicted from the
    reduction rather than read off the computed polynomial.
  * The exceptional pair is NOT fixed in m -- it converges geometrically.  The
    drift is measured, not assumed away: from m = 14 to m = 38 it is 1.9e-14, so
    the caption claims agreement to thirteen decimals and nothing stronger.
  * This numerator is irreducible, hence not a product R(z)S(t), so the pair is
    created by the initial data rather than factored out of it as in
    Proposition 6.3; asserted.

Panel A additionally verifies the caption's p = -1: B has no real zero and both
endpoint collisions are double, so eq. (3.11) gives p = nu - (k-1) = -1 and |W|
blows up at either endpoint.  Checked by delta * 2|W| approaching a positive
constant from both sides.
"""

import sympy as sp
from mpmath import mp

mp.dps = 40

t, z = sp.symbols('t z')

# ---------------------------------------------------------------------------
# denominator, shared by both panels
# ---------------------------------------------------------------------------
Q = sp.expand((1 - t) * (1 - t / 2) * (1 - t / 4))
r = 1
Qp = sp.Poly(Q, t)
n = Qp.degree()
d = max(n, r)
Qc = [sp.Rational(Qp.nth(k)) for k in range(n + 1)]
Qm = [mp.mpf(Qc[k].p) / Qc[k].q for k in range(n + 1)]

assert Q.subs(t, 0) > 0                                  # eq. (1.1): Q(0) > 0
assert all(rt > 0 for rt in sp.real_roots(Qp))           # eq. (1.1): positive zeros
assert len(sp.real_roots(Qp)) == n                       # eq. (1.1): all zeros real
assert max(n, r) > 1                                     # Theorem 1.1 hypothesis
print(f'Q = {Q}   r = {r}   d = {d}')


def critical_points():
    r"""Real zeros of r Q - t Q', the critical points of g = -Q/t^r."""
    poly = sp.Poly(sp.expand(r * Q - t * sp.diff(Q, t)), t)
    assert poly.degree() >= 1
    return sorted(sp.real_roots(poly))


g = -Q / t**r
crit = critical_points()
t_a = min(c for c in crit if c > 0)                      # smallest positive critical point
t_b = max(c for c in crit if c < 0)                      # the negative one (r = 1)
a = mp.mpf(str(sp.N(g.subs(t, t_a), 35)))
b = mp.mpf(str(sp.N(g.subs(t, t_b), 35)))
assert 0 < a < b < mp.inf                                # eq. (3.1), bounded since r = 1
print(f'I_(Q,r) = ({mp.nstr(a, 10)}, {mp.nstr(b, 10)})')


def arc_point(th):
    r"""(tau, z) with t_+ = tau e^{i th} a minimum-modulus zero of Q + z t^r.

    For r = 1 the reality of z = -Q(t_+)/t_+ is
        Im[Q(tau e^{i th}) e^{-i th}] = sum_k q_k tau^k sin((k-1) th) = 0,
    a polynomial in tau.  Each positive root is tested by recomputing every
    denominator zero and checking that tau is attained exactly twice and is
    strictly smallest -- Theorem 3.1's minimum-modulus assertion.
    """
    th = mp.mpf(th)
    co = [Qm[k] * mp.sin((k - 1) * th) for k in range(n + 1)]
    while co and co[-1] == 0:
        co.pop()
    for tau in sorted(mp.re(x) for x in mp.polyroots(list(reversed(co)),
                                                    maxsteps=400, extraprec=400)
                      if abs(mp.im(x)) < mp.mpf('1e-25') and mp.re(x) > 0):
        tp = tau * mp.exp(mp.mpc(0, th))
        zz = -sum(Qm[k] * tp**k for k in range(n + 1)) / tp**r
        if abs(mp.im(zz)) > mp.mpf('1e-20'):
            continue
        zz = mp.re(zz)
        dc = list(Qm)
        dc[r] += zz
        mods = sorted(abs(x) for x in mp.polyroots(list(reversed(dc)),
                                                   maxsteps=400, extraprec=400))
        if (abs(mods[0] - tau) < mp.mpf('1e-20') and abs(mods[1] - tau) < mp.mpf('1e-20')
                and (len(mods) == 2 or mods[2] > tau * (1 + mp.mpf('1e-10')))):
            return tau, zz
    raise RuntimeError(f'no valid arc point at theta = {mp.nstr(th, 12)}')


def W_of(th, Bc):
    r"""eq. (3.7): W = -B(t_+)/(Q'(t_+) + r z t_+^{r-1}).  Returns (W, tau, z)."""
    tau, zz = arc_point(th)
    tp = tau * mp.exp(mp.mpc(0, mp.mpf(th)))
    Bv = sum(Bc[k] * tp**k for k in range(len(Bc)))
    dQ = sum(k * Qm[k] * tp**(k - 1) for k in range(1, n + 1))
    return -Bv / (dQ + r * zz * tp**(r - 1)), tau, zz


def coeffs_P(N, mmax):
    r"""P_0..P_mmax of N/(Q + z t^r) by the exact recurrence of Proposition 2.1."""
    D = sp.Poly(sp.expand(Q + z * t**r), t)
    Nn = sp.Poly(sp.expand(N), t)
    d0 = D.nth(0)
    P = []
    for m in range(mmax + 1):
        acc = Nn.nth(m) - sum(D.nth(j) * P[m - j]
                              for j in range(1, min(m, D.degree()) + 1))
        P.append(sp.expand(sp.cancel(acc / d0)))
    return P


def reduce_numerator(N):
    r"""Lemma 2.2: A(t) = t^{rE} N(t, -Q/t^r) = t^mu B(t), B(0) != 0.  Returns (B, mu, E)."""
    E = sp.Poly(sp.expand(N), z).degree() if sp.expand(N).has(z) else 0
    A = sp.expand(sp.simplify(t**(r * E) * sp.expand(N).subs(z, -Q / t**r)))
    A = sp.expand(sp.cancel(A))
    assert sp.Poly(A, t).is_univariate and A != 0        # Lemma 2.2: A in R[t]\{0}
    mu = 0
    while sp.simplify(sp.Poly(A, t).nth(mu)) == 0:
        mu += 1
    B = sp.expand(sp.cancel(A / t**mu))
    assert sp.Poly(B, t).nth(0) != 0                     # B(0) != 0
    return B, mu, E


# ===========================================================================
# Panel A: the weighted principal decomposition, N = B = 7 t^2 + 8, M = 14
# ===========================================================================
print('\n--- Panel A ---')
NA = 7 * t**2 + 8
M = 14
assert sp.Poly(sp.expand(NA), t).degree() < d            # proper numerator

BA, muA, EA = reduce_numerator(NA)
assert EA == 0 and muA == 0 and sp.expand(BA - NA) == 0  # the reduction is trivial here
print(f'N = B = {NA}: E = {EA}, mu = {muA}, so P_m = F_m with no index shift')
BAc = [mp.mpf(sp.Rational(sp.Poly(BA, t).nth(k)).p) / sp.Rational(sp.Poly(BA, t).nth(k)).q
       for k in range(sp.Poly(BA, t).degree() + 1)]

# the amplitude zero sits at theta_1 = pi/2 in closed form
th1 = mp.pi / 2
tau1, z1 = arc_point(th1)
assert abs(tau1 - mp.sqrt(mp.mpf(8) / 7)) < mp.mpf('1e-30')      # tau(pi/2) = sqrt(8/7)
assert abs(z1 - mp.mpf(45) / 28) < mp.mpf('1e-30')               # z(pi/2)  = 45/28
assert sp.simplify(NA.subs(t, sp.I * sp.sqrt(sp.Rational(8, 7)))) == 0
assert a < mp.mpf(45) / 28 < b                                   # inside I
nu1 = 1
assert sp.simplify(sp.diff(NA, t).subs(t, sp.I * sp.sqrt(sp.Rational(8, 7)))) != 0
print(f'amplitude zero: theta_1 = pi/2, tau = sqrt(8/7) = {mp.nstr(tau1, 12)}, '
      f'z = 45/28 = {mp.nstr(z1, 12)}, nu_1 = {nu1}')

FA = coeffs_P(NA, M)
FMp = sp.Poly(FA[M], z)
assert FMp.degree() == M // r                            # Lemma 2.3, eq. (2.6)
FMc = [mp.mpf(sp.Rational(FMp.nth(k)).p) / sp.Rational(FMp.nth(k)).q
       for k in range(FMp.degree() + 1)]
print(f'deg F_{M} = {FMp.degree()} = floor(M/r)')


def curve(th):
    r"""(tau^{M+1} F_M(z(theta)), 2|W|, |R_M|/|W|) at theta."""
    Wv, tau, zz = W_of(th, BAc)
    val = tau**(M + 1) * sum(FMc[k] * zz**k for k in range(len(FMc)))
    RM = val - 2 * mp.re(Wv * mp.exp(mp.mpc(0, -(M + 1) * mp.mpf(th))))
    ratio = abs(RM) / abs(Wv) if abs(Wv) > 0 else mp.inf
    return val, 2 * abs(Wv), ratio


TH_L = mp.mpf('0.6')                                     # plotted range [TH_L, pi - TH_L]
TH_R = mp.pi - TH_L
NPTS = 301

grid = [TH_L + (TH_R - TH_L) * mp.mpf(i) / (NPTS - 1) for i in range(NPTS)]
vals, envs, ratios = [], [], []
for th in grid:
    v, e, q = curve(th)
    vals.append(v)
    envs.append(e)
    ratios.append(q)

# eq. (3.8) + Theorem 4.1: dominance on the plotted range, away from theta_1
far = [q for th, q in zip(grid, ratios) if abs(th - th1) > mp.mpf('0.02')]
assert max(far) <= mp.mpf('0.5'), f'dominance fails: max ratio {mp.nstr(max(far), 6)}'
print(f'max |R_M|/|W| on the plotted range (|theta-theta_1| > 0.02) = {mp.nstr(max(far), 6)}')

# the window around theta_1 where dominance fails: |R_M| > |W|/2, i.e. |W| < 2|R_M|
RM_scale = max(abs(v - 2 * mp.re(W_of(th, BAc)[0] * mp.exp(mp.mpc(0, -(M + 1) * th))))
               for th, v in zip(grid, vals))
# The caption states that eq. (4.2) fails only within 1e-11 of theta_1 at this M.
# That is a claim about the DOMINANCE-FAILURE set {|R_M| > |W|/2}, not about
# Theta_{1,M} of eq. (4.1), whose width depends on the unpinned constant c: the
# proof allows any c in (0,-log sigma), and at M = 14 even the largest admissible
# c leaves e^{-cM} well above 1e-11.  Measure the failure set on BOTH sides --
# a one-sided bisection would not certify the caption -- and check that the
# crossing of |R_M|/|W| = 1/2 is unique, which the bisection presumes.
half = {}
for side, sgn in (('left', -1), ('right', +1)):
    lo, hi = mp.mpf(0), mp.mpf('0.2')
    assert curve(th1 + sgn * hi)[2] <= mp.mpf('0.5'), 'bisection bracket too small'
    for _ in range(220):
        mid = (lo + hi) / 2
        if curve(th1 + sgn * mid)[2] > mp.mpf('0.5'):
            lo = mid
        else:
            hi = mid
    half[side] = hi
half_width = max(half.values())
assert half_width < mp.mpf('1e-11'), f'caption claim broken: {mp.nstr(half_width, 6)}'
outside = [th for th in grid
           if abs(th - th1) > 10 * half_width and curve(th)[2] > mp.mpf('0.5')]
assert not outside, f'dominance also fails away from theta_1: {len(outside)} points'
print(f'dominance \\eqref{{eq:dominance-bound}} fails only within '
      f'{mp.nstr(half_width, 6)} of theta_1 (left {mp.nstr(half["left"], 4)}, '
      f'right {mp.nstr(half["right"], 4)}; unique crossing; '
      f'|R_M| <= {mp.nstr(RM_scale, 4)})')

# Proposition 5.1: sign changes of the plotted curve vs real zeros of F_M in the window
sign_changes = sum(1 for i in range(len(vals) - 1)
                   if mp.sign(vals[i]) * mp.sign(vals[i + 1]) < 0)
zL, zR = arc_point(TH_L)[1], arc_point(TH_R)[1]
real_in_window = sum(1 for rt in sp.Poly(FA[M], z).real_roots()
                     if zL < mp.mpf(str(sp.N(rt, 35))) < zR)
assert sign_changes == real_in_window, (sign_changes, real_in_window)
total_in_I = sum(1 for rt in sp.Poly(FA[M], z).real_roots()
                 if a < mp.mpf(str(sp.N(rt, 35))) < b)
assert total_in_I == M // r                              # every zero already in I: C_B = 0
print(f'sign changes on the plotted range = {sign_changes} = real zeros of F_M there; '
      f'all {total_in_I} = floor(M/r) zeros lie in I (C_B = 0)')

ymax = max(envs)
print(f'envelope max on the plotted range = {mp.nstr(ymax, 6)} at theta = '
      f'{mp.nstr(grid[envs.index(ymax)], 6)}')

# Lemma 3.6, eq. (3.11): W = delta^p V(delta).  Here B has no real zero, so
# nu = 0 at both finite endpoints, where the principal pair collides to order
# k = max{rho,2} = 2 at the lower and k = 2 at the upper; hence p = -1 and |W|
# grows without bound at either endpoint.  The caption states p = -1, so verify
# it: delta * 2|W| must approach a positive constant from both sides.
assert sp.Poly(NA, t).count_roots() == 0                 # nu = 0: no real zero of B
rho = min(sp.Poly(Q, t).real_roots().count(rt) for rt in set(sp.Poly(Q, t).real_roots()))
rho_min = sp.Poly(Q, t).real_roots().count(min(sp.Poly(Q, t).real_roots()))
assert rho_min == 1, 'the smallest zero of Q must be simple for a > 0'
for side, at_delta in (('lower', lambda dd: dd), ('upper', lambda dd: mp.pi - dd)):
    qs, prev_env = [], None
    for dd in [mp.mpf('0.02') / 2**i for i in range(4)]:
        e = curve(at_delta(dd))[1]
        qs.append(dd * e)
        if prev_env is not None:
            assert e > prev_env, f'|W| not growing at the {side} endpoint'
        prev_env = e
    rel = [abs(qs[i + 1] / qs[i] - 1) for i in range(len(qs) - 1)]
    assert rel[-1] < mp.mpf('0.02') and rel[-1] < rel[0], (side, rel)
    print(f'{side} endpoint: delta*2|W| -> {mp.nstr(qs[-1], 8)} '
          f'(successive ratios off 1 by {[mp.nstr(x, 3) for x in rel]}), so p = -1')

# ===========================================================================
# Panel B: zeros of P_m in the z-plane, N = (1+z+z^2) + t(2-z)
# ===========================================================================
print('\n--- Panel B ---')
NB = sp.expand((1 + z + z**2) + t * (2 - z))
assert sp.Poly(NB, t).degree() < d                       # proper numerator
assert sp.expand(NB).has(t) and sp.expand(NB).has(z)     # genuinely bivariate
# irreducible over Q, so N is not a product R(z)S(t): the exceptional pair is
# created by the initial data, not factored out of it as in Proposition 6.3
assert len(sp.factor_list(NB)[1]) == 1 and sp.factor_list(NB)[1][0][1] == 1
print(f'N = {NB}   (irreducible, so not a product R(z)S(t))')

# Lemma 2.2: the index shift, so the degree is predicted rather than observed
BB, muB, EB = reduce_numerator(NB)
shift = r * EB - muB
print(f'reduction: E = {EB}, mu = {muB}, deg B = {sp.Poly(BB, t).degree()}, '
      f'so M = m + {shift} and deg P_m = floor((m+{shift})/r)')

MS = [14, 38]
PB = coeffs_P(NB, max(MS))
panelB = {}
exc_ref = None
for m in MS:
    poly = sp.Poly(PB[m], z)
    inI, exc = [], []
    for rt in poly.nroots(n=35, maxsteps=1500):
        re_, im_ = mp.mpf(str(sp.re(rt))), mp.mpf(str(sp.im(rt)))
        (inI if (abs(im_) < mp.mpf('1e-25') and a < re_ < b) else exc).append((re_, im_))
    assert poly.degree() == (m + shift) // r              # Lemma 2.3 + Remark 2.4
    assert len(inI) == poly.degree() - 2                  # the bulk grows with m
    assert len(exc) == 2                                  # the defect does not
    exc.sort(key=lambda p: p[1])
    # the pair is not literally fixed in m: it converges geometrically.  Measure
    # the drift rather than asserting identity, since the caption quotes it.
    if exc_ref is None:
        exc_ref, drift = exc, mp.mpf(0)
    else:
        drift = max(mp.sqrt((x1 - x2)**2 + (y1 - y2)**2)
                    for (x1, y1), (x2, y2) in zip(exc, exc_ref))
        # the caption claims agreement to thirteen decimals, i.e. drift < 5e-14;
        # assert exactly that, not a looser bound the caption does not rely on
        assert drift < mp.mpf('5e-14'), f'pair moves by {mp.nstr(drift, 6)}'
    assert abs(exc[0][0] - exc[1][0]) < mp.mpf('1e-25')  # a conjugate pair
    assert abs(exc[0][1] + exc[1][1]) < mp.mpf('1e-25')
    xs = sorted(x for x, _ in inI)                       # the bulk zeros are simple
    assert min(xs[i + 1] - xs[i] for i in range(len(xs) - 1)) > mp.mpf('1e-6')
    assert len(sp.Poly(PB[m], z).real_roots()) == len(set(sp.Poly(PB[m], z).real_roots()))
    panelB[m] = (inI, exc)
    print(f'  m = {m:2d}: deg P_m = {poly.degree():2d}, {len(inI)} zeros in I, '
          f'{len(exc)} exceptional at {mp.nstr(exc[1][0], 8)} +- {mp.nstr(exc[1][1], 8)}i'
          + (f', drift from m = {MS[0]}: {mp.nstr(drift, 4)}' if drift else ''))

# ===========================================================================
# emit the pgfplots coordinate blocks
# ===========================================================================
OUT = 'figure_pole_geom.tex'


def fmt(x, y, digits=6):
    return f'({mp.nstr(x, digits, strip_zeros=False)},{mp.nstr(y, digits, strip_zeros=False)})'


def wrap(pairs, per_line=6, indent='  '):
    lines, cur = [], []
    for p in pairs:
        cur.append(p)
        if len(cur) == per_line:
            lines.append(indent + ' '.join(cur))
            cur = []
    if cur:
        lines.append(indent + ' '.join(cur))
    return '\n'.join(lines)


ENV = 61
egrid = [TH_L + (TH_R - TH_L) * mp.mpf(i) / (ENV - 1) for i in range(ENV)]
evals = [curve(th)[1] for th in egrid]

yA = 5 * mp.ceil(ymax * mp.mpf('1.13') / 5)              # panel A half-height, rounded
xB_lo, xB_hi = mp.mpf('-1.05'), mp.mpf('4.05')
yB = mp.mpf('1.72')

TEMPLATE = r"""% Generated by scripts/make_figure_pole_geom.py -- do not edit by hand.
\begin{figure}[p]
\centering
\begin{tikzpicture}
\begin{axis}[
    name=panelA,
    width=12.7cm, height=5.9cm,
    xlabel={\(\theta\)}, ylabel={\(\tau(\theta)^{M+1}F_M(z(\theta))\)},
    xmin=0, xmax=@@PI@@, ymin=-@@YA@@, ymax=@@YA@@,
    xtick={0,0.7853981634,1.5707963268,2.3561944902,3.1415926536},
    xticklabels={\(0\),\(\pi/4\),\(\pi/2\),\(3\pi/4\),\(\pi\)},
    ytick={-40,-20,0,20,40},
    tick label style={font=\footnotesize}, label style={font=\small},
    title={\footnotesize(A)},
    title style={at={(0,1)}, anchor=south west, yshift=1pt},
    axis lines=left, axis on top, clip=true,
]
\fill[black!9] (axis cs:0,-@@YA@@) rectangle (axis cs:@@THL@@,@@YA@@);
\fill[black!9] (axis cs:@@THR@@,-@@YA@@) rectangle (axis cs:@@PI@@,@@YA@@);
\addplot[black!30, line width=0.5pt, forget plot]
  coordinates {(0,0) (@@PI@@,0)};
\addplot[black!45, dotted, line width=0.7pt, forget plot]
  coordinates {(1.5707963268,-@@YA@@) (1.5707963268,@@YA@@)};
\addplot[black!60, dashed, line width=0.8pt, forget plot] coordinates {
@@ENVUP@@
};
\addplot[black!60, dashed, line width=0.8pt, forget plot] coordinates {
@@ENVLO@@
};
\addplot[black!78, line width=0.9pt, forget plot] coordinates {
@@CURVE@@
};
\node[font=\scriptsize, rotate=90, black!70] at (axis cs:@@THLMID@@,0)
  {\(\theta<h/M\)};
\node[font=\scriptsize, rotate=90, black!70] at (axis cs:@@THRMID@@,0)
  {\(\theta>\pi/r-h/M\)};
\node[font=\scriptsize, anchor=south east] at (axis cs:1.5560,40)
  {\(\theta_1=\pi/2\)};
\node[font=\scriptsize, anchor=west] at (axis cs:2.02,36) {\(\pm2|W(\theta)|\)};
\draw[black!55, line width=0.4pt] (axis cs:2.24,31.2) -- (axis cs:2.35,14.6);
\end{axis}

\begin{axis}[
    name=panelB,
    at={(panelA.below south west)}, anchor=north west, yshift=-11mm,
    width=12.7cm, height=4.6cm,
    xlabel={\(\Re z\)}, ylabel={\(\Im z\)},
    xmin=@@XBLO@@, xmax=@@XBHI@@, ymin=-@@YB@@, ymax=@@YB@@,
    xtick={-1,1,2,3,4}, ytick={-1,1},
    extra x ticks={@@A@@,@@B@@}, extra x tick labels={\(a\),\(b\)},
    extra x tick style={tick label style={font=\footnotesize, yshift=-1.2ex,
                                          xshift=3pt}},
    tick label style={font=\footnotesize}, label style={font=\small},
    title={\footnotesize(B)},
    title style={at={(0,1)}, anchor=south west, yshift=1pt},
    legend style={at={(0.985,0.94)}, anchor=north east, draw=black!40,
                  font=\footnotesize, row sep=-1pt},
    axis lines=middle, axis on top=false, clip=true,
    x label style={at={(ticklabel* cs:1.0)}, anchor=west},
    y label style={at={(ticklabel* cs:1.0)}, anchor=south},
]
\addplot[black!22, line width=2.6pt, forget plot]
  coordinates {(@@A@@,0) (@@B@@,0)};
\node[font=\footnotesize, anchor=south] at (axis cs:2.1,0.28) {\(I_{Q,r}\)};
\addplot[black!40, dotted, line width=0.6pt, forget plot]
  coordinates {(@@A@@,-@@YB@@) (@@A@@,@@YB@@)};
\addplot[black!40, dotted, line width=0.6pt, forget plot]
  coordinates {(@@B@@,-@@YB@@) (@@B@@,@@YB@@)};
\addplot[black, only marks, mark=o, mark size=1.9pt, line width=0.5pt] coordinates {
@@BULK14@@
};
\addlegendentry{\(m=14\)}
\addplot[black, only marks, mark=*, mark size=0.9pt] coordinates {
@@BULK38@@
};
\addlegendentry{\(m=38\)}
\addplot[black, only marks, mark=o, mark size=1.9pt, line width=0.5pt, forget plot]
  coordinates {@@EXC@@};
\addplot[black, only marks, mark=*, mark size=0.9pt, forget plot]
  coordinates {@@EXC@@};
\draw[black!45, line width=0.5pt]
  (axis cs:@@EXCX@@,@@EXCY@@) circle [radius=5.6pt];
\draw[black!45, line width=0.5pt]
  (axis cs:@@EXCX@@,-@@EXCY@@) circle [radius=5.6pt];
\node[font=\scriptsize, anchor=west, align=left] at (axis cs:0.32,1.22)
  {exceptional pair,\\[-2pt] both indices};
\draw[black!55, line width=0.4pt] (axis cs:0.30,1.22) -- (axis cs:-0.45,1.34);
\end{axis}
\end{tikzpicture}
\caption{One denominator, two numerators.  Throughout
\(Q(t)=(1-t)(1-t/2)(1-t/4)\) and \(r=1\).  The upper endpoint is finite because
\(r=1\), and the smallest zero of \(Q\) is simple, so \(a>0\); thus
\(I_{Q,r}=(a,b)=(0.0559\ldots,3.7466\ldots)\).
\textbf{(A)}~The decomposition \eqref{eq:principal-decomposition} at \(M=14\)
for \(N(t,z)=B(t)=7t^2+8\), which \Cref{lem:laurent-reduction} leaves
unshifted, with the principal-pair envelope \(\pm2|W(\theta)|\) of
\eqref{eq:W-def} dashed.
Consecutive phase points enclose distinct zeros in \(I_{Q,r}\)
(\Cref{prop:univariate-main}).  Since \(t_+(\pi/2)=i\sqrt{8/7}\) and
\(z(\pi/2)=45/28\), one has \(B(t_+(\pi/2))=0\), so \(W\) has an amplitude zero
at \(\theta_1=\pi/2\) and the envelope pinches there; the neighborhood of
\(\theta_1\) deleted in \eqref{eq:amplitude-deletion} is exponentially small in
\(M\).  Numerically, the dominance inequality \eqref{eq:dominance-bound} fails
only within \(10^{-11}\) of \(\theta_1\) at this \(M\), too narrow
to draw.  The shaded endpoint windows of
\eqref{eq:retained-range} are drawn wider than \(h\) requires, which keeps on
scale an envelope that grows without bound at either endpoint.
\textbf{(B)}~Zeros of \(P_m\) for the numerator
\(N(t,z)=(1+z+z^2)+t(2-z)\), which is not of the form \(R(z)S(t)\): its
exceptional zeros are created by the initial data rather than factored out of it
as in \Cref{prop:N-dependence}.  At each displayed index, \(\deg P_m=m+2\), with
\(m\) simple zeros in \(I_{Q,r}\) and exactly two elsewhere, a conjugate pair at
\(-0.5655\ldots\pm1.3674\ldots i\) agreeing to thirteen decimals at the two
indices.  The bulk grows with \(m\); the defect does not.}
\label{fig:decomposition-and-defect}
\end{figure}
"""

subs = {
    '@@PI@@': mp.nstr(mp.pi, 11, strip_zeros=False),
    '@@YA@@': mp.nstr(yA, 4, strip_zeros=False),
    '@@THL@@': mp.nstr(TH_L, 6, strip_zeros=False),
    '@@THR@@': mp.nstr(TH_R, 6, strip_zeros=False),
    '@@THLMID@@': mp.nstr(TH_L / 2, 6, strip_zeros=False),
    '@@THRMID@@': mp.nstr((TH_R + mp.pi) / 2, 6, strip_zeros=False),
    '@@XBLO@@': mp.nstr(xB_lo, 4, strip_zeros=False),
    '@@XBHI@@': mp.nstr(xB_hi, 4, strip_zeros=False),
    '@@YB@@': mp.nstr(yB, 4, strip_zeros=False),
    '@@A@@': mp.nstr(a, 7, strip_zeros=False),
    '@@B@@': mp.nstr(b, 7, strip_zeros=False),
    '@@EXCX@@': mp.nstr(exc_ref[1][0], 8, strip_zeros=False),
    '@@EXCY@@': mp.nstr(exc_ref[1][1], 8, strip_zeros=False),
    '@@ENVUP@@': wrap([fmt(th, e) for th, e in zip(egrid, evals)]),
    '@@ENVLO@@': wrap([fmt(th, -e) for th, e in zip(egrid, evals)]),
    '@@CURVE@@': wrap([fmt(th, v) for th, v in zip(grid, vals)]),
    '@@BULK14@@': wrap([fmt(x, 0) for x, _ in panelB[MS[0]][0]]),
    '@@BULK38@@': wrap([fmt(x, 0) for x, _ in panelB[MS[1]][0]]),
    '@@EXC@@': ' '.join(fmt(x, y) for x, y in exc_ref),
}
out = TEMPLATE
for k, v in subs.items():
    out = out.replace(k, v)
assert '@@' not in out, 'unsubstituted placeholder'
with open(OUT, 'w') as f:
    f.write(out)

print(f'\nwrote {OUT}  (panel A half-height {mp.nstr(yA, 4)}, '
       f'{len(grid)} curve points, {ENV} envelope points)')
print('ALL PASS: make_figure_pole_geom')
