#!/usr/bin/env python3
r"""Paper section `sec:scaling` (Critical wall fan and equivalence of ensembles), sec:scaling:
the figure fig:wall-fan, thm:wall-fan and cor:wall-orientation.

Verifies every claim the figure and its caption make about the coefficient-wall
fan at the representative value a = 1, and emits the pgfplots line block the
figure inlines:

  * the plotted lines are the EXACT degree walls of eq. (coefficient-wall),
    tau_n(a,kappa) = 1 - (Delta_n + (kappa-1) q_n)/p_n, not their asymptotic
    approximations.  Delta_n, p_n and q_n are built twice by routes that share
    no code -- once from the endpoint fibers M_m of sec:coefficients (the
    _wallfan_common convolution used by the other wall probes), once by direct
    Cauchy multiplication of the Maclaurin series of Z, Z_a, Z_aa, Z_Theta,
    Z_ThetaTheta and Z_aTheta -- and the two are required to agree;
  * the accumulation point, in closed form: tau_infty(1) = psi_1(1)/8 = pi^2/48,
    and tau_n(1,1) -> tau_infty(1) monotonically from above, the a > 11/12 side
    of eq. (wall-orientation);
  * the exposed wall: tau_1(1,kappa) = tau_cw(1,kappa) of eq. (tau-cw) identically
    in kappa, with the closed form tau_cw(1,1) = pi^2/(2(pi^2-3)), and tau_1 is
    the strict maximum over the plotted degrees at every kappa >= 1;
  * the ordering eq. (wall-ordering) at a = 1: tau_infty(1) < tau_cw(1,1) < 1;
  * the slope identity d tau_n/d kappa = -q_n/p_n exactly, the strict ordering
    q_n/p_n > gn/4 of eq. (qn-pn-ratio) that keeps degree one exposed, and the
    asymptotic -q_n/p_n ~ -psi_1(1) n/4 the caption quotes;
  * the divergence the figure shows on the kappa < 1 side: at fixed kappa < 1 the
    walls are eventually strictly increasing in n and outgrow (g n/4)(1-kappa),
    which is why no tau succeeds when kappa < 1;
  * that the drawn window is honest -- the n = 1 wall lies inside it across the
    whole kappa range, the focus point is interior, and every line that leaves
    the box does so through the top or bottom edge (pgfplots clips it) rather
    than being silently truncated in the data.

Numerical work is mpmath at arbitrary precision.  Run with no arguments to check
only; run with --emit to also print the line block to stdout.
"""

import sys

from mpmath import mp, mpf, psi, gamma, factorial, pi

from _wallfan_common import build_S, wall_data, tau_infty

mp.dps = 40

# --- the figure's declared parameters, mirrored from the .tex ---------------
A_FIG = mpf(1)                      # representative value; not multicritical
N_MAX = 22                          # degrees plotted, n = 1 .. N_MAX
K_LO, K_HI = mpf('0.90'), mpf('1.15')
Y_MIN, Y_MAX = mpf('-0.35'), mpf('1.15')
NS = list(range(1, N_MAX + 1))

g = psi(1, A_FIG)


def tau_cw(a, kappa):
    """eq. (tau-cw)."""
    gg = psi(1, a)
    return (a * gg * (2 * a - 1) - mpf(1) / 2 * (kappa - 1) * a**2 * gg**2) / (2 * a**2 * gg - 1)


# --- route B: Cauchy products of the defining Maclaurin series --------------
def _mul(u, v, N):
    return [sum(u[i] * v[m - i] for i in range(m + 1)) for m in range(N + 1)]


def series_route(a, N):
    """Delta_n, p_n, q_n from eq. (Adef)-(Ckt-def), (PQdef) by direct series
    multiplication -- no fibers, no convolution identity, no shared code."""
    gg = psi(1, a)
    z = [1 / (factorial(k) * gamma(a + k)) for k in range(N + 1)]
    za = [-psi(0, a + k) * z[k] for k in range(N + 1)]
    zaa = [(psi(0, a + k)**2 - psi(1, a + k)) * z[k] for k in range(N + 1)]
    zt = [k * z[k] for k in range(N + 1)]
    ztt = [k * k * z[k] for k in range(N + 1)]
    zat = [k * za[k] for k in range(N + 1)]

    A = [x - y for x, y in zip(_mul(za, za, N), _mul(z, zaa, N))]
    zz = _mul(z, z, N)
    B = [p + q - r for p, q, r in zip(zz, _mul(z, zat, N), _mul(za, zt, N))]
    C = [w + gg * (x - y + v) for w, x, y, v in
         zip(zz, _mul(z, zt, N), _mul(z, ztt, N), _mul(zt, zt, N))]
    D = [x - gg * y for x, y in zip(_mul(A, C, N), _mul(B, B, N))]
    P = _mul(A, zz, N)
    Q = [gg * x for x in _mul(A, _mul(z, zt, N), N)]
    return {n: (D[n], P[n], Q[n]) for n in range(N + 1)}


# --- the two routes must agree, which is what licenses "exact" --------------
S = build_S(A_FIG, N_MAX)
fibers = wall_data(A_FIG, S, NS)
series = series_route(A_FIG, N_MAX)
worst = mpf(0)
for n in NS:
    for x, y in zip(fibers[n], series[n]):
        worst = max(worst, abs(x - y) / abs(y))
assert worst < mpf('1e-30'), worst
print(f'PASS: Delta_n, p_n, q_n agree to {mp.nstr(worst, 3)} relative, '
      f'n <= {N_MAX}, endpoint fibers vs direct series -- the plotted walls are exact')

D_n = {n: fibers[n][0] for n in NS}
p_n = {n: fibers[n][1] for n in NS}
q_n = {n: fibers[n][2] for n in NS}


def tau_n(n, kappa):
    """eq. (coefficient-wall)."""
    return 1 - (D_n[n] + (kappa - 1) * q_n[n]) / p_n[n]


# --- the accumulation point, in closed form -------------------------------
t_inf = tau_infty(A_FIG)
assert abs(t_inf - g / 8) < mpf('1e-35')
assert abs(t_inf - pi**2 / 48) < mpf('1e-35')
gaps = [tau_n(n, 1) - t_inf for n in NS]
assert all(x > 0 for x in gaps)
assert all(b < a_ for a_, b in zip(gaps, gaps[1:]))
print(f'PASS: tau_infty(1) = psi_1(1)/8 = pi^2/48 = {mp.nstr(t_inf, 12)}, '
      f'and tau_n(1,1) decreases to it (the a > 11/12 side of wall-orientation)')

# --- the n = 1 wall IS the coefficientwise wall ---------------------------
for k in ['0.90', '1.00', '1.05', '1.15', '2.00']:
    kk = mpf(k)
    assert abs(tau_n(1, kk) - tau_cw(A_FIG, kk)) < mpf('1e-32'), k
cw1 = tau_cw(A_FIG, 1)
assert abs(cw1 - pi**2 / (2 * (pi**2 - 3))) < mpf('1e-32')
assert t_inf < cw1 < 1
print(f'PASS: tau_1(1,kappa) = tau_cw(1,kappa) identically; '
      f'tau_cw(1,1) = pi^2/(2(pi^2-3)) = {mp.nstr(cw1, 12)}, '
      f'and tau_infty < tau_cw < 1 (wall-ordering)')

# --- degree one is exposed: it is the strict max for kappa >= 1 ------------
for k in ['1.00', '1.02', '1.05', '1.10', '1.15']:
    kk = mpf(k)
    vals = [tau_n(n, kk) for n in NS]
    assert vals[0] == max(vals) and all(v < vals[0] for v in vals[1:]), k
print(f'PASS: tau_1 is the strict maximum over n <= {N_MAX} at every plotted kappa >= 1')

# --- slopes: exact identity, strict ordering, asymptotic ------------------
for n in NS:
    num = tau_n(n, mpf('1.3')) - tau_n(n, mpf('0.7'))
    assert abs(num / mpf('0.6') + q_n[n] / p_n[n]) < mpf('1e-30'), n
    assert q_n[n] / p_n[n] > g * n / 4, n
ratio = (q_n[N_MAX] / p_n[N_MAX]) / (g * N_MAX / 4)
assert 1 < ratio < mpf('1.03'), ratio
print(f'PASS: d tau_n/d kappa = -q_n/p_n exactly, q_n/p_n > gn/4 strictly '
      f'(eq. qn-pn-ratio), and the ratio to gn/4 is {mp.nstr(ratio, 8)} at n = {N_MAX}')

# --- the kappa < 1 divergence the figure displays -------------------------
kk = K_LO
walls = [tau_n(n, kk) for n in NS]
tail = walls[4:]
assert all(b > a_ for a_, b in zip(tail, tail[1:]))
assert walls[-1] > t_inf + g * N_MAX / 4 * (1 - kk)
print(f'PASS: at kappa = {mp.nstr(kk, 3)} the walls rise past '
      f'{mp.nstr(walls[-1], 8)} and outgrow (gn/4)(1-kappa) -- no tau succeeds for kappa < 1')

# --- the drawn window is honest ------------------------------------------
lines = [(n, tau_n(n, K_LO), tau_n(n, K_HI)) for n in NS]
assert all(Y_MIN < y < Y_MAX for y in lines[0][1:])
assert K_LO < 1 < K_HI and Y_MIN < t_inf < Y_MAX and Y_MIN < 1 < Y_MAX
for n, lo, hi in lines:
    assert lo > hi, n
    assert not (lo < Y_MIN or hi > Y_MAX), n          # only ever leaves downward
n_clipped = sum(1 for _, lo, hi in lines if hi < Y_MIN or lo > Y_MAX)
print(f'PASS: the n = 1 wall and both marked levels lie inside '
      f'[{mp.nstr(Y_MIN, 3)}, {mp.nstr(Y_MAX, 3)}]; every wall falls left to right, '
      f'and {n_clipped} leave the box only through an edge pgfplots clips')

# --- emit the pgfplots line block ----------------------------------------
if '--emit' in sys.argv:
    print()
    for n, lo, hi in lines:
        style = ('black, line width=1.0pt' if n == 1
                 else f'black!{38 + min(30, n)}, line width=0.45pt')
        print(f'\\addplot[{style}, forget plot] coordinates '
              f'{{({mp.nstr(K_LO, 4, strip_zeros=False)},{mp.nstr(lo, 9, strip_zeros=False)}) '
              f'({mp.nstr(K_HI, 4, strip_zeros=False)},{mp.nstr(hi, 9, strip_zeros=False)})}};')
    print(f'%% tau_infty(1) = {mp.nstr(t_inf, 20)}   tau_cw(1,1) = {mp.nstr(cw1, 20)}')

print('\nALL PASS')
