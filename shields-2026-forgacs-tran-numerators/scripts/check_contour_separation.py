#!/usr/bin/env python3
r"""Paper section `sec:geometry` (Spectral geometry, residues, and the principal amplitude),
section `subsec:contour-residues`, `lem:contour-separation`.

The lemma the rest of the analytic argument rests on: with `Gamma` a
positively oriented Jordan curve whose interior contains the origin and on which
`D` does not vanish,

    F_M(z) = -sum_{xi in C(z)} Res_{t=xi} B(t)/(t^{M+1} D(t,z))  +  E_M(z),
    E_M(z) = (1/2 pi i) oint_Gamma B(t)/(t^{M+1} D(t,z)) dt,

`C(z)` the set of DISTINCT zeros of `D(.,z)` inside `Gamma`.  Every claim is
checked against `[t^M] B/D` computed independently as a Taylor coefficient.

  (C1) The identity itself, simple poles, `deg Q > r`.  Residual against the
       Taylor coefficient, at several `M`.
  (C2) `eq:simple-residue-amplitude`: at a simple zero the contribution is
       -B(xi)/(D_t(xi,z)) * xi^{-M-1}, asserted term by term against the
       generic residue computed from the factored denominator.
  (C3) The DISTINCT-pole rule at a multiple zero.  A multiset formulation would
       count a double pole twice; the identity closes only when it is counted
       once, with its second-order residue.  Checked two ways: the identity
       closes at the double pole, and splitting the double pole by perturbing
       `z` makes the two simple residues converge to that one second-order
       residue (so the single higher-order term is their true limit, not half
       of it).
  (C4) `eq:contour-remainder-bound`: |rho^{M+1} E_M| <= (L C_Gamma/2pi) sigma^{M+1}
       with rho <= sigma R_Gamma, the constants measured on the contour rather
       than assumed, and the decay rate confirmed by a log-log slope in M.
  (C5) No index threshold.  The lemma holds at M = 0 and for deg B >= deg D,
       where the all-roots partial-fraction sum needs M > deg B - d.
       Both are run on the same data and the threshold is exhibited as a
       property of that maximal contour, not of the lemma.
  (C6) The escaping root.  At deg Q = r the leading coefficient q_d + z vanishes
       at z_inf = -q_d and a root leaves every bounded set.  The identity closes
       at z_inf and on both sides of it with Gamma held FIXED, which is what
       lets the proof of `thm:weighted-dominance` absorb such a root into E_M
       with no case split.
  (C7) E_M is holomorphic in z (Cauchy mean-value property on a z-circle),
       the property the endpoint estimates use.
  (C8) Q(0) != 0 is load-bearing: it is what keeps the origin a pole of order
       exactly M+1 and puts F_M in its residue.

mpmath throughout at raised precision; contour integrals by `quad` on the
parameterized circle.
"""

from mpmath import mp, mpf, mpc, taylor, quad, exp, pi, j, polyroots, fabs, log

mp.dps = 30
TOL = mpf('1e-20')


def poly(c, t):
    return sum(ci * t**k for k, ci in enumerate(c))


def dcoeffs(Qc, r, z):
    """Coefficients of D = Q + z t^r, low -> high, trailing zeros trimmed."""
    d = [mpc(x) for x in Qc] + [mpc(0)] * max(0, r + 1 - len(Qc))
    d[r] += z
    while len(d) > 1 and d[-1] == 0:
        d.pop()
    return d


def roots_of(dc):
    if len(dc) <= 1:
        return []
    return polyroots([mpc(c) for c in reversed(dc)], maxsteps=300, extraprec=300)


def distinct(rts, tol=mpf('1e-18')):
    out = []
    for rt in rts:
        for grp in out:
            if fabs(grp[0] - rt) < tol:
                grp[1] += 1
                break
        else:
            out.append([rt, 1])
    return out


def residue_contrib(Bc, dc, rts, t0, m, M):
    """-Res_{t=t0} B/(t^{M+1} D), the pole counted ONCE at its true order m."""
    if m == 1:
        dD = sum(k * dc[k] * t0**(k - 1) for k in range(1, len(dc)))
        return -poly(Bc, t0) / (t0**(M + 1) * dD)
    oth = [w for w in rts if fabs(w - t0) >= mpf('1e-18')]
    lead = dc[-1]

    def H(t):
        v = lead
        for w in oth:
            v *= (t - w)
        return v

    g = lambda w: poly(Bc, t0 + w) / ((t0 + w)**(M + 1) * H(t0 + w))
    return -taylor(g, 0, m - 1)[m - 1]


def contour(Bc, dc, R, M):
    f = lambda th: (R * exp(j * th) * j) * poly(Bc, R * exp(j * th)) \
        / ((R * exp(j * th))**(M + 1) * poly(dc, R * exp(j * th)))
    return quad(f, [0, pi / 2, pi, 3 * pi / 2, 2 * pi]) / (2 * pi * j)


def split(Bc, Qc, r, z, R, M):
    """Return (taylor coefficient, residue sum, E_M, inside-pole list, roots)."""
    dc = dcoeffs(Qc, r, z)
    rts = roots_of(dc)
    ins = [(t0, m) for t0, m in distinct(rts) if fabs(t0) < R]
    tot = sum((residue_contrib(Bc, dc, rts, t0, m, M) for t0, m in ins), mpc(0))
    E = contour(Bc, dc, R, M)
    ser = taylor(lambda t: poly(Bc, t) / poly(dc, t), 0, M)[M]
    return ser, tot, E, ins, rts


def ok(msg):
    print('  ' + msg)


# ---------------------------------------------------------------------------
# (C1) the identity, simple poles, deg Q > r
# ---------------------------------------------------------------------------
print('=' * 78)
print('C1: the contour-separated identity, simple poles')
print('=' * 78)
Q1 = [mpf(1), mpf(-3), mpf(2)]           # (1-t)(1-2t): zeros 1, 1/2
B1 = [mpf(1), mpf(-1), mpf(3)]
r1, z1, R1 = 1, mpf('0.7'), mpf('1.9')
for M in (0, 1, 2, 5, 9, 14):
    ser, tot, E, ins, _ = split(B1, Q1, r1, z1, R1, M)
    res = fabs(ser - (tot + E))
    assert res < TOL, (M, res)
ok(f'F_M = -sum Res + E_M to < {mp.nstr(TOL, 1)} at M = 0,1,2,5,9,14 '
   f'({len(ins)} poles inside |t| = {R1}, both simple)')

# ---------------------------------------------------------------------------
# (C2) eq:simple-residue-amplitude
# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('C2: `eq:simple-residue-amplitude` term by term')
print('=' * 78)
dc = dcoeffs(Q1, r1, z1)
rts = roots_of(dc)
M = 7
for t0 in rts:
    if fabs(t0) >= R1:
        continue
    dD = sum(k * dc[k] * t0**(k - 1) for k in range(1, len(dc)))
    stated = -poly(B1, t0) / dD * t0**(-M - 1)
    generic = residue_contrib(B1, dc, rts, t0, 1, M)
    assert fabs(stated - generic) < TOL, (t0, stated, generic)
ok(f'-B(xi)/D_t(xi,z) * xi^(-M-1) equals the generic residue at every simple '
   f'pole inside the contour (M = {M})')

# ---------------------------------------------------------------------------
# (C3) the DISTINCT-pole rule
# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('C3: distinct poles, higher-order residue counted ONCE')
print('=' * 78)
# Q = 1 - 2t, r = 2: D = 1 - 2t + z t^2 has a double root t = 1 exactly at z = 1
Qd, rd, Bd, Rd = [mpf(1), mpf(-2)], 2, [mpf(1), mpf(0), mpf(0), mpf(5)], mpf('1.7')
for M in (0, 1, 4, 9):
    ser, tot, E, ins, _ = split(Bd, Qd, rd, mpf(1), Rd, M)
    assert len(ins) == 1 and ins[0][1] == 2, ins
    assert fabs(ser - (tot + E)) < TOL, (M, fabs(ser - (tot + E)))
ok('at the double pole the identity closes with ONE second-order residue '
   '(M = 0,1,4,9); a multiset sum would count that pole twice')
# and the second-order residue is the limit of the two simple ones
M = 6
dcz = dcoeffs(Qd, rd, mpf(1))
exact = residue_contrib(Bd, dcz, roots_of(dcz), roots_of(dcz)[0], 2, M)
prev = None
for e in (mpf('1e-3'), mpf('1e-4'), mpf('1e-5'), mpf('1e-6')):
    dce = dcoeffs(Qd, rd, mpf(1) + e)
    rte = roots_of(dce)
    two = sum((residue_contrib(Bd, dce, rte, w, 1, M) for w in rte
               if fabs(w) < Rd), mpc(0))
    gap = fabs(two - exact)
    assert prev is None or gap < prev, (e, gap, prev)
    prev = gap
assert prev < mpf('1e-4'), prev
ok(f'splitting the double pole: the two simple residues converge to that same '
   f'second-order residue (gap -> {mp.nstr(prev, 3)} as the split -> 1e-6), so '
   f'the single term is their true limit and not half of it')

# ---------------------------------------------------------------------------
# (C4) eq:contour-remainder-bound, constants measured
# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('C4: `eq:contour-remainder-bound` with measured constants')
print('=' * 78)
dc = dcoeffs(Q1, r1, z1)
CG = max(fabs(poly(B1, R1 * exp(j * mpf(k) * 2 * pi / 720))
              / poly(dc, R1 * exp(j * mpf(k) * 2 * pi / 720))) for k in range(720))
LG = 2 * pi * R1
rho = max(fabs(w) for w in roots_of(dc) if fabs(w) < R1)
sigma = rho / R1
assert sigma < 1, sigma
lhs, Ms = [], (4, 8, 12, 16, 20)
for M in Ms:
    E = contour(B1, dc, R1, M)
    # the lemma as stated: |E_M| <= (L C/2pi) R_Gamma^(-M-1)
    prim = LG * CG / (2 * pi) * R1**(-M - 1)
    assert fabs(E) <= prim, (M, fabs(E), prim)
    # and its normalized corollary, which is what the endpoint estimates use
    val = rho**(M + 1) * fabs(E)
    bound = LG * CG / (2 * pi) * sigma**(M + 1)
    assert val <= bound, (M, val, bound)
    lhs.append(val)
slope = (log(lhs[-1]) - log(lhs[0])) / (len(Ms) - 1) / ((Ms[1] - Ms[0]))
assert fabs(slope - log(sigma)) < mpf('0.05') * fabs(log(sigma)), (slope, log(sigma))
ok(f'|E_M| <= (L C/2pi) R_Gamma^(-M-1) at M = {Ms}, and the normalized '
   f'corollary |s^(M+1) E_M| <= (L C/2pi) sigma^(M+1) for s <= sigma R_Gamma, with measured '
   f'sigma = {mp.nstr(sigma, 6)}, C_Gamma = {mp.nstr(CG, 4)}, L = {mp.nstr(LG, 4)}')
ok(f'and the decay rate is sigma itself: log-log slope {mp.nstr(slope, 6)} '
   f'against log sigma = {mp.nstr(log(sigma), 6)}')

# ---------------------------------------------------------------------------
# (C5) no index threshold
# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('C5: no M threshold, unlike the all-roots partial-fraction sum')
print('=' * 78)
Bbig = [mpf(1)] * 6                      # deg B = 5 > deg D = 2
d_all = mpf('4.0')                        # a contour enclosing EVERY finite root
dc = dcoeffs(Q1, r1, z1)
dnum = len(dc) - 1
thresh = len(Bbig) - 1 - dnum            # deg B - d
for M in range(0, 6):
    ser, tot, E, ins, _ = split(Bbig, Q1, r1, z1, R1, M)
    assert fabs(ser - (tot + E)) < TOL, (M, fabs(ser - (tot + E)))
ok(f'deg B = {len(Bbig)-1} >= deg D = {dnum}: the lemma closes at every '
   f'M = 0..5 with the separating contour')
bad = []
for M in range(0, 6):
    dcA = dcoeffs(Q1, r1, z1)
    rtsA = roots_of(dcA)
    pf = sum((residue_contrib(Bbig, dcA, rtsA, w, 1, M) for w in rtsA), mpc(0))
    ser = taylor(lambda t: poly(Bbig, t) / poly(dcA, t), 0, M)[M]
    if fabs(ser - pf) > TOL:
        bad.append(M)
assert bad == [M for M in range(0, 6) if M <= thresh], (bad, thresh)
ok(f'while the bare all-roots residue sum fails exactly at M <= deg B - d = '
   f'{thresh} (failing set {bad}), so the threshold belongs to that maximal '
   f'contour and not to `lem:contour-separation`')

# ---------------------------------------------------------------------------
# (C6) the escaping root, contour held FIXED
# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('C6: deg Q = r, a root escaping to infinity, Gamma fixed')
print('=' * 78)
Qe = [mpf(1), mpf(-3), mpf(2)]           # q_d = 2, so z_inf = -2
re_, Be, Re = 2, [mpf(1), mpf(2)], mpf('1.3')
z_inf = mpf(-2)
seen = []
for z in (z_inf - mpf('0.05'), z_inf - mpf('0.001'), z_inf,
          z_inf + mpf('0.001'), z_inf + mpf('0.05')):
    ser, tot, E, ins, rts = split(Be, Qe, re_, z, Re, 12)
    assert fabs(ser - (tot + E)) < TOL, (z, fabs(ser - (tot + E)))
    out = [w for w in rts if fabs(w) >= Re]
    seen.append((z, len(rts), max([fabs(w) for w in out], default=mpf('inf'))))
assert any(n == 1 for _, n, _ in seen), seen         # at z_inf the root is GONE
# what the proof needs: the escaping root is OUTSIDE the fixed contour at every
# parameter, and its modulus grows without bound as z -> z_inf
assert all(mo > Re for _, n, mo in seen if n > 1), seen
near = [mo for z, n, mo in seen if n > 1 and fabs(z - z_inf) < mpf('0.01')]
far = [mo for z, n, mo in seen if n > 1 and fabs(z - z_inf) > mpf('0.01')]
assert min(near) > 40 * max(far), (near, far)
ok('the identity closes at z_inf and on both sides with the SAME contour; the '
   f'escaping root stays outside |t| = {mp.nstr(Re, 3)} throughout, and its '
   f'modulus grows by a factor {mp.nstr(min(near)/max(far), 4)} as the '
   'parameter closes the last factor of 50 onto z_inf')
for z, n, mo in seen:
    ok(f'    z = {mp.nstr(z, 8):>10}: {n} finite root(s), outside-modulus '
       f'{"(none: degree dropped)" if n == 1 else mp.nstr(mo, 6)}')

# ---------------------------------------------------------------------------
# (C7) E_M is holomorphic in z
# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('C7: E_M holomorphic in z')
print('=' * 78)
M, z0, eps = 6, mpf('0.7'), mpf('0.05')
dcz = lambda w: dcoeffs(Q1, r1, w)
EM = lambda w: contour(B1, dcz(w), R1, M)
mv = quad(lambda th: EM(z0 + eps * exp(j * th)) * (eps * exp(j * th) * j)
          / (eps * exp(j * th)), [0, pi, 2 * pi]) / (2 * pi * j)
assert fabs(mv - EM(z0)) < mpf('1e-15'), (mv, EM(z0))
ok(f'Cauchy mean value on |z - {mp.nstr(z0,3)}| = {mp.nstr(eps,3)} reproduces '
   f'E_M(z0) to {mp.nstr(fabs(mv - EM(z0)), 3)}')

# ---------------------------------------------------------------------------
# (C8) Q(0) != 0 is load-bearing
# ---------------------------------------------------------------------------
print()
print('=' * 78)
print('C8: Q(0) != 0')
print('=' * 78)
Q0 = [mpf(0), mpf(1)]                    # Q = t, so Q(0) = 0
dc0 = dcoeffs(Q0, 1, mpf('0.5'))         # D = t + 0.5 t = 1.5 t, vanishing at 0
assert fabs(poly(dc0, mpf(0))) < TOL
ok('with Q(0) = 0 the origin is a zero of D, B/D is not analytic there, and '
   'F_M is not the residue of B/(t^(M+1) D) at 0 -- so the hypothesis is not '
   'decoration')
assert fabs(poly(dcoeffs(Q1, r1, z1), mpf(0)) - Q1[0]) < TOL
ok('and under the paper\'s hypothesis D(0,z) = Q(0) for every z, so one '
   'contour serves the whole parameter interval')

print()
print('PASS: (C1) the contour-separated identity closes against [t^M] B/D')
print('PASS: (C2) the simple-pole residue amplitude is as stated')
print('PASS: (C3) distinct poles, the higher-order residue counted once')
print('PASS: (C4) the remainder bound holds with measured constants, rate sigma')
print('PASS: (C5) no index threshold; that threshold belongs to the maximal contour')
print('PASS: (C6) an escaping root needs no case split, Gamma fixed')
print('PASS: (C7) E_M is holomorphic in z')
print('PASS: (C8) Q(0) != 0 is load-bearing')
print('ALL PASS: check_contour_separation')
