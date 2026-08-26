"""Q = (1-t)^3 with r = 3: the first pencil whose two clusters are both non-empty.

Every witness in the tree so far has had one endpoint empty.  `CubicWitness`
(Q = (1-t)^3, r = 1) has rho = 3 at the lower endpoint and an empty upper
cluster; `UpperClusterWitness` (Q = 1 - t, r = 3) has the mirror defect.  Here
the triple zero gives rho = 3 and n0 = rho - 2 = 1, and r = 3 gives
n1 = r - 2 = 1, so BOTH cluster binder families are instantiated non-vacuously
at one pencil -- which is what a joint instantiation of
`weighted_dominance_of_branch` needs.

The branch is rational in a parameter.  z = -((1-t)/t)^3 is real exactly when
arg((1-t)/t) is a multiple of pi/3; taking w = (1-t)/t = rho e^{-i pi/3} makes
z = -w^3 = rho^3 real with nothing to solve, because the locus is a RAY in w
rather than a curve cut out by an equation.  Then t = 1/(1+w) and

    tau(rho) = 1/sqrt(1 + rho + rho^2)      theta(rho) = arctan(sqrt3 rho/(2+rho))

This script checks that, and then checks the sharper closed forms it collapses
to.  Eliminating rho in favor of theta -- rho(theta) = sin(theta)/cos(theta+pi/6)
-- removes every square root and every arctangent:

    tau(theta)   = (2/sqrt3) cos(theta + pi/6)
    t3(theta)    = cos(theta + pi/6) / (sqrt3 cos(theta + pi/3))
    t3/tau       = 1 / (2 cos(theta + pi/3))
    z(theta)     = (sin(theta)/cos(theta + pi/6))^3

THE ONE DEGENERACY.  D = (1-t)^3 + z t^3 = 1 - 3t + 3t^2 + (z-1)t^3 has leading
coefficient z - 1, which vanishes at rho = 1.  There the degree drops to 2 and
the third root escapes: t3 has a pole, the retained set is EXACTLY the principal
pair, and both cluster counts are 0 rather than 1.  That point is
theta = pi/6 -- the midpoint of the viewing arc (0, pi/3) -- so it is interior,
and both binder windows avoid it as long as e0 < pi/6 and e1 < pi/6.  It is a
real feature of the pencil, not an artifact of the parametrization.

THE INVOLUTION.  rho -> 1/rho maps the arc to itself by
theta -> pi/3 - theta, fixing exactly rho = 1, and it carries the normalized
nonprincipal member to MINUS itself.  In the theta closed form that is the
identity

    | ratio(pi/3 - delta) | = ratio(delta),      ratio(d) = 1/(2 cos(d + pi/3))

so ONE scalar function carries both endpoints: the lower endpoint reads it as a
complex value (hexp_0's shape) and the upper reads its modulus (hexp_1's).  That
the two binders differ in shape is not softened by the symmetry -- the symmetry
is precisely what introduces the sign that makes the complex form false at the
upper end.
"""
import mpmath as mpm

mpm.mp.dps = 45
SQ3 = mpm.sqrt(3)
PI = mpm.pi
TOL = mpm.mpf('1e-30')


def rho_of_theta(th):
    return mpm.sin(th) / mpm.cos(th + PI / 6)


def tau(th):
    return 2 * mpm.cos(th + PI / 6) / SQ3


def third(th):
    return mpm.cos(th + PI / 6) / (SQ3 * mpm.cos(th + PI / 3))


def ratio(d):
    return 1 / (2 * mpm.cos(d + PI / 3))


def zed(th):
    return rho_of_theta(th) ** 3


def den(th, w):
    return (1 - w) ** 3 + zed(th) * w ** 3


def roots(th):
    z = zed(th)
    return mpm.polyroots([z - 1, 3, -3, 1], maxsteps=400, extraprec=400)


print("pencil Q(t) = (1-t)^3, r = 3;  viewing arc (0, pi/3)")
print("rho = 3 (triple zero of Q) so n0 = rho - 2 = 1;  r = 3 so n1 = r - 2 = 1")
print()

# --- the rho parametrization agrees with the theta closed forms ------------
print("the two parametrizations agree, and the pencil vanishes on the retained set")
print(f"{'theta':>8} {'rho':>12} {'|tau_rho-tau_th|':>17} {'|D(t+)|':>10} {'|D(t3)|':>10} {'|t3/tau-ratio|':>15}")
SAMPLES = ['0.02', '0.2', '0.45', '0.6', '0.9', '1.03']
for s in SAMPLES:
    th = mpm.mpf(s)
    r = rho_of_theta(th)
    tau_rho = 1 / mpm.sqrt(1 + r + r ** 2)
    tp = tau(th) * mpm.mpc(mpm.cos(th), mpm.sin(th))
    tb = tau(th) * mpm.mpc(mpm.cos(th), -mpm.sin(th))
    t3 = mpm.mpc(third(th))
    d1, d2, d3 = abs(den(th, tp)), abs(den(th, tb)), abs(den(th, t3))
    assert abs(tau_rho - tau(th)) < TOL, f"tau closed forms disagree at {s}"
    assert abs(mpm.atan(SQ3 * r / (2 + r)) - th) < TOL, f"theta(rho) not inverse at {s}"
    for d in (d1, d2, d3):
        assert d < TOL, f"D != 0 on the retained set at theta = {s}"
    assert abs(t3 / tau(th) - ratio(th)) < TOL, f"ratio closed form wrong at {s}"
    print(f"{float(th):>8.3f} {float(r):>12.6f} {float(abs(tau_rho-tau(th))):>17.2e}"
          f" {float(d1):>10.2e} {float(d3):>10.2e} {float(abs(t3/tau(th)-ratio(th))):>15.2e}")

# --- z is real and positive, by construction rather than by solving --------
for s in SAMPLES:
    th = mpm.mpf(s)
    assert zed(th) > 0, f"z not positive at {s}"
print()
print("z = rho^3 is real and positive with no equation solved: the realness locus is a")
print("ray in w = (1-t)/t, not a curve, because arg w = -pi/3 already forces arg w^3 = -pi.")

# --- the minimum-modulus condition IS the arc condition -------------------
# tau < |t3|  <=>  2 < 1/|cos(theta+pi/3)|  <=>  |cos(theta+pi/3)| < 1/2
# <=>  theta + pi/3 in (pi/3, 2pi/3)  <=>  theta in (0, pi/3).
viol = []
for k in range(1, 2000):
    th = PI / 3 * mpm.mpf(k) / 2000
    if abs(th - PI / 6) < mpm.mpf('1e-6'):
        continue
    if not tau(th) < abs(third(th)):
        viol.append(float(th))
assert not viol, f"tau is not the minimum modulus at {viol[:5]}"
print()
print("tau is the minimum modulus at every sampled theta of the open arc, and the")
print("algebra says exactly that: tau < |t3| iff |cos(theta+pi/3)| < 1/2 iff")
print("theta in (0, pi/3).  The branch condition is the arc condition -- no extra")
print("hypothesis, and no interval where it has to be checked separately.")

# --- the degeneracy -------------------------------------------------------
print()
print("the degeneracy at rho = 1")
assert abs(rho_of_theta(PI / 6) - 1) < TOL
assert abs(zed(PI / 6) - 1) < TOL
deg_roots = mpm.polyroots([3, -3, 1])
tau6, th6 = tau(PI / 6), PI / 6
pair6 = [tau6 * mpm.mpc(mpm.cos(th6), mpm.sin(th6)),
         tau6 * mpm.mpc(mpm.cos(th6), -mpm.sin(th6))]
for a in deg_roots:
    assert min(abs(a - b) for b in pair6) < TOL, "degenerate roots are not the principal pair"
assert abs(tau6 - 1 / SQ3) < TOL
print(f"   theta = pi/6 = {float(PI/6):.9f}, rho = 1, z = 1, leading coefficient z - 1 = 0")
print(f"   D = 1 - 3t + 3t^2, degree 2, and its two roots ARE the principal pair at")
print(f"   tau = 1/sqrt3 = {float(tau6):.9f}.  So the cluster is EMPTY there, n0 = n1 = 0,")
print("   which is a sharper statement than 'the degree drops'.")
print("   pi/6 is the midpoint of (0, pi/3), so e0 < pi/6 and e1 < pi/6 avoid it.")

# --- n0 = n1 = 1, at the real objects ------------------------------------
print()
print("n0 and n1 at the real objects: the retained set less the principal pair")
print(f"{'theta':>10} {'end':>6} {'#roots':>7} {'n':>3} {'nonprincipal/tau':>26}")
for s, tag in [('1e-4', 'lower'), ('1e-3', 'lower'), ('0.01', 'lower'),
               ('1.0471', 'upper'), ('1.0471975', 'upper')]:
    th = mpm.mpf(s) if tag == 'lower' else PI / 3 - (PI / 3 - mpm.mpf(s))
    th = mpm.mpf(s)
    rts = list(roots(th))
    tp = tau(th) * mpm.mpc(mpm.cos(th), mpm.sin(th))
    tb = tau(th) * mpm.mpc(mpm.cos(th), -mpm.sin(th))
    for target in (tp, tb):
        k = min(range(len(rts)), key=lambda i: abs(rts[i] - target))
        assert abs(rts[k] - target) < mpm.mpf('1e-25'), f"principal member missing at {s}"
        rts.pop(k)
    assert len(rts) == 1, f"n = {len(rts)} at theta = {s}, expected 1"
    print(f"{float(th):>10.7f} {tag:>6} {3:>7} {len(rts):>3} {mpm.nstr(rts[0]/tau(th), 14):>26}")
print()
print("n0 = n1 = 1: three roots, the principal pair is two, one nonprincipal member at")
print("each end.  rho = 3 is the MULTIPLICITY of Q's only zero, not a count of D's")
print("roots; the two agree here only because deg D = 3.")

# --- both endpoints, one scalar function ---------------------------------
print()
print("the mirror identity, and the two expansion shapes")
print(f"{'delta':>10} {'ratio(delta)':>18} {'ratio(pi/3-delta)':>20} {'|mirror error|':>16}")
for s in ['0.3', '0.1', '0.01', '1e-3', '1e-4']:
    d = mpm.mpf(s)
    lo, up = ratio(d), ratio(PI / 3 - d)
    err = abs(abs(up) - lo)
    assert err < TOL, f"mirror identity fails at delta = {s}"
    assert lo > 0 and up < 0, f"signs wrong at delta = {s}"
    print(f"{float(d):>10.0e} {mpm.nstr(lo, 12):>18} {mpm.nstr(up, 12):>20} {float(err):>16.2e}")
print()
print("|ratio(pi/3 - delta)| = ratio(delta) exactly, and the sign is opposite.  The lower")
print("endpoint reads the value (hexp_0 bounds a complex difference), the upper reads the")
print("modulus (hexp_1 bounds a difference of moduli).  The involution does not make the")
print("two binders the same shape -- it is what puts the sign there.")

# --- the expansion, once, for both ---------------------------------------
c_pred = (mpm.cos(PI / 3) - (-1)) / mpm.sin(PI / 3)
assert abs(c_pred - SQ3) < TOL
assert abs(ratio(mpm.mpf(0)) - 1) < TOL
assert abs(mpm.diff(ratio, mpm.mpf('1e-25')) - SQ3) < mpm.mpf('1e-20')
k2 = max(abs(mpm.diff(ratio, mpm.mpf(i) / 1000, 2)) for i in range(0, 101))
assert k2 < 14, f"second derivative {k2} exceeds 14 on [0, 1/10]"
print()
print(f"ratio(0) = 1 and ratio'(0) = {mpm.nstr(SQ3, 12)} = (cos(pi/3) - Re(-1))/sin(pi/3),")
print("the same coefficient at both ends because rho = r = 3 at both.")
print(f"max |ratio''| on [0, 1/10] = {mpm.nstr(k2, 10)} < 14, so kappa_2 = 14 carries the")
print("Taylor bound -- ONE bound, used at both endpoints.")
worst = mpm.mpf(0)
for i in range(1, 101):
    d = mpm.mpf(i) / 1000
    worst = max(worst, abs(ratio(d) - (1 + SQ3 * d)) / d ** 2)
assert worst < 14, f"Taylor constant {worst} exceeds 14"
print(f"observed |ratio(d) - (1 + sqrt3 d)|/d^2 <= {mpm.nstr(worst, 8)} on (0, 1/10].")

# --- the upper amplitude ratio, and that the numerator drops out --------------
#
# hratio_1 sends the amplitude ratio to L_1, and hL_1 asks |L_1| = 1.  With
# simple zeros the cofactor at a zero is D'(t), so the ratio of amplitudes at two
# zeros is (B(g)/D'(g)) / (B(t+)/D'(t+)).  The prediction is the cluster
# direction over the principal direction, omega_2/e^{i pi/3} = e^{2 i pi/3} --
# which is the same cube root of unity the sum-of-cubes factorization runs on.
#
# B(0) != 0 means B does not vanish on this cluster, so it cancels from the
# limit.  That is checked rather than assumed, at three different numerators.
def dD(th, w):
    return -3 * (1 - w) ** 2 + 3 * zed(th) * w ** 2


def amp_ratio(th, B):
    tp = tau(th) * mpm.mpc(mpm.cos(th), mpm.sin(th))
    g = mpm.mpc(third(th))
    return (B(g) / dD(th, g)) / (B(tp) / dD(th, tp))


L1 = mpm.mpc(mpm.cos(2 * PI / 3), mpm.sin(2 * PI / 3))
print()
print("the upper amplitude ratio, at three numerators")
print(f"{'B':>12} {'delta':>9} {'ratio':>34} {'|ratio|':>13} {'|ratio - L1|':>14}")
NUMERATORS = [("1", lambda w: mpm.mpc(1)),
              ("1 + t", lambda w: 1 + w),
              ("3t^2 + 1", lambda w: 3 * w ** 2 + 1)]
for label, B in NUMERATORS:
    assert abs(B(mpm.mpf(0))) > mpm.mpf('1e-30'), f"B(0) = 0 for {label}"
    prev = None
    for k in (3, 5, 7):
        d = mpm.mpf(10) ** (-k)
        R = amp_ratio(PI / 3 - d, B)
        err = abs(R - L1)
        assert prev is None or err < prev, f"not converging for {label}"
        prev = err
        print(f"{label:>12} {float(d):>9.0e} {mpm.nstr(R, 12):>34}"
              f" {float(abs(R)):>13.10f} {float(err):>14.2e}")
    assert prev < mpm.mpf('1e-6'), f"limit not reached for {label}: {prev}"

print()
print("L_1 = omega_2 / e^{i pi/3} = -e^{-i pi/3} = e^{2 i pi/3}, modulus 1, and the same")
print("value at all three numerators -- B(0) != 0 keeps B off this cluster, so it cancels.")
print("That constant is exactly the eta of the sum-of-cubes factorization.")

# --- why hte_1 has no escape route at this pencil ---------------------------
#
# weighted_dominance_of_branch pins te_1 = ftPrincipal tau (b - 0) and asks
# te_1 != 0, i.e. tau must not vanish at the upper endpoint b = pi/r.  Here it
# does.  But that alone does not settle the question, because there is a second
# way the endpoint could carry a positive tau: at theta = pi/r the principal
# point is t+ = tau e^{i pi/r} with t+^r = -tau^r, so
#
#     D(t+) = 0   <=>   z = -Q(t+)/t+^r,   which is real  <=>  Im Q(t+) = 0.
#
# For Q = prod (1 - t/x_k) each arg(1 - tau e^{i pi/r}/x_k) sweeps
# (-(pi - pi/r), 0), so the sum reaches -pi -- and the imaginary part vanishes
# at a positive tau -- exactly when n (1 - 1/r) > 1.  At n = 3 that holds for
# every r >= 2, so a positive-tau candidate EXISTS at each of them.
#
# Every one of those candidates is excluded by the branch condition, and this is
# what the block below checks: at the candidate's own z, the minimum-modulus
# zero of the pencil is REAL, so the conjugate pair at +-pi/r is not the
# principal pair.  The branch condition is a hypothesis the theorem already
# carries, so the exclusion costs nothing extra -- but without it the refutation
# of hte_1 would be incomplete.
#
# The sign is the trap: z = -Q(t+)/t+^r, not +.  With the sign wrong the roots
# come out at moduli that make tau* look minimal at r = 2.
print()
print("hte_1: the positive-tau candidates at theta = pi/r, and why each is excluded")
print(f"{'r':>3} {'tau*':>12} {'z':>14} {'min |zero|':>12} {'arg of it':>11} {'pair minimal?':>14}")
for r in (2, 3, 4):
    ts = mpm.findroot(lambda tv: mpm.arg(1 - tv * mpm.exp(1j * PI / r)) + PI / 3,
                      mpm.mpf('1.0'))
    assert ts > 0, f"no positive candidate at r = {r}"
    tp = ts * mpm.exp(1j * PI / r)
    zc = -((1 - tp) ** 3) / (tp ** r)
    assert abs(zc.imag) < TOL, f"candidate z not real at r = {r}"
    zc = zc.real
    assert abs((1 - tp) ** 3 + zc * tp ** r) < mpm.mpf('1e-25'), f"t+ not a zero at r = {r}"
    co = [-1, 3, -3, 1]
    co[3 - r] += zc
    rts = sorted(mpm.polyroots(co, maxsteps=400, extraprec=400), key=abs)
    smallest = rts[0]
    pair_minimal = abs(abs(smallest) - ts) < mpm.mpf('1e-12')
    assert not pair_minimal, f"the pair IS minimal at r = {r} -- hte_1 would survive"
    assert abs(mpm.im(smallest)) < mpm.mpf('1e-20'), f"smallest zero not real at r = {r}"
    print(f"{r:>3} {float(ts):>12.8f} {float(zc):>14.8f} {float(abs(smallest)):>12.8f}"
          f" {float(mpm.arg(smallest)):>+11.6f} {str(pair_minimal):>14}")

print()
print("At every r >= 2 a positive-tau candidate exists and every one is excluded: the")
print("minimum-modulus zero at its own z is REAL, so the conjugate pair at +-pi/r is not")
print("the principal pair.  So hte_1 is refuted at this pencil for every r >= 2, and not")
print("merely at the r where the upper cluster is non-empty.")

# --- the parity threshold, which settles hte_1 outright below it -------------
#
# `ftInterval_subset_posRay` puts the admissible z on the POSITIVE ray, and that
# sharpens the endpoint question into two cases.
#
# z = -Q(t+)/t+^r and t+^r = -tau^r, so z = Q(t+)/tau^r and z > 0 forces Q(t+)
# real POSITIVE, i.e. arg Q(t+) in 2 pi Z.  That argument is the sum of n terms
# each in (-(pi - pi/r), 0), so it lies in (-n(pi - pi/r), 0) -- an open interval
# containing no multiple of 2 pi as soon as n(pi - pi/r) <= 2 pi.  Hence:
#
#   (A)  n(r-1) <= 2r  =>  NO positive-z endpoint candidate exists at all,
#                          and hte_1 is refuted by parity alone.
#   (B)  n(r-1) >  2r  =>  candidates exist, and each has to be excluded by the
#                          branch condition instead.
#
# At r = 3 the threshold is n <= 3, which covers both r >= 2 pencils in the tree:
# Q = (1-t)^3 (n = 3) and Q = 1 - t (n = 1).  So for those two the refutation
# needs no sweep.  Case (B) starts at n = 4, r = 3, and is checked below --
# there the candidate is genuine and z is POSITIVE, which the earlier r >= 2
# candidates were not, so it is the first case where the branch condition does
# real work.
print()
print("the parity threshold n(r-1) <= 2r, and the first case beyond it")
for r_, n_ in ((3, 1), (3, 3), (3, 4), (2, 3), (4, 2)):
    span = n_ * (PI - PI / r_)
    has = span > 2 * PI
    print(f"   r={r_}, n={n_}: arg-sum range (-{float(span):.4f}, 0), "
          f"positive-z candidate {'possible' if has else 'IMPOSSIBLE (parity)'}")

# case (B): Q = (1-t)^4, r = 3.  n*arg(1 - tau e^{i pi/3}) = -2 pi  =>  arg = -pi/2
# =>  Re(1 - tau e^{i pi/3}) = 0  =>  tau = 2.
r_, n_ = 3, 4
tau_b = mpm.mpf(2)
tp = tau_b * mpm.exp(1j * PI / r_)
Qt = (1 - tp) ** n_
zb = -Qt / tp ** r_
assert abs(zb.imag) < TOL, "candidate z not real"
zb = zb.real
assert zb > 0, f"candidate z not positive: {zb}"
co = [mpm.mpf(1), mpm.mpf(-4) + zb, mpm.mpf(6), mpm.mpf(-4), mpm.mpf(1)]
assert abs(sum(c * tp ** (4 - i) for i, c in enumerate(co))) < mpm.mpf('1e-25'), \
    "t+ is not a zero of the candidate pencil"
rts = sorted(mpm.polyroots(co, maxsteps=500, extraprec=500), key=abs)
assert abs(abs(rts[0]) - tau_b) > mpm.mpf('1e-9'), \
    "the pair IS minimal at n=4, r=3 -- hte_1 would survive there"
print()
print(f"   case (B) first instance, Q = (1-t)^4, r = 3:  tau* = {float(tau_b)}, "
      f"z = {float(zb)} > 0,")
print(f"   t+ is a genuine zero, but the minimum-modulus pair sits at "
      f"|t| = {float(abs(rts[0])):.6f} with")
print(f"   arg {float(mpm.arg(rts[0])):+.6f} != pi/3, so the branch condition excludes it too.")
print()
print("So hte_1 is refuted by PARITY for n(r-1) <= 2r -- both r >= 2 pencils in the tree --")
print("and by the BRANCH CONDITION in the first case beyond that threshold.  What is not")
print("settled is case (B) in general: candidates exist for every large enough n, and only")
print("n = 4, r = 3 has been checked.")

print()
print('ALL PASS: check_joint_witness')
