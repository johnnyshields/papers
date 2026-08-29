"""The pencil `(deg Q, r) = (2,1)`, which the admissible class contains.

Paper: `sec:reduction` (the admissible class), `thm:main`, `eq:ab-def`,
`thm:FT-geometry`.

`thm:main` assumes `Q` nonconstant, `r >= 1` and `max{deg Q, r} > 1`, so at
`r = 1` it admits `deg Q = 2`; the text says so outright -- "at `r = 1` one has
`deg Q >= 2` and the negative zero `t_b`".  The only case the paper excludes is
`deg Q = r = 1`.

`Forgacs2017RationalDenominator` Props. 1--2 carry their own exclusion
`(deg Q, r) = (2,1)`, which is exactly this pencil, so anything routed through them
inherits it -- which is why the four dominance cells of `DominanceSupplyClosure`
carry `3 <= n` at `r = 1` and cover the admissible class minus this one point.

**That is not a gap.**  The paper handles the case in `rem:quadratic-case` and the
tree proves it outright by a different route -- `QuadraticCase` for the geometry
and `QuadraticDefect` for the defect bound, through Favard orthogonality rather
than through principal-pair dominance.  So this pencil is covered; it simply does
not travel the dominance partition, by design.

What this script checks is the mathematical content the two routes share, derived
from the pencil rather than read off the manuscript:

  C1  the pencil is admissible by the paper's own definition;
  C2  both critical points exist, so `t_a`, `t_b` and the interval `I_{Q,r}` do;
  C3  `t_a` lies strictly inside the first gap, as at every other admissible pencil;
  C4  the pencil has degree 2, so the principal pair is ALL of its zeros and the
      set of "remaining" zeros the separation statements speak about is EMPTY --
      which is why the case is degenerate rather than hard;
  C5  the branch exists across the whole arc and its radius is well defined.
"""

import mpmath as mp

mp.mp.dps = 40

A = [mp.mpf(1), mp.mpf(2)]
C, R, N = mp.mpf(1), 1, 2

# --- C1: admissible by the paper's definition. -----------------------------
deg_Q = N
assert deg_Q >= 1, "C1 Q is constant"
assert max(deg_Q, R) > 1, f"C1 max(deg Q, r) = {max(deg_Q, R)} is not > 1"
assert not (deg_Q == 1 and R == 1), "C1 this is the paper's one excluded case"
print(f"C1     deg Q = {deg_Q}, r = {R}: nonconstant, max = {max(deg_Q, R)} > 1, "
      "and not the excluded deg Q = r = 1")


def Qreal(s):
    out = C
    for ak in A:
        out *= ak - s
    return out


def Ereal(s):
    """E = t Q' - r Q, by exact differentiation of the product."""
    dQ = C * sum(-mp.mpf(1) * mp.fprod([A[j] - s for j in range(len(A)) if j != k])
                 for k in range(len(A)))
    return s * dQ - R * Qreal(s)


# --- C2/C3: both critical points, and t_a inside the first gap. ------------
# E(t) = t^2 - 2 at a = (1,2), c = 1, r = 1.
for probe in [mp.mpf("0.5"), mp.mpf("1.5"), mp.mpf("-1.5")]:
    assert abs(Ereal(probe) - (probe ** 2 - 2)) < mp.mpf("1e-30"), "C2 E is not t^2 - 2"
ta = mp.findroot(Ereal, (mp.mpf(1) + mp.mpf("1e-9"), mp.mpf(2) - mp.mpf("1e-9")),
                 solver="bisect", tol=mp.mpf("1e-35"), maxsteps=400)
tb = mp.findroot(Ereal, (mp.mpf(-5), -mp.mpf("1e-9")), solver="bisect",
                 tol=mp.mpf("1e-35"), maxsteps=400)
assert ta > 0 and tb < 0, f"C2 critical points {ta}, {tb} are not of both signs"
assert abs(ta - mp.sqrt(2)) < mp.mpf("1e-25"), f"C2 t_a = {ta}, expected sqrt 2"
assert abs(tb + mp.sqrt(2)) < mp.mpf("1e-25"), f"C2 t_b = {tb}, expected -sqrt 2"
g = lambda s: -Qreal(s) / s ** R
lo, hi = g(ta), g(tb)
assert lo < hi, f"C2 the interval ({lo}, {hi}) is empty"
assert abs(lo - (3 - 2 * mp.sqrt(2))) < mp.mpf("1e-25"), "C2 a is not 3 - 2 sqrt 2"
assert abs(hi - (3 + 2 * mp.sqrt(2))) < mp.mpf("1e-25"), "C2 b is not 3 + 2 sqrt 2"
print(f"C2     t_a = {mp.nstr(ta, 12)}, t_b = {mp.nstr(tb, 12)}; "
      f"I = ({mp.nstr(lo, 10)}, {mp.nstr(hi, 10)}), nonempty")
assert A[0] < ta < A[1], f"C3 t_a = {ta} is not inside the first gap"
print(f"C3     a_1 = {A[0]} < t_a < a_2 = {A[1]}: inside the first gap, as everywhere else")

# --- C4: the principal pair is every zero of the pencil. -------------------
d = max(deg_Q, R)
assert d == 2, f"C4 deg_t D = {d}"
print(f"C4     deg_t D = {d}, so the principal pair t_+ and t_- are ALL of its zeros: "
      "the set of remaining zeros the separation statements quantify over is EMPTY")

# --- C5: the branch exists across the arc. ---------------------------------
def branch_sum(tau, theta):
    gam = tau * mp.exp(mp.mpc(0, 1) * theta)
    return sum(mp.arg(gam - ak) for ak in A)


def ft_tau(theta):
    target = R * theta + (N - 1) * mp.pi
    f = lambda t: branch_sum(t, theta) - target
    lo_, hi_ = mp.mpf("1e-12"), mp.mpf(1)
    while f(hi_) > 0:
        hi_ *= 2
        assert hi_ < mp.mpf("1e6"), "C5 no bracket above"
    while f(lo_) < 0:
        lo_ /= 2
        assert lo_ > mp.mpf("1e-30"), "C5 no bracket below"
    return mp.findroot(f, (lo_, hi_), solver="bisect", tol=mp.mpf("1e-30"), maxsteps=400)


sq = mp.sqrt(A[0] * A[1])
ssum = A[0] + A[1]
taus = []
for k in range(1, 20):
    th = mp.pi * mp.mpf(k) / 20
    t = ft_tau(th)
    assert t > 0, f"C5 tau({th}) = {t} is not positive"
    taus.append((th, t))
# tau is not merely well defined here -- it is CONSTANT.
for th, t in taus:
    assert abs(t - sq) < mp.mpf("1e-25"), f"C5 tau({th}) = {t}, expected sqrt(a1 a2) = {sq}"
print(f"C5     tau is CONSTANT at sqrt(a_1 a_2) = {mp.nstr(sq, 12)} across the whole arc, "
      f"to {mp.nstr(max(abs(t - sq) for _, t in taus), 3)}")

# --- C6: and the branch is explicit, which is why the case is degenerate. --
# E = c(t^2 - a_1 a_2) always at deg Q = 2, r = 1, so t_a = -t_b = sqrt(a_1 a_2);
# the branch is the circle of that radius and z(theta) = s - 2 sqrt(p) cos theta.
for probe in [mp.mpf("0.7"), mp.mpf("1.9"), mp.mpf("-2.3")]:
    assert abs(Ereal(probe) - C * (probe ** 2 - A[0] * A[1])) < mp.mpf("1e-30"), \
        "C6 E is not c(t^2 - a_1 a_2)"
assert abs(ta + tb) < mp.mpf("1e-25"), f"C6 t_a + t_b = {ta + tb} is not 0"
zs = []
for th, t in taus:
    gam = t * mp.exp(mp.mpc(0, 1) * th)
    z = C * (ssum - 2 * sq * mp.cos(th))
    # gamma really is a root of the pencil at that real z
    assert abs(Qreal(gam) + z * gam ** R) < mp.mpf("1e-24"), \
        f"C6 gamma({th}) is not a root of the pencil at z = {z}"
    zs.append(z)
for k in range(1, len(zs)):
    assert zs[k] > zs[k - 1], "C6 z is not strictly increasing"
assert abs(zs[0] - lo) < mp.mpf("0.2") and abs(zs[-1] - hi) < mp.mpf("0.2"), \
    "C6 z does not sweep the interval"
print(f"C6     E = c(t^2 - a_1 a_2), so t_a = -t_b always at this pencil; the branch is "
      "the CIRCLE of radius sqrt(a_1 a_2)")
print(f"       and z(theta) = c((a_1 + a_2) - 2 sqrt(a_1 a_2) cos(theta)) sweeps "
      f"({mp.nstr(zs[0], 8)}, {mp.nstr(zs[-1], 8)}) increasing, into I")
print("       the branch here is explicit, not hard: the exclusion is the cited "
      "proposition's, not the geometry's")

# --- C7: the closed form is not an artifact of one pencil. -----------------
# The C1-C6 run fixes a = (1,2), c = 1, and the claims above are algebraic, so
# they are re-run across a spread of pencils rather than trusted from one.
for cc, a1, a2 in [(mp.mpf(1), mp.mpf(1), mp.mpf(5)), (mp.mpf(3), mp.mpf("0.4"), mp.mpf(2)),
                   (mp.mpf("0.25"), mp.mpf(2), mp.mpf("2.5")), (mp.mpf(7), mp.mpf("0.1"),
                    mp.mpf(9))]:
    AA, sq2, ss = [a1, a2], mp.sqrt(a1 * a2), a1 + a2

    def QQ(x, AA=AA, cc=cc):
        return cc * (AA[0] - x) * (AA[1] - x)

    def EE(x, AA=AA, cc=cc):
        dQ = cc * (-(AA[1] - x) - (AA[0] - x))
        return x * dQ - QQ(x)

    for probe in [mp.mpf("0.3"), mp.mpf("3.1"), mp.mpf("-1.7")]:
        assert abs(EE(probe) - cc * (probe ** 2 - a1 * a2)) < mp.mpf("1e-28"), \
            f"C7 E != c(t^2 - a1 a2) at c={cc}, a={AA}"
    assert a1 <= sq2 <= a2 or a2 <= sq2 <= a1, f"C7 sqrt(a1 a2) outside the gap at {AA}"
    for k in range(1, 12):
        th = mp.pi * mp.mpf(k) / 12
        gam = sq2 * mp.exp(mp.mpc(0, 1) * th)
        z = cc * (ss - 2 * sq2 * mp.cos(th))
        assert abs(mp.im(z)) < mp.mpf("1e-30"), "C7 z is not real"
        assert abs(QQ(gam) + z * gam) < mp.mpf("1e-24"), \
            f"C7 the circle of radius sqrt(a1 a2) is not the branch at c={cc}, a={AA}"
print("C7     the closed form holds across four further pencils, asymmetric and with "
      "c != 1: the degeneracy is the pencil shape, not the example")

print("check_dominance_cell_coverage.py: PASS")
