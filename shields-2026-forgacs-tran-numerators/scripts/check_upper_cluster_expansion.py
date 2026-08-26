#!/usr/bin/env python3
r"""Paper section `sec:dominance`, `thm:weighted-dominance`; `eq:upper-residue-ratio`.

`weighted_dominance_of_branch`'s `hexp1` claims, for each NONPRINCIPAL member of
the upper cluster,

    | |zeta_j(delta)| - (1 + c_j delta) | <= C delta^2,
    c_j = (cos(pi/r) - Re omega_j) / sin(pi/r),   omega_j^r = -1,

with zeta_j = g_1(b - delta)_j / tau(b - delta) and b = pi/r.  That binder has
carried a wrong coefficient twice, so the number is checked here at the real
objects before anything is built against it.

The check runs over a FAMILY of pencils, and that is the point rather than
thoroughness.  |zeta_j| - 1 is of order tau, not of order delta, so the
coefficient is only reachable through the tau-rate -- and the tau-rate is NOT
pencil-free: it carries S = sum 1/a_k.  A version of this check at the single
pencil Q(t) = 1 - t, where S = 1, cannot see that factor at all, and reading its
figure as the general rate gives a constant that is wrong at every other pencil.

  (U5) The coefficient IS pencil-free: (|zeta_j| - 1)/delta converges to
       (cos(pi/r) - Re omega_j)/sin(pi/r) over pencils with S from 1 to 2.25,
       at r = 3 (one nonprincipal member) and r = 4 (two).
  (U6) The tau-rate is NOT: tau(b - delta)/delta -> r/(sin(pi/r) S).  Asserted
       in both directions -- the S-carrying form holds, and the S-free form
       r/sin(pi/r) FAILS wherever S != 1, so the factor cannot be dropped again.
  (U7) The two are consistent exactly because the S cancels: c_j comes out of
       (tau/delta)(S/r)(cos(pi/r) - Re omega_j), so a pencil-free coefficient
       and an S-carrying rate are the same statement.
  (U8) The principal pair carries |zeta| = 1 EXACTLY, so `hgmem1` is what
       excludes it, not the coefficient -- the two agree rather than compete.

Pencil range matters here and not only for coverage.  `Q(t) = 1 - t` has a single
root, so n = 1, and `FTBranchUpper.exists_bound_ftTau_upper` requires n >= 2 --
a chain routed through the upper tau-rate is not exercised at all by that pencil.
Four of the five below have n >= 2 and they are what carries every assertion.
"""

import mpmath as mp

mp.mp.dps = 80
PASSES = 0


def ok(msg):
    global PASSES
    PASSES += 1
    print(f'PASS  {msg}')


def branch_data(r, z, a, c):
    """(delta, tau, principal pair, nonprincipal members) for Q = c prod(a_k - t)."""
    co = [mp.mpf(c)]
    for ak in a:
        nxt = [mp.mpf(0)] * (len(co) + 1)
        for i, p in enumerate(co):
            nxt[i] += -p
            nxt[i + 1] += mp.mpf(ak) * p
        co = nxt
    deg = max(len(co) - 1, r)
    full = [mp.mpf(0)] * (deg + 1)
    for i, p in enumerate(co):
        full[deg - (len(co) - 1 - i)] += p
    full[deg - r] += mp.mpf(z)
    rts = mp.polyroots(full, maxsteps=30000, extraprec=4000)
    # exactly r roots run into the origin; a pencil with deg Q > r keeps the rest away
    rts = sorted(rts, key=lambda t: abs(t))[:r]
    tau = abs(rts[0])
    pair = [t for t in rts if abs(abs(t) - tau) < mp.mpf('1e-30') * tau]
    tp = min(pair, key=lambda t: mp.im(t))
    theta = -mp.atan2(mp.im(tp), mp.re(tp))
    delta = mp.pi / r - theta
    rest = [t for t in rts if all(abs(t - p) > mp.mpf('1e-25') for p in pair)]
    return delta, tau, pair, rest


def claimed(r, zeta):
    omega = zeta / abs(zeta)
    return (mp.cos(mp.pi / r) - mp.re(omega)) / mp.sin(mp.pi / r)


# `[1]` has n = 1, which is OUTSIDE `FTBranchUpper.exists_bound_ftTau_upper`'s
# `hn2 : 2 <= n` -- so it is kept as the case where S = 1 makes the tau-rate's
# factor invisible, and never as the carrier of a claim.  Every assertion below
# loops over all five and fails per pencil, and the guard after this list stops a
# later trim from leaving only the n = 1 case behind.
PENCILS = [([1], 1, 3), ([1, 2, 3], 1, 3), ([1, 2], 1, 3),
           ([1, 2, 3], 1, 4), ([mp.mpf('0.5'), 4], 2, 3)]

INSIDE = [p for p in PENCILS if len(p[0]) >= 2]
assert len(INSIDE) >= 3, (
    "the sweep must carry at least three pencils with n >= 2: a chain routed "
    "through the upper tau-rate is not tested at all by the n = 1 case")


# ----------------------------------------------------------------- (U5), (U8)

print("--- the coefficient, over pencils")
for a, c, r in PENCILS:
    S = sum(1 / mp.mpf(ak) for ak in a)
    prev = None
    for k in (25, 35, 45, 55):
        delta, tau, pair, rest = branch_data(r, mp.mpf(2) ** k, a, c)
        assert len(rest) == r - 2, f"expected {r - 2} nonprincipal members, got {len(rest)}"
        err = max(abs((abs(t / tau) - 1) / delta - claimed(r, t / tau)) for t in rest)
        assert prev is None or err < prev, (
            f"(U5) a={a} r={r}: coefficient not converging: {prev} -> {err}")
        prev = err
    print(f"      a={a} c={c} r={r}  S={mp.nstr(S, 6):<9s} "
          f"(|zeta|-1)/delta = {mp.nstr((abs(rest[0] / tau) - 1) / delta, 9):<12s} "
          f"claimed = {mp.nstr(claimed(r, rest[0] / tau), 9)}")
    # convergence is slow and slower as r grows, so the substantive assertion is the
    # monotone one across the whole k sweep; this is a backstop, not the evidence
    assert prev < mp.mpf('5e-4'), f"(U5) a={a} r={r}: residual {prev}"
    for p in pair:
        assert abs(abs(p / tau) - 1) < mp.mpf('1e-40'), "principal pair not unimodular"
ok("(U5) (|zeta_j|-1)/delta -> (cos(pi/r) - Re omega_j)/sin(pi/r) at every pencil: "
   "the coefficient is pencil-free, over S from 1 to 2.25 and r = 3, 4")
ok("(U8) both members of the principal pair carry |zeta| = 1 exactly, so `hgmem1` "
   "excludes them and the coefficient does not have to")


# ----------------------------------------------------------------- (U6), (U7)

print("--- the tau-rate, which is NOT pencil-free")
sfree_failures = 0
for a, c, r in PENCILS:
    S = sum(1 / mp.mpf(ak) for ak in a)
    target = r / (mp.sin(mp.pi / r) * S)
    sfree = r / mp.sin(mp.pi / r)
    prev = None
    for k in (25, 35, 45, 55):
        delta, tau, _, _ = branch_data(r, mp.mpf(2) ** k, a, c)
        err = abs(tau / delta - target)
        assert prev is None or err < prev, (
            f"(U6) a={a} r={r}: tau/delta not converging to r/(sin(pi/r) S)")
        prev = err
    print(f"      a={a} c={c} r={r}  S={mp.nstr(S, 6):<9s} "
          f"tau/delta = {mp.nstr(tau / delta, 10):<14s} "
          f"r/(sin S) = {mp.nstr(target, 10):<14s} r/sin = {mp.nstr(sfree, 10)}")
    assert prev < mp.mpf('1e-4') * target, (
        f"(U6) a={a} r={r}: relative residual {prev / target}")
    if abs(S - 1) > mp.mpf('1e-20'):
        assert abs(tau / delta - sfree) > mp.mpf('0.3') * target, (
            f"(U6) a={a} r={r}: the S-free form is NOT excluded -- guard is vacuous")
        sfree_failures += 1
assert sfree_failures >= 3, "(U6) too few pencils with S != 1 to pin the S-dependence"
ok("(U6) tau(b - delta)/delta -> r/(sin(pi/r) S) with S = sum 1/a_k, at every pencil")
ok(f"(U6) and the S-free form r/sin(pi/r) is REFUTED at {sfree_failures} pencils with "
   "S != 1, so the factor cannot be dropped again by reading a single pencil")

# c_j = (tau/delta)(S/r)(cos(pi/r) - Re omega_j) -- the S cancels
for a, c, r in PENCILS:
    S = sum(1 / mp.mpf(ak) for ak in a)
    delta, tau, _, rest = branch_data(r, mp.mpf(2) ** 55, a, c)
    for t in rest:
        zeta = t / tau
        via_rate = (tau / delta) * (S / r) * (mp.cos(mp.pi / r) - mp.re(zeta / abs(zeta)))
        assert abs(via_rate - claimed(r, zeta)) < mp.mpf('1e-4'), (
            f"(U7) a={a} r={r}: the S does not cancel: {via_rate} vs {claimed(r, zeta)}")
ok("(U7) c_j = (tau/delta)(S/r)(cos(pi/r) - Re omega_j) reproduces the pencil-free "
   "coefficient at every pencil: the S in the rate is exactly what cancels")

print()
print(f"{PASSES} checks")
print("ALL PASS: check_upper_cluster_expansion")
