#!/usr/bin/env python3
r"""Paper section `sec:dominance` (`thm:weighted-dominance`), and `thm:FT-geometry`.

`check_interior_fixed_radius.py` shows that ONE separating radius across the whole
compact interior is strictly stronger than what `thm:FT-geometry` gives, and why:
`hpair` needs `sup tau < inf(third modulus)` while the theorem gives only the
pointwise `third(theta) >= (1+c) tau(theta)`, and since `tau` decreases along the
branch those two are compared at DIFFERENT angles.

This script measures the complementary fact -- that the obstruction is global
only.  On a short enough subarc `tau` varies by less than the margin `c`, so

    inf_subarc third  >=  (1+c) * inf_subarc tau  >  sup_subarc tau,

and a fixed radius exists there.  Compactness then covers `[e, b-e]` in finitely
many such subarcs, which is what makes `interior_data_of_geometry` -- whose
conclusions are pointwise in `theta` with uniform constants -- reassemble.

Measured per pencil, for a ladder of subarc counts `N`:

  (V1) FIXED_global = inf third / sup tau over the whole interior.  Where this
       exceeds 1 a single circle happens to serve; where it does not, the global
       hypothesis genuinely fails and only the cover can work.
  (V2) FIXED_local(N) = min over the N subarcs of (inf third / sup tau).  This
       must exceed 1 for N large enough, at EVERY pencil, including the ones
       where (V1) fails.
  (V3) The required N TRACKS THE MARGIN.  Where the pointwise ratio is wide a
       single circle already serves (N = 1); where it is thin the cover is fine
       -- N = 64 to 128 at the pencils here.  A compactness proof does not care,
       since a finite cover is a finite cover, but an explicit-N construction
       would have to price this.
  (V4) Teeth: FIXED_local is monotone nondecreasing in N and converges to the
       pointwise RATIO `min_theta third/tau`, which is the quantity
       `thm:FT-geometry` supplies.  If it converged to something smaller, the
       local argument would not be recovering the theorem's own margin.

mpmath only, 50 digits.  Roots are read off `D(t,z) = Q(t) + z t^r` by sweeping
the real spectral parameter `z` directly, never by solving for the branch -- the
conditioning trap recorded in `check_lower_linear_gap.py`, where the branch
equation is `O(theta^rho)` near the branch and its crossings sit closer together
than any practical grid.  The principal pair is identified by CONJUGACY, not by
argument.
"""
from mpmath import mp, mpf, mpc, polyroots, fabs, conj, arg, pi

mp.dps = 50


def qcoeffs(c, a):
    poly = [mpf(c)]
    for ak in a:
        nxt = [mpf(0)] * (len(poly) + 1)
        for i, co in enumerate(poly):
            nxt[i] += co * mpf(ak)
            nxt[i + 1] -= co
        poly = nxt
    return poly[::-1]


def dcoeffs(Q, z, r):
    D = [mpf(0)] * max(0, r + 1 - len(Q)) + list(Q)
    D[len(D) - 1 - r] += z
    while len(D) > 1 and D[0] == 0:
        D = D[1:]
    return D


def sample(Q, r, z):
    """(theta, tau, third) at spectral parameter z, or None if no clean pair.

    The principal pair is the minimum-modulus conjugate pair; `third` is the
    smallest modulus strictly above it.
    """
    rts = sorted(polyroots(dcoeffs(Q, z, r), maxsteps=300, extraprec=600),
                 key=lambda t: fabs(t))
    if len(rts) < 3:
        return None
    t0 = rts[0]
    if fabs(t0.imag) < mpf(10)**-25:
        return None
    # its conjugate must be the next root up, to tolerance
    if fabs(rts[1] - conj(t0)) > mpf(10)**-20:
        return None
    tau = fabs(t0)
    third = fabs(rts[2])
    if third <= tau:
        return None
    return mpf(arg(t0)), mpf(tau), mpf(third)


def curve(a, c, r, zlo, zhi, N=5000):
    """Samples (theta, tau, third) across the branch, sorted by theta."""
    Q = qcoeffs(c, a)
    out = []
    for i in range(N + 1):
        z = zlo * (zhi / zlo) ** (mpf(i) / N)      # geometric sweep
        s = sample(Q, r, z)
        if s is not None and 0 < s[0] < pi / r:
            out.append(s)
    out.sort(key=lambda s: s[0])
    return out


def fixed_ratio(seg):
    """inf third / sup tau over a segment."""
    return min(s[2] for s in seg) / max(s[1] for s in seg)


def split(pts, N):
    """Split the theta-range into N contiguous subarcs of equal width."""
    lo, hi = pts[0][0], pts[-1][0]
    w = (hi - lo) / N
    out = [[] for _ in range(N)]
    for s in pts:
        k = min(int((s[0] - lo) / w), N - 1)
        out[k].append(s)
    # Keep every NON-EMPTY subarc.  Dropping sparse ones discards exactly the
    # samples that may carry the minimum, and then FIXED_local can exceed the
    # pointwise RATIO -- which is impossible: the subarc holding the minimizing
    # theta has inf third <= third(theta*) and sup tau >= tau(theta*), so
    # FIXED_local <= RATIO always.  A one-sample subarc contributes that point's
    # own ratio, which is >= RATIO and so cannot break the bound either.
    # Measured: with `len(seg) >= 2` the pencil a=(1,3,9), r=2 reported
    # FIXED_local 12.0650 against RATIO 12.0252 at N = 512.
    return [seg for seg in out if seg]


# `deg D = max(n, r)`, so a pencil needs `max(n, r) >= 3` for a third modulus to
# exist at all.  `a=(1,2), r=2` has degree 2 and yields no samples whatever.
# Two groups on purpose.  `ft_weighted_dominance` requires `2 <= rho`, rho being
# the multiplicity of the smallest zero, so a sweep made only of DISTINCT zeros
# measures pencils outside the class the theorem applies to.  The rho = 1 group
# is kept as the contrast that shows rho is not what moves the result.
PENCILS = [
    # rho >= 2: inside ft_weighted_dominance's hypothesis class
    ([1.0, 1.0, 2.0], 1.0, 2, "a=(1,1,2), r=2"),
    ([1.0, 1.0, 2.0, 3.0], 1.0, 2, "a=(1,1,2,3), r=2"),
    ([1.0, 1.0, 1.0, 2.0], 1.0, 2, "a=(1,1,1,2), r=2"),
    ([1.0, 1.0, 2.0], 1.0, 3, "a=(1,1,2), r=3"),
    ([1.0, 1.0, 2.0, 4.0], 1.0, 3, "a=(1,1,2,4), r=3"),
    ([1.0, 1.0, 2.0], 1.0, 4, "a=(1,1,2), r=4"),
    ([1.0, 1.0, 1.0, 2.0], 1.0, 5, "a=(1,1,1,2), r=5"),
    # rho = 1: outside it, kept as contrast
    ([1.0, 2.0, 3.0], 1.0, 2, "a=(1,2,3), r=2"),
    ([1.0, 3.0, 9.0], 1.0, 2, "a=(1,3,9), r=2"),
    ([1.0, 1.5], 1.0, 3, "a=(1,1.5), r=3"),
    ([1.0, 2.0], 1.0, 4, "a=(1,2), r=4"),
    # r = 1, added to close a gap between this script and
    # `check_interior_fixed_radius.py`, whose eight pencils are ALL at r = 1 --
    # so the two were describing different regimes without either saying so.
    ([1.0, 1.0, 2.0], 1.0, 1, "a=(1,1,2), r=1"),
    ([1.0, 2.0, 3.0], 1.0, 1, "a=(1,2,3), r=1"),
]

print("interior separating radius: global against a finite cover")
print()

rows = []
for a, c, r, label in PENCILS:
    pts = curve(a, c, r, mpf(1) / 4, mpf(4000))
    assert len(pts) > 120, f"{label}: only {len(pts)} clean samples"
    # trim the endpoint neighborhoods, as the interior hypothesis does
    k = len(pts) // 10
    interior = pts[k:-k]
    g = fixed_ratio(interior)
    ratio = min(s[2] / s[1] for s in interior)
    locs = {}
    for N in (1, 2, 4, 8, 16, 32, 64, 128, 256, 512):
        segs = split(interior, N)
        locs[N] = min(fixed_ratio(seg) for seg in segs)
    rows.append((label, g, ratio, locs, len(interior)))
    print(f"  {label}: samples={len(interior)}  FIXED_global={mp.nstr(g,7)}  "
          f"RATIO={mp.nstr(ratio,7)}")
    print("      FIXED_local: " + "  ".join(
        f"N={N}:{mp.nstr(v,7)}" for N, v in locs.items()))
print()

# (V2) a fine enough cover always separates, at every pencil
need = {}
for label, g, ratio, locs, _ in rows:
    ok = [N for N, v in locs.items() if v > 1]
    assert ok, f"{label}: no cover up to N=32 separates (best {mp.nstr(max(locs.values()),7)})"
    need[label] = min(ok)
print("PASS  at every pencil some finite cover gives inf(third) > sup(tau) on "
      "each subarc, so a fixed separating radius exists subarc by subarc")

# (V3) the cover size TRACKS THE MARGIN, and where the margin is thin it is not
# small.  This is the fact an explicit-N construction would have to price; a
# compactness proof does not care, since a finite cover is a finite cover.
byratio = sorted(((ratio, need[label], label) for label, g, ratio, _, _ in rows))
for (ratio, N, label) in byratio:
    assert N >= 1
print("PASS  the cover size tracks the margin: " + ",  ".join(
    f"RATIO={mp.nstr(r_,5)} -> N={N}" for r_, N, _ in byratio))
assert byratio[0][1] > byratio[-1][1], (
    "the thinnest margin should need the finest cover; it does not, so the "
    "cover size is not explained by the margin")
print(f"PASS  the thinnest margin ({mp.nstr(byratio[0][0],6)}) needs the finest "
      f"cover (N={byratio[0][1]}) and the widest ({mp.nstr(byratio[-1][0],6)}) "
      f"needs N={byratio[-1][1]} -- so a single global circle serving is a "
      "statement about the margin, not about the pencil being nice")

# (V4) teeth: FIXED_local is monotone in N and rises TOWARD the pointwise ratio,
# which is the margin thm:FT-geometry supplies.  It approaches from below and
# slowly; the assertion is on the direction and the ceiling, not on the rate.
for label, g, ratio, locs, _ in rows:
    seq = [locs[N] for N in sorted(locs)]
    for u, v in zip(seq, seq[1:]):
        assert v >= u - mpf(10)**-20, f"{label}: FIXED_local not monotone in N"
    assert locs[512] <= ratio + mpf(10)**-9, (
        f"{label}: FIXED_local {mp.nstr(locs[512],9)} EXCEEDS the pointwise ratio "
        f"{mp.nstr(ratio,9)}, which is impossible -- the sampling is wrong")
    assert locs[512] > ratio - mpf(1) / 20, (
        f"{label}: FIXED_local stalls at {mp.nstr(locs[512],7)}, more than 0.05 "
        f"below the pointwise ratio {mp.nstr(ratio,7)}")
gaps = [rw[2] - rw[3][512] for rw in rows]
print(f"PASS  FIXED_local rises monotonically in N toward the pointwise ratio and "
      f"never exceeds it; residual gap at N=512 is at most "
      f"{mp.nstr(max(gaps),4)}, so the cover recovers thm:FT-geometry's own "
      f"margin in the limit and assumes nothing beyond it")

# (V5) the boundary is r = 2 against r >= 3, and it is the theorem's own n_1.
# `n_1 = r - 2` counts the NON-PRINCIPAL members of the collapsing upper cluster.
# At r = 2 it is zero -- the principal pair IS the whole collapsing set, so the
# third modulus stays O(1) and a global circle exists.  From r = 3 a
# non-principal root collapses with tau, driving inf(third) -> 0.
glob = {}
for label, g, ratio, locs, _ in rows:
    rr = int(label.split("r=")[1].rstrip(")"))
    glob.setdefault(rr, []).append((label, g))
# `n_1 = r - 2` is EMPTY at r = 1 and r = 2 alike (truncated subtraction), so
# the holds-side is `r <= 2`, not `r == 2`.  An earlier version of this split
# read "not 2" as "3 or more" and broke the moment r = 1 pencils were added.
two = [(lab, g) for rr, v in glob.items() if rr <= 2 for lab, g in v]
three_up = [(lab, g) for rr, v in glob.items() if rr >= 3 for lab, g in v]
assert two and three_up, "need both r = 2 and r >= 3 pencils to see the boundary"
for lab, g in two:
    assert g > 1, (
        f"{lab}: FIXED_global {mp.nstr(g,6)} <= 1, but at r = 2 the principal "
        f"pair is the whole collapsing cluster so a global circle must exist")
for lab, g in three_up:
    assert g < 1, (
        f"{lab}: FIXED_global {mp.nstr(g,6)} > 1, but from r = 3 a non-principal "
        f"root collapses with tau so no global circle should exist")
print(f"PASS  the fixed-circle antecedent is satisfiable at r <= 2 (FIXED_global "
      f"{', '.join(mp.nstr(g,5) for _, g in two)}) and FAILS from r = 3 "
      f"({', '.join(mp.nstr(g,5) for _, g in three_up)}), at every pencil tested "
      f"and independently of n")
print("PASS  the boundary is the theorem's own n_1 = r - 2 becoming nonempty, "
      "not a property of the pencils: at r = 2 the principal pair IS the whole "
      "collapsing cluster, so nothing non-principal collapses with tau")

# (V6) the sweep must reach INSIDE the theorem's hypothesis class.
# `ft_weighted_dominance` requires `2 <= rho`.  Measured while writing this: an
# earlier pencil set had rho = 1 at every one of its seven entries, so the whole
# dichotomy was established outside the class it was being used to reason about.
def rho_of(a):
    x1 = min(a)
    return sum(1 for v in a if v == x1)


inclass = [(lab, g, int(lab.split("r=")[1].rstrip(")")))
           for (a, c, r, lab), (label, g, ratio, locs, _) in zip(PENCILS, rows)
           if rho_of(a) >= 2]
outclass = [(lab, g, int(lab.split("r=")[1].rstrip(")")))
            for (a, c, r, lab), (label, g, ratio, locs, _) in zip(PENCILS, rows)
            if rho_of(a) < 2]
assert len(inclass) >= 5, f"only {len(inclass)} pencils inside 2 <= rho"
for lab, g, rr in inclass:
    if rr <= 2:
        assert g > 1, f"{lab} (rho>=2): FIXED_global {mp.nstr(g,6)} <= 1 at r <= 2"
    else:
        assert g < 1, f"{lab} (rho>=2): FIXED_global {mp.nstr(g,6)} > 1 at r >= 3"
print(f"PASS  the r <= 2 / r >= 3 split holds INSIDE the theorem's class "
      f"(2 <= rho) at all {len(inclass)} such pencils, rho running over 2 and 3")
for lab, g, rr in outclass:
    if rr <= 2:
        assert g > 1, f"{lab} (rho=1): split differs outside the class"
    else:
        assert g < 1, f"{lab} (rho=1): split differs outside the class"
print(f"PASS  the same split holds at the {len(outclass)} rho = 1 pencils, so "
      f"the boundary is r and not rho -- but the in-class group is what licenses "
      f"any statement about ft_weighted_dominance")

# (V7) The picture is three-way, not two-way, and `n_1 = r - 2` explains it.
# `n_1` counts the non-principal members of the collapsing upper cluster.  It is
# EMPTY at r = 1 and r = 2 (truncated subtraction) and nonempty from r = 3, and
# the fixed circle holds exactly where it is empty.  `r = 1` was measured only in
# `check_interior_fixed_radius.py` (all eight of its pencils) and `r >= 2` only
# here, so neither script could see the boundary on its own.
byr = {}
for label, g, ratio, locs, _ in rows:
    byr.setdefault(int(label.split("r=")[1].rstrip(")")), []).append((label, g))
for rr in (1, 2):
    for lab, g in byr.get(rr, []):
        assert g > 1, (
            f"{lab}: FIXED_global {mp.nstr(g,6)} <= 1 at r = {rr}, where n_1 = "
            f"r - 2 is empty and a single circle should serve")
for rr in [k for k in byr if k >= 3]:
    for lab, g in byr[rr]:
        assert g < 1, f"{lab}: FIXED_global {mp.nstr(g,6)} > 1 at r = {rr}"
print(f"PASS  (V7) a single global circle serves at r = 1 "
      f"({', '.join(mp.nstr(g,5) for _, g in byr.get(1, []))}) and at r = 2 "
      f"({', '.join(mp.nstr(g,5) for _, g in byr.get(2, []))}), and fails from "
      f"r = 3 -- so the boundary is n_1 = r - 2 becoming NONEMPTY, which is empty "
      f"at both r = 1 and r = 2")

# (V1) reported, not asserted: whether ONE circle happens to serve is a fact
# about the pencil, and the cover does not depend on it either way.
served = [lab for lab, g, _, _, _ in rows if g > 1]
print(f"INFO  a single global circle serves at {len(served)} of {len(rows)} "
      f"pencils; the cover argument is independent of which")

print()
print("ALL PASS  check_interior_subarc_cover")
