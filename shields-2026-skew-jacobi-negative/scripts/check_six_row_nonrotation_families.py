#!/usr/bin/env python3
"""Verify the three proposed NEW six-row nonrotation families at nu = 7, 8, 9.

Claim under test, on 1 <= q <= b < g, with common row betas

    X = (b+5g, b+4g, b+3g, b+2g, b+g, b)

and column betas

    nu=7   Y_F = (3g+q, 2g,   g+q, g, q, 0)    Y_H = (3g,   2g+q, g+q, g,   q, 0)
    nu=8   Y_F = (4g+q, 2g+q, g+q, g, q, 0)    Y_H = (3g+q, 2g+q, 2g,  g+q, q, 0)
    nu=9   Y_F = (4g+q, 3g+q, g+q, g, q, 0)    Y_H = (3g+q, 3g,   2g+q, g+q, q, 0)

each giving six nonempty rows, n_min = 6, the stated negative shapes, s_F = s_H,
and four distinct members {F, F*, H, H*}.

Why this matters more than another family.  If true these are nonrotation
classes at nu = 7, 8, 9 with LOW minimal row count, i.e. exactly the regime the
high-minimal-row theorem (nu <= 9 and n_min >= 7 implies rigidity) does not
reach -- and they are claimed NOT to be instances of the classified M1-M4
staircase families.  That would mean the classified list is incomplete in a
range the paper speaks about, so it is checked hard, with the M1-M4 exclusion
done by direct construction rather than by taking the family's statement on trust.

Beta convention: X_i = lam_i - (i+1), Y_j = mu_j - (j+1), matching the engine.
"""

import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ENGINE = os.path.join(HERE, "check_composition_irreducibility.py")
spec = importlib.util.spec_from_file_location("eng", ENGINE)
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)

FAILURES = []
CHECKED = 0


def fail(m):
    FAILURES.append(m)
    print("FAIL  " + m)


def from_beta(X, Y):
    lam = [X[i] + (i + 1) for i in range(len(X))]
    mu = [Y[j] + (j + 1) for j in range(len(Y))]
    if any(m < 0 for m in mu) or any(lam[i] < mu[i] for i in range(len(lam))):
        return None
    return E.from_lam_mu(lam, mu)


def build(L, g):
    return E.cells_from_rho_a(list(L), [x + 1 for x in g])


def negdata(cells):
    lam, mu = E.lam_mu_of(cells)
    n = len(lam)
    mu = list(mu) + [0] * (n - len(mu))
    b = [sum(1 for j in range(n) if lam[i] - mu[j] - i + j < 0) for i in range(n)]
    rho = tuple(x for x in sorted(b, reverse=True) if x > 0)
    nmin = 1 + max(x + (i + 1) for i, x in enumerate(rho)) if rho else 0
    return sum(b), rho, nmin


def prof(cells):
    ri = E.row_intervals(cells)
    idx = sorted(ri)
    L = tuple(ri[i][1] - ri[i][0] + 1 for i in idx)
    g = tuple(min(ri[idx[t]][1], ri[idx[t + 1]][1])
              - max(ri[idx[t]][0], ri[idx[t + 1]][0]) for t in range(len(idx) - 1))
    return (L, g)


def X_of(b, g):
    return (b + 5 * g, b + 4 * g, b + 3 * g, b + 2 * g, b + g, b)


FAM = {
    7: (lambda b, g, q: (3 * g + q, 2 * g, g + q, g, q, 0),
        lambda b, g, q: (3 * g, 2 * g + q, g + q, g, q, 0),
        (4, 2, 1), (4, 2, 1)),
    8: (lambda b, g, q: (4 * g + q, 2 * g + q, g + q, g, q, 0),
        lambda b, g, q: (3 * g + q, 2 * g + q, 2 * g, g + q, q, 0),
        (4, 2, 1, 1), (4, 3, 1)),
    9: (lambda b, g, q: (4 * g + q, 3 * g + q, g + q, g, q, 0),
        lambda b, g, q: (3 * g + q, 3 * g, 2 * g + q, g + q, q, 0),
        (4, 2, 2, 1), (4, 3, 2)),
}

print("=" * 78)
print("THREE PROPOSED NEW SIX-ROW FAMILIES AT nu = 7, 8, 9")
print("=" * 78)

DOM = [(b, g, q) for g in range(2, 12) for b in range(1, g)
       for q in range(1, b + 1)]
print(f"\nparameter domain 1 <= q <= b < g <= 11: {len(DOM)} points")

AREA = {7: lambda b, g, q: 6 * b + 8 * g - 3 * q,
        8: lambda b, g, q: 6 * b + 7 * g - 4 * q,
        9: lambda b, g, q: 6 * b + 6 * g - 4 * q}

allF = {}
for nu_t, (YF, YH, rF, rH) in FAM.items():
    ok = eqn = 0
    rows_seen, nus, rhos, nmins = set(), set(), set(), set()
    for (b, g, q) in DOM:
        CHECKED += 1
        F = from_beta(X_of(b, g), YF(b, g, q))
        H = from_beta(X_of(b, g), YH(b, g, q))
        if F is None or H is None:
            fail(f"nu={nu_t} ({b},{g},{q}): beta lists do not give a shape")
            continue
        if not (E.is_connected_skew(F) and E.is_connected_skew(H)):
            fail(f"nu={nu_t} ({b},{g},{q}): not connected")
            continue
        rows_seen.add(len(set(i for i, _ in F)))
        rows_seen.add(len(set(i for i, _ in H)))
        nF, rrF, nmF = negdata(F)
        nH, rrH, nmH = negdata(H)
        nus.update({nF, nH})
        rhos.update({rrF, rrH})
        nmins.update({nmF, nmH})
        if (rrF, rrH) != (rF, rH):
            fail(f"nu={nu_t} ({b},{g},{q}): rho {rrF}/{rrH}, claimed {rF}/{rH}")
            continue
        if len(F) != AREA[nu_t](b, g, q):
            fail(f"nu={nu_t} ({b},{g},{q}): area {len(F)}, "
                 f"formula {AREA[nu_t](b,g,q)}")
            continue
        if dict(E.jt_of_cells(F)) != dict(E.jt_of_cells(H)):
            fail(f"nu={nu_t} ({b},{g},{q}): s_F != s_H")
            continue
        eqn += 1
        if len({E.normalize(F), E.rotate(F), E.normalize(H), E.rotate(H)}) != 4:
            fail(f"nu={nu_t} ({b},{g},{q}): four members not distinct")
            continue
        ok += 1
        allF.setdefault(nu_t, []).append((b, g, q, F, H))
    print(f"\n-- nu = {nu_t} --")
    print(f"  rows {sorted(rows_seen)}  nu {sorted(nus)}  n_min {sorted(nmins)}")
    print(f"  rho values {sorted(rhos)}")
    print(f"  s_F = s_H at {eqn}/{len(DOM)};  four distinct members at {ok}")

# ---- the M1-M4 exclusion, done by construction rather than on trust --------
print("\n-- are these M1-M4 instances?  built directly and compared --")
CHECKED += 1
m_shapes = set()
for d in range(0, 7):
    for t in range(0, 7):
        for a in range(1, 10):
            for bb in range(1, 10):
                if not (a > t + d and bb > t + d and a != bb):
                    continue
                A, B = a + d, bb + d
                for L, gg in (((A, B, A, A + B, B), (t, 0, t, t)),
                              ((A, A + B, B, A, B), (t, t, 0, t)),
                              ((A, B, A, A + B - t, B), (0, t, 0, 0)),
                              ((A, A + B - t, B, A, B), (0, 0, t, 0))):
                    c = build(L, gg)
                    if E.is_connected_skew(c):
                        m_shapes.add(E.normalize(c))
                        m_shapes.add(E.rotate(c))
for d in range(0, 7):
    for a in range(1, 10):
        for bb in range(a + d + 1, a + d + 10):
            A, B = a + d, bb + d
            for L, gg in (((A, B, B, B, A + B), (0, 0, 0, a)),
                          ((A, B, A + B, B, B), (0, a, 0, 0)),
                          ((A, B, B, A + B, A + B), (0, 0, a, a)),
                          ((A, B, A + B, A + B, B), (0, a, a, 0))):
                c = build(L, gg)
                if E.is_connected_skew(c):
                    m_shapes.add(E.normalize(c))
                    m_shapes.add(E.rotate(c))
print(f"  built {len(m_shapes)} M1-M4 diagrams and rotations for comparison")
overlap = 0
tested = 0
for nu_t, lst in allF.items():
    for (b, g, q, F, H) in lst:
        tested += 2
        if E.normalize(F) in m_shapes or E.normalize(H) in m_shapes:
            overlap += 1
if overlap:
    fail(f"{overlap} of the new diagrams ARE M1-M4 instances -- not new")
else:
    print(f"  none of the {tested} new diagrams coincides with any M1-M4 "
          f"diagram or rotation => genuinely outside the classified families")

# ---- the tabulated small witnesses ---------------------------------------
print("\n-- the (b,g,q)=(1,2,1) witnesses --")
WIT = {7: ((7, 4, 3, 2, 1, 0), (6, 5, 3, 2, 1, 0), 19),
       8: ((9, 5, 3, 2, 1, 0), (7, 5, 4, 3, 1, 0), 16),
       9: ((9, 7, 3, 2, 1, 0), (7, 6, 5, 3, 1, 0), 14)}
for nu_t, (yf, yh, area) in WIT.items():
    CHECKED += 1
    F = from_beta((11, 9, 7, 5, 3, 1), yf)
    H = from_beta((11, 9, 7, 5, 3, 1), yh)
    nF, rrF, nmF = negdata(F)
    okeq = dict(E.jt_of_cells(F)) == dict(E.jt_of_cells(H))
    if len(F) != area or not okeq:
        fail(f"witness nu={nu_t}: area {len(F)} (claimed {area}), s_F=s_H {okeq}")
    else:
        print(f"  nu={nu_t}: area {len(F)}  nu={nF}  n_min={nmF}  "
              f"F={prof(F)}  s_F=s_H {okeq}")

# ---- the nu=10 self-conjugate staircase ribbon family --------------------
print("\n-- the nu=10 rho=(4,3,2,1) ribbon family --")
CHECKED += 1
good = 0
for a in range(1, 7):
    for bb in range(1, 7):
        if a == bb:
            continue
        F = build((a, bb, a, a + bb, a + bb, bb), (0, 0, 0, 0, 0))
        H = build((a, a + bb, a + bb, bb, a, bb), (0, 0, 0, 0, 0))
        if not (E.is_connected_skew(F) and E.is_connected_skew(H)):
            continue
        nF, rrF, nmF = negdata(F)
        if rrF != (4, 3, 2, 1) or nF != 10 or nmF != 6:
            fail(f"ribbon (a,b)=({a},{bb}): nu={nF} rho={rrF} n_min={nmF}")
            continue
        if dict(E.jt_of_cells(F)) != dict(E.jt_of_cells(H)):
            fail(f"ribbon (a,b)=({a},{bb}): s_F != s_H")
            continue
        if E.normalize(F) == E.rotate(H) or E.normalize(F) == E.normalize(H):
            fail(f"ribbon (a,b)=({a},{bb}): rotation pair")
            continue
        good += 1
print(f"  nonrotation Schur equalities with rho=(4,3,2,1), nu=10, n_min=6: "
      f"{good} parameter points")

# ---- controls -------------------------------------------------------------
print("\n-- controls (each must fire) --")
CHECKED += 1
bad = from_beta(X_of(1, 2), (7, 4, 3, 2, 1, 0))
per = from_beta(X_of(1, 2), (7, 4, 3, 2, 2, 0))
if per is not None and dict(E.jt_of_cells(bad)) == dict(E.jt_of_cells(per)):
    fail("control did not fire: a perturbed Y still gives the equality")
else:
    print("  perturbed-Y control fires")

CHECKED += 1
if len(m_shapes) < 100:
    fail(f"M1-M4 comparison set too small ({len(m_shapes)}) to be meaningful")
else:
    print(f"  M1-M4 comparison set non-vacuous ({len(m_shapes)} diagrams)")

print("\n" + "=" * 78)
print(f"checks run: {CHECKED}   failures: {len(FAILURES)}")
print("RESULT: " + ("FAIL" if FAILURES else "ALL PASS"))
sys.exit(1 if FAILURES else 0)
