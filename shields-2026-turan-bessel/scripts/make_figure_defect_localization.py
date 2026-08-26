#!/usr/bin/env python3
"""Paper section `subsec:finite-defect` (Finite-defect localization), subsec:finite-defect: the figure
fig:defect-localization.

The figure asserts a structural claim, not a numerical one, so every part of it
is checked against the exact endpoint fibers rather than against a plot:

  * panel (a), the fiber classification at (kappa, tau) = (1, 1): M_0 is
    positive semidefinite of rank one, M_m is positive definite for m >= 2
    (thm:gram), and M_1 alone changes inertia, with the trichotomy of
    lem:M1-indefinite at a_* = 0.3690738484...;
  * MD(M_0, M_1) = (a g - 1)/a^2 > 0, the eq. (Delta1-sharp) route;
  * MD(M_1, M_m) > 0 for m >= 2, the eq. (M1-Mm-positive) route, on both sides
    of a = 1/2 where the paper's proof splits;
  * the polarization identity MD(M_1, M_1) = 2 det M_1, which is why the single
    self-pair is the only summand that can go negative;
  * the degree-two decomposition eq. (Delta2-unsimplified),
    Delta_2 = S_0 S_2 MD(M_0, M_2) + S_1^2 det M_1;
  * eq. (Delta-n-MD) itself, against a direct Cauchy-product route, so the array
    the figure draws is the actual summand set and not a mnemonic;
  * the combinatorial claim the figure exists to make: among the ordered pairs
    (k, n-k), k = 0..n, the self-pair (1, 1) occurs for n = 2 and no other n;
  * the drawn array, parsed back out of the .tex, against that rule -- entry
    set, shading, and the single boxed cell.

Numerical work is mpmath at arbitrary precision.  Run with no arguments to check
only; run with --emit to also print the array block the figure inlines.
"""

import re
import sys
from pathlib import Path

from mpmath import mp, mpf, psi, gamma, factorial

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _wallfan_common import build_S, M_endpoint

mp.dps = 40

PAPER = Path(__file__).resolve().parent.parent / "shields-2026-turan-bessel.tex"
NMAX = 5                      # rows drawn in panel (b)
A_STAR = mpf("0.3690738484")  # ten digits, as the paper prints them


def MD(U, V):
    return U[0]*V[2] + U[2]*V[0] - 2*U[1]*V[1]


def det2(U):
    return U[0]*U[2] - U[1]**2


def fibers(a, mmax):
    g = psi(1, a)
    return g, [M_endpoint(a, g, m) for m in range(mmax+1)]


def Delta_via_MD(a, n):
    """eq. (Delta-n-MD): the polarized four-copy form."""
    g, M = fibers(a, n)
    S = build_S(a, n)
    return sum(S[k]*S[n-k]*MD(M[k], M[n-k]) for k in range(n+1)) / 2


def _mul(u, v, N):
    return [sum(u[i]*v[m-i] for i in range(m+1)) for m in range(N+1)]


def Delta_via_series(a, N):
    """Independent route to Delta_n: direct series multiplication from
    eq. (Adef)-(Ckt-def).  No fibers, no S_m, no convolution identity -- it
    shares no code with Delta_via_MD, which is what makes the agreement
    below evidence rather than a restatement."""
    g = psi(1, a)
    z   = [1/(factorial(k)*gamma(a+k)) for k in range(N+1)]
    za  = [-psi(0, a+k)*z[k] for k in range(N+1)]
    zaa = [(psi(0, a+k)**2 - psi(1, a+k))*z[k] for k in range(N+1)]
    zt  = [k*z[k] for k in range(N+1)]
    ztt = [k*k*z[k] for k in range(N+1)]
    zat = [k*za[k] for k in range(N+1)]
    A = [x - y for x, y in zip(_mul(za, za, N), _mul(z, zaa, N))]
    zz = _mul(z, z, N)
    B = [p + q - r for p, q, r in
         zip(zz, _mul(z, zat, N), _mul(za, zt, N))]
    C = [w + g*(x - y + v) for w, x, y, v in
         zip(zz, _mul(z, zt, N), _mul(z, ztt, N), _mul(zt, zt, N))]
    return [x - g*y for x, y in zip(_mul(A, C, N), _mul(B, B, N))]


def pairs(n):
    return [(k, n-k) for k in range(n+1)]


def classify(k, l):
    if k == 1 and l == 1:
        return "self"
    if k == 1 or l == 1:
        return "mixed"
    return "psd"


AS = [mpf("0.05"), mpf("0.2"), A_STAR, mpf("0.45"), mpf("0.5"),
      mpf(1), mpf("2.5"), mpf(7)]

# --- panel (a): the fiber classification -----------------------------------
for a in AS:
    g, M = fibers(a, 8)
    assert abs(det2(M[0])) < mpf(10)**(-30) and M[0][0] > 0, ("M_0 rank one", a)
    for m in range(2, 9):
        assert M[m][0] > 0 and det2(M[m]) > 0, ("M_m pos def", a, m)
print("PASS: at (kappa,tau)=(1,1), M_0 is positive semidefinite of rank one and "
      "M_m is positive definite for 2 <= m <= 8, at every sampled a")

for a, want in [(mpf("0.05"), -1), (mpf("0.2"), -1), (mpf("0.45"), +1),
                (mpf(1), +1), (mpf(7), +1)]:
    g, M = fibers(a, 1)
    assert mp.sign(det2(M[1])) == want, ("M_1 inertia", a)
g, M = fibers(A_STAR, 1)
assert abs(det2(M[1])) < mpf(10)**(-9) and M[1][0] > 0, "M_1 psd rank one at a_*"
print(f"PASS: M_1 is indefinite for a < a_*, positive semidefinite of rank one at "
      f"a_* = {mp.nstr(A_STAR, 10)}, and positive definite for a > a_* "
      f"(det M_1 = {mp.nstr(det2(M[1]), 3)} there)")

# --- the two pairing kinds, and the identity that isolates the self-pair ----
for a in AS:
    g, M = fibers(a, 8)
    assert MD(M[0], M[1]) > 0, ("MD(M_0,M_1)", a)
    assert abs(MD(M[0], M[1]) - (a*g - 1)/a**2) < mpf(10)**(-28), ("closed form", a)
    for m in range(2, 9):
        assert MD(M[1], M[m]) > 0, ("MD(M_1,M_m)", a, m)
    assert abs(MD(M[1], M[1]) - 2*det2(M[1])) < mpf(10)**(-30), ("self-pair", a)
print("PASS: MD(M_0,M_1) = (ag-1)/a^2 > 0 and MD(M_1,M_m) > 0 for 2 <= m <= 8 at "
      "every sampled a, on both sides of the a = 1/2 split in the paper's proof")
print("PASS: MD(M_1,M_1) = 2 det M_1 identically -- the self-pair is the only "
      "summand carrying the inertia of M_1")

# --- eq. (Delta-n-MD) itself, against a route sharing none of its code ------
worst = mpf(0)
for a in AS:
    ser = Delta_via_series(a, NMAX)
    for n in range(1, NMAX+1):
        u, v = Delta_via_MD(a, n), ser[n]
        worst = max(worst, abs(u - v)/abs(v))
        assert u > 0, ("Delta_n > 0", a, n)
assert worst < mpf(10)**(-30), worst
print(f"PASS: eq. (Delta-n-MD) agrees with direct series multiplication to "
      f"{mp.nstr(worst, 3)} relative, n <= {NMAX} -- the drawn array is the "
      f"actual summand set")

# --- the degree-two decomposition the localization is closed by ------------
for a in AS:
    g, M = fibers(a, 2)
    S = build_S(a, 2)
    lhs = Delta_via_MD(a, 2)
    rhs = S[0]*S[2]*MD(M[0], M[2]) + S[1]**2*det2(M[1])
    assert abs(lhs - rhs)/abs(lhs) < mpf(10)**(-30), ("Delta_2 decomp", a)
print("PASS: eq. (Delta2-unsimplified), Delta_2 = S_0 S_2 MD(M_0,M_2) + "
      "S_1^2 det M_1, at every sampled a")

# --- the combinatorial claim the figure exists to make ---------------------
hits = [n for n in range(1, 400) if (1, 1) in pairs(n)]
assert hits == [2], hits
for n in range(1, NMAX+1):
    for k, l in pairs(n):
        c = classify(k, l)
        assert (c == "self") == (n == 2 and k == 1), (n, k, l)
        if c == "mixed":
            assert max(k, l) >= 2 or n == 1, (n, k, l)
print("PASS: among the ordered pairs (k, n-k), the self-pair (1,1) occurs for "
      "n = 2 and for no other n up to 399; every other appearance of index 1 is "
      "mixed with an index >= 2, except n = 1 where the partner is 0")


# --- the drawn array, parsed back out of the manuscript --------------------
CELL = re.compile(
    r"\\(fill|draw)\[(?P<sty>[^]]*)\]\s*"
    r"\((?P<x0>[-\d.]+),(?P<y0>[-\d.]+)\)\s*rectangle\s*"
    r"\((?P<x1>[-\d.]+),(?P<y1>[-\d.]+)\);\s*"
    r"%\s*cell (?P<k>\d+),(?P<l>\d+)")


def emit():
    out = []
    for n in range(1, NMAX+1):
        cy = ROW_Y[n]
        for k, l in pairs(n):
            cx = X0 + DX*k
            kind = classify(k, l)
            sty = {"psd": "draw[black!45, line width=0.4pt]",
                   "mixed": "fill[black!10] ",
                   "self": "fill[black!22] "}[kind]
            if kind == "mixed":
                out.append(f"\\fill[black!10] ({cx-HW:.2f},{cy-HH:.2f}) "
                           f"rectangle ({cx+HW:.2f},{cy+HH:.2f});  % cell {k},{l}")
                out.append(f"\\draw[black!45, line width=0.4pt] "
                           f"({cx-HW:.2f},{cy-HH:.2f}) rectangle "
                           f"({cx+HW:.2f},{cy+HH:.2f});")
            elif kind == "self":
                out.append(f"\\fill[black!22] ({cx-HW:.2f},{cy-HH:.2f}) "
                           f"rectangle ({cx+HW:.2f},{cy+HH:.2f});  % cell {k},{l}")
                out.append(f"\\draw[line width=1.1pt] ({cx-HW:.2f},{cy-HH:.2f}) "
                           f"rectangle ({cx+HW:.2f},{cy+HH:.2f});")
            else:
                out.append(f"\\draw[black!45, line width=0.4pt] "
                           f"({cx-HW:.2f},{cy-HH:.2f}) rectangle "
                           f"({cx+HW:.2f},{cy+HH:.2f});  % cell {k},{l}")
            out.append(f"\\node[font=\\footnotesize] at ({cx:.2f},{cy:.2f}) "
                       f"{{\\({k},{l}\\)}};")
    return "\n".join(out)


X0, DX, HW, HH = 1.90, 1.16, 0.50, 0.21
ROW_Y = {1: 2.85, 2: 2.30, 3: 1.75, 4: 1.20, 5: 0.65}

if PAPER.exists():
    tex = PAPER.read_text(encoding="utf-8")
    blk = tex[tex.index(r"\label{fig:defect-localization}") - 9000:
              tex.index(r"\label{fig:defect-localization}")] \
        if r"\label{fig:defect-localization}" in tex else ""
    if blk:
        drawn = {}
        for m in CELL.finditer(blk):
            k, l = int(m.group("k")), int(m.group("l"))
            shaded = "fill" == m.group(1)
            dark = "black!22" in m.group("sty")
            drawn[(k, l)] = (shaded, dark)
        want = {(k, l) for n in range(1, NMAX+1) for k, l in pairs(n)}
        assert set(drawn) == want, (set(drawn) ^ want)
        for (k, l), (shaded, dark) in drawn.items():
            c = classify(k, l)
            assert shaded == (c != "psd"), ("shading", k, l, c)
            assert dark == (c == "self"), ("boxed cell", k, l, c)
        nboxed = sum(1 for v in drawn.values() if v[1])
        assert nboxed == 1, nboxed
        print(f"PASS: the manuscript draws all {len(want)} pairs for n <= {NMAX}, "
              f"shades exactly the {sum(1 for v in drawn.values() if v[0]) - 1} "
              f"mixed cells, and boxes exactly one cell, (1,1)")
    else:
        print("NOTE: fig:defect-localization not yet in the manuscript; "
              "array guard skipped")

print("\nALL PASS")

# --- emit the array block --------------------------------------------------
if "--emit" in sys.argv:
    print()
    print(emit())
