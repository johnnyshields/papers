"""Consistency audit: verify every numeric claim in the caption of
fig:decomposition-and-defect, and the statement/proof bookkeeping that
depends on those numbers.

Paper: shields-2026-forgacs-tran-numerators.tex
Figure setting throughout: Q(t) = (1-t)(1-t/2)(1-t/4), r = 1.

Claims checked (caption text in quotes):
  C1  "I_{Q,r} = (a,b) = (0.0559..., 3.7466...)"
  C2  B(t) = 7t^2+8 is left unshifted by lem:laurent-reduction (M = m)
  C3  "t_+(pi/2) = i sqrt(8/7) and z(pi/2) = 45/28", so B(t_+(pi/2)) = 0
  C4  the lower/upper endpoint exponent p = -1, so the envelope |W| -> infinity
  C5  panel B: N = (1+z+z^2) + t(2-z) gives deg P_m = m+2
  C6  panel B: at m = 14 and m = 38, exactly m simple zeros in I_{Q,r}
      and exactly two elsewhere, a conjugate pair at -0.5655... +- 1.3674... i
      "agreeing to thirteen decimals at the two indices"
  C7  the plotted zero lists in the .tex match the computed zeros
  C8  eq:dominance-bound |R_M| <= |W|/2 fails only within 1e-11 of theta_1 at M=14
"""

import mpmath as mp

mp.mp.dps = 60

R = 1  # r = 1 throughout the figure

# Q(t) = (1-t)(1-t/2)(1-t/4) = 1 - (7/4)t + (7/8)t^2 - (1/8)t^3
XS = [mp.mpf(1), mp.mpf(2), mp.mpf(4)]
QC = [mp.mpf(1), -mp.mpf(7) / 4, mp.mpf(7) / 8, -mp.mpf(1) / 8]  # ascending


def poly(coeffs, t):
    """Evaluate sum coeffs[k] t^k."""
    return sum(c * t**k for k, c in enumerate(coeffs))


def Q(t):
    return poly(QC, t)


def dQ(t):
    return sum(k * c * t ** (k - 1) for k, c in enumerate(QC) if k >= 1)


def check_Q_expansion():
    prod = lambda t: (1 - t) * (1 - t / 2) * (1 - t / 4)
    for t in [mp.mpf("0.3"), mp.mpf("2.7"), mp.mpf(-1), mp.mpc(0, 1)]:
        assert abs(prod(t) - Q(t)) < mp.mpf(10) ** -40, t
    print("Q expansion 1 - 7t/4 + 7t^2/8 - t^3/8 .......... OK")


# ---------------------------------------------------------------- C1: a and b
def endpoints():
    """t_a = smallest positive critical point of g = -Q/t^r; t_b = the
    negative one (r = 1).  Critical points solve r Q(t) - t Q'(t) = 0."""
    crit = lambda t: R * Q(t) - t * dQ(t)
    # r Q - t Q' = 1 - (7/8)t^2 + (1/4)t^3  (r = 1)
    cc = [mp.mpf(1), mp.mpf(0), -mp.mpf(7) / 8, mp.mpf(1) / 4]
    for t in [mp.mpf("0.5"), mp.mpf("3.1"), mp.mpf(-2)]:
        assert abs(poly(cc, t) - crit(t)) < mp.mpf(10) ** -40
    roots = mp.polyroots([c for c in reversed(cc)], maxsteps=200, extraprec=200)
    real = sorted(mp.re(z) for z in roots if abs(mp.im(z)) < mp.mpf(10) ** -30)
    pos = [t for t in real if t > 0]
    neg = [t for t in real if t < 0]
    t_a, t_b = min(pos), max(neg)
    g = lambda t: -Q(t) / t**R
    return t_a, t_b, g(t_a), g(t_b)


T_A, T_B, A_END, B_END = endpoints()


def check_C1():
    print(f"  t_a = {mp.nstr(T_A, 12)}   t_b = {mp.nstr(T_B, 12)}")
    print(f"  a   = {mp.nstr(A_END, 12)}   b   = {mp.nstr(B_END, 12)}")
    # caption prints a = 0.0559..., b = 3.7466...; axis extra ticks carry
    # the 8-digit values 0.05593557 and 3.746690
    assert mp.nstr(A_END, 4) == "0.05594", mp.nstr(A_END, 8)
    assert abs(A_END - mp.mpf("0.05593557")) < mp.mpf("1e-8"), mp.nstr(A_END, 12)
    assert abs(B_END - mp.mpf("3.746690")) < mp.mpf("1e-6"), mp.nstr(B_END, 12)
    # the caption's truncations
    assert mp.floor(A_END * 10**4) / 10**4 == mp.mpf("0.0559")
    assert mp.floor(B_END * 10**4) / 10**4 == mp.mpf("3.7466")
    assert A_END > 0, "smallest zero of Q simple => a > 0"
    print("C1  I_{Q,r} = (0.0559..., 3.7466...) ............ OK")


# ------------------------------------------------- C2/C5: the Laurent reduction
def laurent_A(N_coeffs, E):
    """A(t) = t^{rE} N(t, -Q(t)/t^r) as a polynomial in t.

    N_coeffs[beta] is the list of t-coefficients of the z^beta part.
    Returns ascending coefficient list of A.
    """
    # work with polynomials as ascending coefficient lists
    def pmul(p, q):
        out = [mp.mpf(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return out

    def padd(p, q):
        n = max(len(p), len(q))
        return [
            (p[i] if i < len(p) else mp.mpf(0)) + (q[i] if i < len(q) else mp.mpf(0))
            for i in range(n)
        ]

    total = [mp.mpf(0)]
    for beta, nb in enumerate(N_coeffs):
        if all(c == 0 for c in nb):
            continue
        # term: t^{alpha} * (-1)^beta Q^beta * t^{r(E-beta)}
        Qb = [mp.mpf(1)]
        for _ in range(beta):
            Qb = pmul(Qb, QC)
        sign = mp.mpf(-1) ** beta
        shift = R * (E - beta)
        piece = pmul(nb, [sign * c for c in Qb])
        piece = [mp.mpf(0)] * shift + piece
        total = padd(total, piece)
    while len(total) > 1 and total[-1] == 0:
        total.pop()
    return total


def check_C2():
    # N = 7t^2 + 8  ->  E = 0, A = N, mu = 0, B = A, M = m + rE - mu = m
    N = [[mp.mpf(8), mp.mpf(0), mp.mpf(7)]]  # z^0 part only
    A = laurent_A(N, E=0)
    assert [mp.nstr(c, 8) for c in A] == ["8.0", "0.0", "7.0"], A
    mu = next(i for i, c in enumerate(A) if c != 0)
    assert mu == 0 and A[0] != 0
    assert R * 0 - mu == 0, "shift must be zero"
    print("C2  B = 7t^2+8 unshifted (M = m) ............... OK")
    return A


def check_C5():
    # N = (1 + z + z^2) + t(2 - z):  z^0 -> 1 + 2t, z^1 -> 1 - t, z^2 -> 1
    N = [
        [mp.mpf(1), mp.mpf(2)],
        [mp.mpf(1), -mp.mpf(1)],
        [mp.mpf(1)],
    ]
    E = 2
    A = laurent_A(N, E)
    mu = next(i for i, c in enumerate(A) if c != 0)
    shift = R * E - mu
    d = max(len(QC) - 1, R)
    assert d == 3
    assert max(len(part) - 1 for part in N) < d, "properness deg_t N < d"
    assert mu == 0, mu
    assert shift == 2, shift
    B = A[mu:]
    print(f"  A(0) = {mp.nstr(A[0], 8)}, mu = {mu}, deg B = {len(B) - 1}")
    print(f"C5  M = m + {shift}, so deg P_m = floor(M/r) = m+{shift} ... OK")
    return B, shift


# ------------------------------------------- C3: the amplitude zero at theta_1
def principal_pair(theta):
    """Solve for tau > 0 and z real with Q(tau e^{i theta}) + z (tau e^{i
    theta})^r = 0.  Im part determines tau, Re part then gives z."""
    e = mp.expjpi(theta / mp.pi)

    def imres(tau):
        t = tau * e
        return mp.im(Q(t) / t**R)

    lo, hi = mp.mpf("1e-8"), mp.mpf(50)
    tau = mp.findroot(imres, mp.mpf("1.0"), solver="secant", tol=mp.mpf(10) ** -50)
    if not (tau > 0):
        tau = mp.findroot(imres, [lo, hi], solver="bisect")
    t = tau * e
    z = -mp.re(Q(t) / t**R)
    assert abs(Q(t) + z * t**R) < mp.mpf(10) ** -40, abs(Q(t) + z * t**R)
    return tau, z, t


def check_C3():
    tau, z, tp = principal_pair(mp.pi / 2)
    print(f"  tau(pi/2) = {mp.nstr(tau, 20)}   sqrt(8/7) = {mp.nstr(mp.sqrt(mp.mpf(8)/7), 20)}")
    print(f"  z(pi/2)   = {mp.nstr(z, 20)}   45/28     = {mp.nstr(mp.mpf(45)/28, 20)}")
    assert abs(tau - mp.sqrt(mp.mpf(8) / 7)) < mp.mpf(10) ** -40
    assert abs(z - mp.mpf(45) / 28) < mp.mpf(10) ** -40
    assert abs(tp - mp.mpc(0, 1) * mp.sqrt(mp.mpf(8) / 7)) < mp.mpf(10) ** -40
    B = lambda t: 7 * t**2 + 8
    assert abs(B(tp)) < mp.mpf(10) ** -40, abs(B(tp))
    assert A_END < z < B_END, "theta_1 must sit inside the parameter interval"
    print("C3  t_+(pi/2)=i sqrt(8/7), z=45/28, B(t_+)=0 ... OK")
    return tau, z, tp


# ------------------------------------------------- C4: the endpoint exponent p
def check_C4():
    """p = nu - (k-1) at a finite endpoint; k = max{rho,2} (lower), 2 (upper);
    nu = order of vanishing of B at t_e."""
    B = lambda t: 7 * t**2 + 8
    rho = sum(1 for x in XS if x == min(XS))
    assert rho == 1, "smallest zero of Q is simple"
    for name, t_e in (("lower", T_A), ("upper", T_B)):
        k = max(rho, 2) if name == "lower" else 2
        assert k == 2
        nu = 0 if abs(B(t_e)) > mp.mpf(10) ** -30 else None
        assert nu == 0, f"B({name} endpoint) = {mp.nstr(B(t_e), 8)} != 0"
        p = nu - (k - 1)
        assert p == -1, p
        print(f"  {name} endpoint: t_e={mp.nstr(t_e,8)}, k={k}, nu={nu}, p={p}")
    print("C4  p = -1 at both endpoints, so |W| -> infinity  OK")


# -------------------------------------------- C6/C7: the panel-B zero pictures
def coeff_series(Bco, z, nmax):
    """[t^n] B(t)/(Q(t)+z t^r) for n = 0..nmax, by long division."""
    D = [c for c in QC]
    while len(D) <= R:
        D.append(mp.mpf(0))
    D[R] = D[R] + z
    out = []
    num = list(Bco) + [mp.mpf(0)] * (nmax + 1 + len(D))
    for n in range(nmax + 1):
        c = num[n] / D[0]
        out.append(c)
        for j, dj in enumerate(D):
            num[n + j] -= c * dj
    return out


def P_m_coeffs(Bco, shift, m, deg):
    """Coefficients of P_m(z) = F_{m+shift}(z), degree deg, by interpolation
    at deg+1 nodes -- each node is one exact power-series division."""
    M = m + shift
    nodes = [mp.mpf(2) * j / (deg + 1) - 1 for j in range(deg + 1)]
    nodes = [n + mp.mpf("0.37") for n in nodes]  # avoid symmetric cancellation
    vals = [coeff_series(Bco, zz, M)[M] for zz in nodes]
    # Lagrange -> monomial coefficients via Vandermonde solve
    Amat = mp.matrix(deg + 1, deg + 1)
    for i, zz in enumerate(nodes):
        for j in range(deg + 1):
            Amat[i, j] = zz**j
    sol = mp.lu_solve(Amat, mp.matrix(vals))
    return [sol[j] for j in range(deg + 1)]


def check_C6_C7(Bco, shift):
    tol_in = mp.mpf(10) ** -25
    pair_by_m = {}
    for m in (14, 38):
        deg = m + shift
        co = P_m_coeffs(Bco, shift, m, deg)
        assert abs(co[deg]) > mp.mpf(10) ** -30, "leading coefficient must not vanish"
        roots = mp.polyroots(
            [co[k] for k in range(deg, -1, -1)], maxsteps=400, extraprec=400
        )
        inside, outside = [], []
        for zz in roots:
            if abs(mp.im(zz)) < tol_in and A_END < mp.re(zz) < B_END:
                inside.append(mp.re(zz))
            else:
                outside.append(zz)
        inside.sort()
        print(f"  m={m}: deg P_m = {deg}, |inside I| = {len(inside)}, "
              f"|outside| = {len(outside)}")
        assert deg == m + 2, deg
        assert len(inside) == m, (m, len(inside))
        assert len(outside) == 2, (m, len(outside))
        # simple zeros inside: consecutive gaps well above numerical noise
        gaps = [inside[i + 1] - inside[i] for i in range(len(inside) - 1)]
        assert min(gaps) > mp.mpf(10) ** -6, min(gaps)
        # the outside pair is a conjugate pair
        o = sorted(outside, key=lambda w: mp.im(w))
        assert abs(o[0] - mp.conj(o[1])) < mp.mpf(10) ** -25
        pair_by_m[m] = o[1]
        print(f"        exceptional pair = {mp.nstr(mp.re(o[1]), 16)} "
              f"+- {mp.nstr(mp.im(o[1]), 16)} i")
        # caption digits
        assert mp.floor(mp.re(o[1]) * -(10**4)) / 10**4 == mp.mpf("0.5655"), mp.nstr(mp.re(o[1]), 10)
        assert mp.floor(mp.im(o[1]) * 10**4) / 10**4 == mp.mpf("1.3674"), mp.nstr(mp.im(o[1]), 10)
        # plotted marker in the .tex
        assert abs(mp.re(o[1]) - mp.mpf("-0.56552684")) < mp.mpf("1e-8")
        assert abs(mp.im(o[1]) - mp.mpf("1.3674916")) < mp.mpf("1e-7")
        globals().setdefault("_INSIDE", {})[m] = inside
    d = abs(pair_by_m[14] - pair_by_m[38])
    print(f"  |pair(14) - pair(38)| = {mp.nstr(d, 6)}")
    assert d < mp.mpf("1e-13"), mp.nstr(d, 6)
    print("C6  m simple zeros in I + exactly one conjugate pair,")
    print("    agreeing to 13 decimals across m=14,38 ......... OK")


TEX_M14 = """0.0819235 0.163594 0.307396 0.514709 0.779251 1.09186
1.44571 1.83220 2.23495 2.63133 2.99692 3.30865 3.54669 3.69588"""

TEX_M38 = """0.0593608 0.0697425 0.0873782 0.112703 0.146220 0.188424
0.239744 0.300492 0.370835 0.450779 0.540167 0.638700 0.745965 0.861476
0.984705 1.11510 1.25205 1.39489 1.54281 1.69486 1.84997 2.00696 2.16454
2.32139 2.47615 2.62745 2.77394 2.91431 3.04727 3.17161 3.28618 3.38993
3.48189 3.56121 3.62714 3.67907 3.71652 3.73913"""


def check_C7_plotted():
    for m, blob in ((14, TEX_M14), (38, TEX_M38)):
        plotted = [mp.mpf(s) for s in blob.split()]
        computed = _INSIDE[m]
        assert len(plotted) == m, (m, len(plotted))
        assert len(plotted) == len(computed)
        worst = max(abs(p - c) for p, c in zip(plotted, computed))
        print(f"  m={m}: {len(plotted)} plotted zeros, max |plotted-computed| "
              f"= {mp.nstr(worst, 4)}")
        assert worst < mp.mpf("6e-6"), (m, mp.nstr(worst, 8))
        assert all(A_END < p < B_END for p in plotted), "plotted zeros inside I"
    print("C7  plotted zero lists match computed zeros ..... OK")


# ------------------------------- C8: where the dominance inequality really fails
def W_and_R(Bco, theta, M):
    """Return |W(theta)| and |R_M(theta)| for the decomposition
    tau^{M+1} F_M(z(theta)) = 2 Re(W e^{-i(M+1)theta}) + R_M."""
    tau, z, tp = principal_pair(theta)
    Bv = lambda t: poly(Bco, t)
    dD = dQ(tp) + R * z * tp ** (R - 1)
    W = -Bv(tp) / dD
    full = tau ** (M + 1) * coeff_series(Bco, z, M)[M]
    principal = 2 * mp.re(W * mp.expjpi(-(M + 1) * theta / mp.pi))
    return abs(W), abs(full - principal)


def check_C8(Bco):
    M = 14
    th1 = mp.pi / 2
    print("  offset from theta_1   |R_M|/|W|   dominance |R|<=|W|/2 ?")
    prev_bad = None
    for e in range(4, 15):
        off = mp.mpf(10) ** -e
        for s in (+1, -1):
            aW, aR = W_and_R(Bco, th1 + s * off, M)
            ratio = aR / aW
            ok = ratio <= mp.mpf("0.5")
            if s == +1:
                print(f"    1e-{e:<2d}            {mp.nstr(ratio, 6):>12}   "
                      f"{'yes' if ok else 'NO'}")
            if not ok:
                prev_bad = max(prev_bad or 0, e)
    # claim: fails only within 1e-11 of theta_1
    aW, aR = W_and_R(Bco, th1 + mp.mpf(10) ** -11, M)
    assert aR / aW <= mp.mpf("0.5"), "should already hold at 1e-11"
    aW, aR = W_and_R(Bco, th1 + mp.mpf(10) ** -13, M)
    assert aR / aW > mp.mpf("0.5"), "should fail well inside 1e-11"
    print("C8  dominance holds at 1e-11, fails by 1e-13 .... OK")
    print("    (caption's 'fails only within 1e-11' is an upper bound: sound)")


if __name__ == "__main__":
    check_Q_expansion()
    check_C1()
    B1 = check_C2()
    check_C3()
    check_C4()
    B2, shift2 = check_C5()
    check_C6_C7(B2, shift2)
    check_C7_plotted()
    check_C8(B1)
    print("\nall figure-caption claims verified")
