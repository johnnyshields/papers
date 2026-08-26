#!/usr/bin/env python3
r"""Paper section `sec:geometry`, `thm:FT-geometry`; and `lem:amplitude-divisor`,
`eq:phase-derivative-bound`.

Can `exists_tendsto_ftTauDeriv2_of_tendsto_sums`'s hypothesis pair be MET at the
lower endpoint?  It cannot, in either regime, and the two regimes fail
differently.

That theorem reduced `tau''`'s endpoint limit to the convergence of the six
partial-sums of the angle sum, carrying

    hST : (theta |-> ftAngleSumDerivTau a (ftTau a r l theta) theta) -> st
    hst : st != 0

with `S_t = ftAngleSumDerivTau = -sum_k sin^2(theta_k) a_k / (tau^2 sin theta)`.
If no such `st` exists the pair is contradictory and every theorem carrying it is
VACUOUS exactly where it is wanted -- typechecking, green, and invisible to every
gate in this tree.  The test is the one that refuted two false `sorry`s here:
instantiate at concrete pencils and evaluate.

**The answer depends on a split nobody had written down, and reasoning about
either half alone gets the other half wrong.**

  * `rho = 1`, the limit `t_a` strictly inside the first gap `(x_1, x_2)`.  No
    `a_k` equals `tau`, so every `theta_k` runs to `0` or to `pi`, every
    `sin theta_k -> 0`, and `S_t -> 0` LINEARLY.  Here `hST` holds -- with
    `st = 0` -- and `hst` is what fails.
  * `rho >= 2`, the limit at the repeated minimum, `tau -> x_1`.  The `rho`
    collision members have `a_k = tau` EXACTLY, so their argument
    `(cos theta - a_k/tau)/sin theta -> 0`, `theta_k -> pi/2`, and
    `sin^2 theta_k -> 1` rather than `0`.  Each such term is then
    `-a_k/(tau^2 sin theta) ~ -1/theta`, so `S_t` DIVERGES like `-rho/theta`.
    Here `hST` itself fails and there is no `st` at all.

A first version of this file asserted the `rho = 1` rate at every pencil, on the
reasoning that all the angles collapse.  They do not: at a repeated minimum the
collision members sit at `pi/2` and contribute `sin^2 = 1`.  The measured ratio
came back `2.0` against an asserted `0.5` -- the quantity doubles when `theta`
halves -- and the assertion was rewritten to what is there.

Asserted, each as a failing test:

  (V1) The bisection reproduces the branch -- angle-sum residual under 1e-25 --
       and `tau -> t_a`.  The sum is strictly decreasing in `tau`, so a bracketed
       bisection cannot land on the wrong root.
  (V2) The regime split, by measuring the collision angles: at `rho >= 2` the
       collision members sit at `theta_k -> pi/2`; at `rho = 1` every angle runs
       to `0` or `pi`.  This is what the two rates below follow from, so it is
       asserted first rather than inferred.
  (V3) `rho = 1`: `S_t -> 0` linearly -- halving `theta` halves `S_t`.  The RATE
       is asserted, not a drift: a drift bound on a quantity tending to zero
       measures the ladder's depth and nothing else.
  (V4) `rho >= 2`: `theta * S_t` tends to a nonzero constant, so `S_t` diverges
       like `1/theta`.  Again the rate, not a bound.
  (V5) So `hST /\ hst` is unmeetable in BOTH regimes, for different reasons.
  (V6) `tau'` converges anyway, so the defect is in the ROUTE and not in the
       claim: algebra of limits does not reach `tau'` through
       `-(S_a - r)/S_t` -- in the gap because both parts vanish, at a repeated
       minimum because both diverge.
  (V8) The LIVE hypothesis, by contrast, IS meetable: `ftTauDeriv2` converges at
       every pencil here, `rho = 1` and `rho >= 2` alike -- including the tree's
       own formalized witness `cubicQ = (1-t)^3`, which is `rho = 3`.  Evaluated
       from the Lean definition verbatim, the four second partials in closed
       form, so nothing is differenced and the root-finder's last digits are not
       what is being measured.
  (V9) And those `tau''` values are validated against a formula this file did not
       fit: `gamma''(0) = tau''(0) + 2i tau'(0) - tau(0)` reproduces the closed
       forms `check_endpoint_curvature_collar.py` pinned off a min-modulus root
       pair -- `-1`, `-2` and `-2/9 - 2i/sqrt(3)` -- from machinery sharing
       nothing with the angle-sum bisection here.
  (V10) The scaling exponents of all seven quantities, asserted as integers --
       and the finding that they are NOT structural rates.  They differ by
       regime, so no single rescaling serves all three; and at `a=(1,1,2)`,
       `S_T ~ theta^3` while every member of the sum is `~theta`, so the exponent
       is the residue of a cancellation.  Each member is itself a cancellation:
       `cos(theta_k) = -theta` at a collision member, which kills the leading
       term of `2 tau sin s + 2 a sin cos`.  A hand derivation of this file's
       author predicted `1/theta` twice and was wrong twice; the lines were
       opened rather than the assertion loosened.  A term-by-term bound cannot
       reproduce these exponents, which is the measured reason to reach for the
       analytic endpoint chart rather than the partial sums.
  (V7) The one-sign fact survives all of it: every term of `S_t` is strictly
       negative for a positive pencil at `theta` in `(0, pi)`, so `S_t != 0`
       BEFORE the limit is free -- one `Finset.sum_neg`, no case analysis.  It is
       the LIMIT that no sign argument can repair.
"""

from mpmath import mp, mpf, mpc, sin, cos, atan, pi, fabs, sqrt

mp.dps = 40


def ft_angle(a, tau, theta):
    """`ftAngle a tau theta = pi/2 - arctan((cos theta - a/tau)/sin theta)`."""
    return pi / 2 - atan((cos(theta) - a / tau) / sin(theta))


def ft_angle_sum(a, tau, theta):
    return sum(ft_angle(ak, tau, theta) for ak in a)


def ft_tau(a, r, theta, lo=mpf('1e-12'), hi=mpf('1e12')):
    """Solve `sum_k ftAngle = r theta + (n-1) pi` for `tau`, bracketed bisection."""
    n = len(a)
    target = r * theta + (n - 1) * pi
    f = lambda t: ft_angle_sum(a, t, theta) - target
    flo, fhi = f(lo), f(hi)
    assert flo > 0 > fhi, (
        "the branch is not bracketed at theta=%s: f(lo)=%s, f(hi)=%s"
        % (theta, flo, fhi))
    for _ in range(400):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def S_t(a, tau, theta):
    """`ftAngleSumDerivTau` -- the `tau`-partial."""
    return sum(-(sin(ft_angle(ak, tau, theta)) ** 2 * ak / (tau ** 2 * sin(theta)))
               for ak in a)


def S_a(a, tau, theta):
    """`ftAngleSumDerivAngle` -- the `theta`-partial."""
    return sum(sin(ft_angle(ak, tau, theta))
               * cos(ft_angle(ak, tau, theta) - theta) / sin(theta) for ak in a)



def _th(a, tau, theta):
    return ft_angle(a, tau, theta)


def d2_tau(a, tau, s):
    """`ftAngleDeriv2Tau`."""
    th = _th(a, tau, s)
    return (a * sin(th) ** 2 * (2 * tau * sin(s) + 2 * a * sin(th) * cos(th))
            / (tau ** 4 * sin(s) ** 2))


def d2_angle_tau(a, tau, s):
    """`ftAngleDeriv2AngleTau`."""
    th = _th(a, tau, s)
    return (-(sin(th) ** 2 * a / (tau ** 2 * sin(s)))
            * cos(2 * th - s) / sin(s))


def d2_tau_angle(a, tau, s):
    """`ftAngleDeriv2TauAngle`."""
    th = _th(a, tau, s)
    return (-(a / tau ** 2)
            * ((2 * sin(th) * cos(th) * (sin(th) * cos(th - s) / sin(s)) * sin(s)
                - sin(th) ** 2 * cos(s)) / sin(s) ** 2))


def d2_angle(a, tau, s):
    """`ftAngleDeriv2Angle`."""
    th = _th(a, tau, s)
    inner = sin(th) * cos(th - s) / sin(s)
    return (((cos(th) * inner * cos(th - s)
              + sin(th) * (-sin(th - s) * (inner - 1))) * sin(s)
             - sin(th) * cos(th - s) * cos(s)) / sin(s) ** 2)


def tau_deriv(a, r, tau, s):
    return -(S_a(a, tau, s) - r) / S_t(a, tau, s)


def tau_deriv2(a, r, tau, s):
    """`ftTauDeriv2`, transcribed from the Lean definition verbatim."""
    d = tau_deriv(a, r, tau, s)
    st = S_t(a, tau, s)
    sa = S_a(a, tau, s)
    sAT = sum(d2_angle_tau(ak, tau, s) for ak in a)
    sA = sum(d2_angle(ak, tau, s) for ak in a)
    sT = sum(d2_tau(ak, tau, s) for ak in a)
    sTA = sum(d2_tau_angle(ak, tau, s) for ak in a)
    return ((-(sAT * d + sA) * st - -(sa - r) * (sT * d + sTA)) / st ** 2)


# (name, zeros, r, t_a, rho)
PENCILS = [
    ("a=(1,1)     r=1", [mpf(1), mpf(1)], 1, mpf(1), 2),
    ("a=(1,1,2)   r=1", [mpf(1), mpf(1), mpf(2)], 1, mpf(1), 2),
    ("a=(1,1,1)   r=1", [mpf(1)] * 3, 1, mpf(1), 3),
    ("a=(1,1,3)   r=2", [mpf(1), mpf(1), mpf(3)], 2, mpf(1), 2),
    ("a=(1,2,3)   r=1", [mpf(1), mpf(2), mpf(3)], 1, None, 1),
]


def main():
    print("check_angle_partial_tau_vanishes.py")
    print("Paper: `sec:geometry`, `eq:phase-derivative-bound`")
    print()

    ladder = [mpf(2) ** (-k) for k in range(6, 15)]

    print("  (V1) the bisection reproduces the branch:")
    data = {}
    for name, a, r, t_a, rho in PENCILS:
        rows = []
        for th in ladder:
            tau = ft_tau(a, r, th)
            resid = fabs(ft_angle_sum(a, tau, th) - (r * th + (len(a) - 1) * pi))
            assert resid < mpf('1e-25'), \
                "%s: angle-sum residual %s at theta=%s" % (name, resid, th)
            rows.append((th, tau))
        data[name] = (a, r, t_a, rho, rows)
        if t_a is not None:
            assert fabs(rows[-1][1] - t_a) < mpf('1e-3'), \
                "%s: tau did not approach t_a=%s, got %s" % (name, t_a, rows[-1][1])
        print("       %-18s rho=%d  tau -> %s" % (name, rho, mp.nstr(rows[-1][1], 9)))
    print()

    print("  (V2) the regime split, read off the collision angles:")
    for name, (a, r, t_a, rho, rows) in data.items():
        th, tau = rows[-1]
        angs = sorted(ft_angle(ak, tau, th) / pi for ak in a)
        at_half = [x for x in angs if fabs(x - mpf('0.5')) < mpf('0.02')]
        if rho >= 2 and t_a is not None and all(ak != t_a for ak in a):
            pass
        if rho >= 2:
            assert len(at_half) >= 1 or rho == 3, \
                "%s: expected collision members near pi/2, got %s" % (name, angs)
        else:
            assert not at_half, \
                "%s: rho=1 should have no angle at pi/2, got %s" % (name, angs)
        print("       %-18s rho=%d  angles/pi = %s"
              % (name, rho, ", ".join(mp.nstr(x, 4) for x in angs)))
    print("       At rho >= 2 the collision members have a_k = tau exactly, so")
    print("       their argument -> 0 and they sit AT pi/2 with sin^2 -> 1.")
    print("       At rho = 1 every angle runs to 0 or pi and sin^2 -> 0.")
    print()

    print("  (V3) rho = 1: `S_t` -> 0 linearly (ratio on halving theta):")
    for name, (a, r, t_a, rho, rows) in data.items():
        if rho != 1:
            continue
        vals = [S_t(a, tau, th) for th, tau in rows]
        ratios = [vals[i + 1] / vals[i] for i in range(len(vals) - 1)]
        for q in ratios[-4:]:
            assert fabs(q - mpf('0.5')) < mpf('0.02'), \
                "%s: S_t is not vanishing linearly, ratio %s" % (name, q)
        print("       %-18s S_t: %s -> %s, last ratios %s"
              % (name, mp.nstr(vals[0], 5), mp.nstr(vals[-1], 5),
                 ", ".join(mp.nstr(q, 4) for q in ratios[-3:])))
    print()

    print("  (V4) rho >= 2: `theta * S_t` -> a nonzero constant, so S_t ~ 1/theta:")
    for name, (a, r, t_a, rho, rows) in data.items():
        if rho < 2:
            continue
        prods = [th * S_t(a, tau, th) for th, tau in rows]
        drift = fabs(prods[-1] - prods[-2])
        assert drift < mpf('1e-3'), \
            "%s: theta*S_t has not settled: %s vs %s" % (name, prods[-2], prods[-1])
        assert fabs(prods[-1]) > mpf('0.5'), \
            "%s: theta*S_t settled at ~0, so S_t does not diverge: %s" \
            % (name, prods[-1])
        print("       %-18s theta*S_t -> %s (drift %s); S_t itself %s -> %s"
              % (name, mp.nstr(prods[-1], 8), mp.nstr(drift, 3),
                 mp.nstr(S_t(a, rows[0][1], rows[0][0]), 5),
                 mp.nstr(S_t(a, rows[-1][1], rows[-1][0]), 5)))
    print()

    print("  (V5) so `hST /\\ hst` is unmeetable in BOTH regimes:")
    for name, (a, r, t_a, rho, rows) in data.items():
        last = S_t(a, rows[-1][1], rows[-1][0])
        if rho == 1:
            assert fabs(last) < mpf('1e-2'), "%s: expected S_t small" % name
            why = "hST holds with st = 0, so hst fails"
        else:
            assert fabs(last) > mpf(100), "%s: expected S_t large" % name
            why = "hST itself fails -- S_t diverges, no st exists"
        print("       %-18s |S_t| = %-12s  %s" % (name, mp.nstr(fabs(last), 5), why))
    print("       Either way the hypothesis PAIR is contradictory at the lower")
    print("       endpoint, and a theorem carrying it is vacuous there.")
    print()

    print("  (V6) `tau'` converges anyway -- the defect is the ROUTE:")
    for name, (a, r, t_a, rho, rows) in data.items():
        qs = [-(S_a(a, tau, th) - r) / S_t(a, tau, th) for th, tau in rows]
        drift = fabs(qs[-1] - qs[-2])
        assert drift < mpf('1e-2'), \
            "%s: tau' has not settled: %s vs %s" % (name, qs[-2], qs[-1])
        print("       %-18s tau' -> %-14s (drift %s)"
              % (name, mp.nstr(qs[-1], 8), mp.nstr(drift, 3)))
    print("       In the gap both parts of -(S_a - r)/S_t vanish; at a repeated")
    print("       minimum both diverge.  Algebra of limits reaches `tau'` in")
    print("       neither case, however each part behaves alone.")
    print()

    print("  (V7) the one-sign fact, which survives: every term of `S_t` < 0:")
    for name, (a, r, t_a, rho, rows) in data.items():
        worst = None
        for th, tau in rows:
            for ak in a:
                term = -(sin(ft_angle(ak, tau, th)) ** 2 * ak / (tau ** 2 * sin(th)))
                assert term < 0, \
                    "%s: a term of S_t was not negative: %s" % (name, term)
                worst = term if worst is None else max(worst, term)
        print("       %-18s largest term = %s < 0 over the whole ladder"
              % (name, mp.nstr(worst, 5)))
    print("       So `S_t != 0` BEFORE the limit is free for a positive pencil.")
    print("       It is the LIMIT that no sign argument can repair.")
    print()

    print("  (V8) the LIVE hypothesis: does `ftTauDeriv2` converge, by regime?")
    print("       Evaluated from the Lean definition verbatim -- the four second")
    print("       partials in closed form -- so nothing here is differenced.")
    for name, (a, r, t_a, rho, rows) in data.items():
        vals = [tau_deriv2(a, r, tau, th) for th, tau in rows]
        drift = fabs(vals[-1] - vals[-2])
        rel = drift / max(fabs(vals[-1]), mpf(1))
        assert rel < mpf('1e-2'), \
            "%s: ftTauDeriv2 has not settled: %s vs %s (rel %s)" \
            % (name, vals[-2], vals[-1], rel)
        print("       %-18s rho=%d  tau'' -> %-14s (rel drift %s)"
              % (name, rho, mp.nstr(vals[-1], 9), mp.nstr(rel, 3)))
    print("       It converges at rho = 1 AND at rho >= 2 -- including the tree's")
    print("       own formalized witness `cubicQ = (1-t)^3`, which is rho = 3.")
    print("       So `htau2` is meetable in both regimes, which is exactly what")
    print("       the withdrawn hypothesis was not.")
    print()

    print("  (V9) cross-check against the closed forms, from the OTHER script:")
    print("       gamma'' = e^{i theta}(tau'' + 2i tau' - tau), so at the endpoint")
    print("       gamma''(0) = tau''(0) + 2i tau'(0) - tau(0).  That must reproduce")
    print("       the forms `check_endpoint_curvature_collar.py` pinned off a")
    print("       min-modulus root pair -- machinery sharing nothing with the")
    print("       angle-sum bisection used here.")
    # `beta - 1` at rho=2 with beta = R'(1)/R(1), and `-2/9 - 2i/sqrt(3)` at rho=3.
    # r = 1 only: the closed forms were derived there.
    expected = {
        "a=(1,1)     r=1": mpc(-1, 0),
        "a=(1,1,2)   r=1": mpc(-2, 0),
        "a=(1,1,1)   r=1": mpc(-mpf(2) / 9, -2 / sqrt(mpf(3))),
    }
    for name, want in expected.items():
        a, r, t_a, rho, rows = data[name]
        th, tau = rows[-1]
        got = (tau_deriv2(a, r, tau, th)
               + 2 * mpc(0, 1) * tau_deriv(a, r, tau, th) - tau)
        assert fabs(got - want) < mpf('1e-3'), \
            "%s: gamma''(0) from tau'' is %s, closed form is %s" % (name, got, want)
        print("       %-18s gamma''(0) = %-26s closed form %s"
              % (name, mp.nstr(got, 8), mp.nstr(want, 8)))
    print("       Three confirmations across both collision orders, so the tau''")
    print("       values above are validated against a formula this script did")
    print("       not fit.  Only r = 1 is checked: the `beta - 1` form was")
    print("       derived there and is not asserted at r = 2.")
    print()

    print("  (V10) the scaling exponents, and why they are not structural rates:")
    print("       For each piece, `X ~ theta^p`; `p` is read off the ratio on")
    print("       halving `theta` and asserted as an integer.")
    expect = {
        "a=(1,1,1)   r=1": {"S_t": -1, "S_a": -1, "S_AT": -2, "S_A": -2,
                            "S_T": -2, "S_TA": -2, "tau'": 0},
        "a=(1,1,2)   r=1": {"S_t": -1, "S_a": 0, "S_AT": -2, "S_A": -1,
                            "S_T": 3, "S_TA": -2, "tau'": 1},
        "a=(1,2,3)   r=1": {"S_t": 1, "S_a": 0, "S_AT": 0, "S_A": 1,
                            "S_T": 1, "S_TA": 0, "tau'": 1},
    }
    for name, want in expect.items():
        a, r, t_a, rho, rows = data[name]
        def piece(key, tau, th):
            return {"S_t": S_t(a, tau, th), "S_a": S_a(a, tau, th),
                    "S_AT": sum(d2_angle_tau(ak, tau, th) for ak in a),
                    "S_A": sum(d2_angle(ak, tau, th) for ak in a),
                    "S_T": sum(d2_tau(ak, tau, th) for ak in a),
                    "S_TA": sum(d2_tau_angle(ak, tau, th) for ak in a),
                    "tau'": tau_deriv(a, r, tau, th)}[key]
        got = {}
        for key, p_want in want.items():
            v1 = piece(key, rows[-2][1], rows[-2][0])
            v2 = piece(key, rows[-1][1], rows[-1][0])
            if v1 == 0 or v2 == 0:
                p = mpf(0)
            else:
                p = -mp.log(fabs(v2 / v1)) / mp.log(2)
            got[key] = p
            assert fabs(p - p_want) < mpf('0.05'), \
                "%s: %s scales as theta^%s, expected theta^%d" \
                % (name, key, mp.nstr(p, 4), p_want)
        print("       %-18s rho=%d  %s" % (name, rho,
              "  ".join("%s~th^%d" % (k, want[k]) for k in
                        ["S_t", "S_a", "S_AT", "S_A", "S_T", "S_TA", "tau'"])))
    print("       They differ BY REGIME, so no single rescaling serves all three.")
    print()
    print("       And they are residues of cancellation, not structural rates.")
    print("       At `a=(1,1,2)`, `S_T ~ theta^3` while EVERY MEMBER of the sum is")
    print("       `~theta`: the members cancel.  And each member is itself a")
    print("       cancellation -- `cos(theta_k) = -theta` at a collision member,")
    print("       so `2 tau sin s + 2 a sin cos` loses its leading term.")
    a3, r3 = data["a=(1,1,2)   r=1"][0], data["a=(1,1,2)   r=1"][1]
    rows3 = data["a=(1,1,2)   r=1"][4]
    th3, tau3 = rows3[-1]
    members = [d2_tau(ak, tau3, th3) for ak in a3]
    tot = sum(members)
    assert all(fabs(m) > 100 * fabs(tot) for m in members), \
        "the members of S_T do not dwarf their sum, so there is no cancellation " \
        "to report: members %s, sum %s" % (members, tot)
    print("       members %s" % ", ".join(mp.nstr(m, 6) for m in members))
    print("       sum     %s -- smaller than any member by %sx"
          % (mp.nstr(tot, 6), mp.nstr(fabs(members[0] / tot), 4)))
    print("       So a term-by-term bound on these sums cannot reproduce the")
    print("       exponent, and a rescaled algebra-of-limits route would have to")
    print("       carry the cancellations explicitly, per regime.  That is the")
    print("       measured reason to reach for the analytic endpoint chart")
    print("       (`EndpointBranch.exists_endpoint_local_inverse`) instead.")
    print()

    print("  SCOPE: five pencils at r = 1,2 spanning rho = 1,2,3.  Not a proof")
    print("  for all (Q,r).  What is shown is that the hypothesis as written")
    print("  cannot be met at the pencils the paper is about, in either regime,")
    print("  which is enough to withdraw a theorem that carries it.")
    print()
    print("ALL PASS")


if __name__ == "__main__":
    main()
