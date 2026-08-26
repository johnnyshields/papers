"""Does the shrinking deleted window remove the `hout` obstruction?

Earlier finding, against the FIXED window `cubicTheta M = {|t - pi/2| < 1}`:
the two complementary windows of `hout` must contain the deleted middle, of
length 2, so C2 >= 2(M+1)/pi and C2/d -> 2/pi = 0.6366, not 0.

`CubicMain.cubic_shrinkingWindow` replaces that by deleted windows of half-width
h/M: the two endpoint windows [0,h/M], [pi-h/M,pi] and the amplitude window
|t - pi/2| < h/M.  Total deleted measure 4h/M, not 2.

Setting, matching `ft_equidistribution` at r = 1: a = 0, b = pi, inner window
(alpha,beta) containing the deleted middle, so the two outer components are
exactly [h/M, alpha] and [beta, pi - h/M].  Each component's count is bounded
below by `cubic_phaseZeros_of_dominance`'s phase-free form

    (M - 1/2) * (length) / pi - 2.

C2 is then whatever makes

    (M+1)(b-a)/pi - (M+1)(beta-alpha)/pi - C2 <= Zlo.card + Zhi.card

hold.  Everything at 50 digits -- no float64 anywhere.
"""

import mpmath as mp

mp.mp.dps = 50


def c2_required(M, h, alpha, beta):
    """Smallest C2 making hout hold, at the construction actually built:
    outer components [e, alpha-e] and [beta+e, pi-e], e = h/M."""
    pi = mp.pi
    M = mp.mpf(M)
    e = h / M
    needed = (M + 1) * pi / pi - (M + 1) * (beta - alpha) / pi
    lo = (M - mp.mpf(1) / 2) * (alpha - 2 * e) / pi - 2
    hi = (M - mp.mpf(1) / 2) * (pi - beta - 2 * e) / pi - 2
    return needed - (lo + hi)


def c1_required(M, h, alpha, beta):
    """Smallest C1 making hin hold, at the same construction:
    inner components [alpha+e, pi/2-e] and [pi/2+e, beta-e]."""
    pi = mp.pi
    M = mp.mpf(M)
    e = h / M
    needed = (M + 1) * (beta - alpha) / pi
    lo = (M - mp.mpf(1) / 2) * (pi / 2 - e - (alpha + e)) / pi - 2
    hi = (M - mp.mpf(1) / 2) * (beta - e - (pi / 2 + e)) / pi - 2
    return needed - (lo + hi)


def c2_closed_form(M, h, alpha, beta):
    """The hand-derived closed form, to be checked against c2_required."""
    pi = mp.pi
    M = mp.mpf(M)
    return (mp.mpf(11) / 2 - (mp.mpf(3) / 2) * (beta - alpha) / pi
            + 4 * h * (M - mp.mpf(1) / 2) / (M * pi))


def main() -> None:
    pi = mp.pi
    h = mp.mpf(1) / 2          # any h > 0; the bound is uniform in it
    print(f"  h = {mp.nstr(h, 6)}, a = 0, b = pi, r = 1, d = M")

    print("\n  (1) the hand-derived closed form is exact")
    for M in (100, 1000, 10 ** 5):
        for (alpha, beta) in ((pi / 3, 2 * pi / 3), (pi / 4, 3 * pi / 4),
                              (pi / 2 - mp.mpf(1) / 5, pi / 2 + mp.mpf(1) / 5)):
            a = c2_required(M, h, alpha, beta)
            b = c2_closed_form(M, h, alpha, beta)
            assert abs(a - b) < mp.mpf("1e-40"), (M, alpha, beta, a, b)
    print("      c2_required == 11/2 - 3(beta-alpha)/(2 pi) + 4h(M-1/2)/(M pi)"
          "  to 40 digits, every case")

    print("\n  (2) C2 is BOUNDED in M, and C2/d -> 0")
    alpha, beta = pi / 3, 2 * pi / 3
    print("    M          C2 required        C2/d           old C2/d (fixed window)")
    for M in (100, 1000, 10 ** 4, 10 ** 5, 10 ** 6):
        c2 = c2_required(M, h, alpha, beta)
        old = (M + 1) * mp.mpf(2) / pi / M
        print(f"    {M:<10} {mp.nstr(c2, 12):<18} {mp.nstr(c2 / M, 10):<14} "
              f"{mp.nstr(old, 10)}")
    ratios = [c2_required(M, h, alpha, beta) / M
              for M in (100, 1000, 10 ** 4, 10 ** 5, 10 ** 6)]
    assert all(ratios[i] > ratios[i + 1] for i in range(len(ratios) - 1))
    assert ratios[-1] < mp.mpf("1e-5"), ratios[-1]
    print("      C2/d strictly decreasing, below 1e-5 at M = 1e6 -- the O(1/d)"
          " conclusion holds")

    print("\n  (3) the M-free bound 11/2 + 2h/pi covers every M and every window")
    cap = mp.mpf(11) / 2 + 4 * h / pi
    worst = mp.mpf(0)
    for M in (10, 100, 1000, 10 ** 4, 10 ** 5):
        for k in range(1, 20):
            alpha = pi / 2 - k * pi / 50
            beta = pi / 2 + k * pi / 50
            if alpha <= h / M:
                continue
            c2 = c2_required(M, h, alpha, beta)
            c1 = c1_required(M, h, alpha, beta)
            worst = max(worst, c2, c1)
            assert c2 <= cap, (M, k, c2, cap)
            assert c1 <= cap, (M, k, c1, cap)
    print(f"      cap 11/2 + 4h/pi = {mp.nstr(cap, 12)} covers BOTH C1 and C2;"
          f"  worst observed = {mp.nstr(worst, 12)}")
    assert worst <= cap

    print("\n  (4) the deleted measure, old vs new")
    print("    M          fixed window   shrinking window (4h/M)")
    for M in (10, 100, 1000, 10 ** 4):
        print(f"    {M:<10} {'2.0':<14} {mp.nstr(4 * h / M, 10)}")
    for M in (10, 100, 1000, 10 ** 4):
        assert 4 * h / M < 2

    print("\nALL PASS -- the 2/pi obstruction is GONE, not merely smaller.")


if __name__ == "__main__":
    main()
