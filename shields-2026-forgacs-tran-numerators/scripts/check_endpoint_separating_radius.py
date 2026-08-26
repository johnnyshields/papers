"""The separating circle at the lower endpoint (`sec:dominance`, the retained-cluster
group of `thm:weighted-dominance`: `haR₀`, `huniq₀`, `hCbd₀`).

The pencil is `D(t,z) = Q(t) + z t^r` with `Q = c∏(a_k - t)`, every `a_k > 0` and
`x₁ = min a_k` carried `ρ` times.  A radius `R₀` separates the cluster from the rest
of the spectrum when `x₁ < R₀ < min{a_k : a_k ≠ x₁}`.  Three claims are checked, each
with a failing assert:

1.  On `‖t‖ = R₀` the elementary bound `|Q(t)| ≥ |c| d^n` holds, where
    `d = min(R₀ - x₁, m - R₀)` and `m = min{a_k : a_k ≠ x₁}`.  This is the estimate
    the Lean proof uses in place of a compactness argument, since `|a_k - t| ≥
    ||t| - a_k| = |R₀ - a_k|`.
2.  For `|z| ≤ |c| d^n / (2 R₀^r)` the circle is zero-free, with `|D| ≥ |c| d^n / 2`.
3.  In the open disk `‖t‖ < R₀` the pencil has exactly `ρ` roots for such `z`, and
    they are distinct once `z ≠ 0` — the counting the retained cluster's cardinality
    `n₀ = ρ - 2` rests on.

The separating quantity is the RATIO `m / x₁`, not any numeral: the radius is chosen
inside `(x₁, m)` and every bound above scales with `x₁`.
"""

import mpmath as mp

mp.mp.dps = 40


def q_eval(c, a, t):
    v = mp.mpf(c) if not isinstance(c, mp.mpc) else c
    for ak in a:
        v = v * (mp.mpf(ak) - t)
    return v


def separating_data(c, a, r):
    x1 = min(a)
    rest = [ak for ak in a if ak != x1]
    m = min(rest) if rest else x1 + 1
    R0 = (mp.mpf(x1) + mp.mpf(m)) / 2
    d = min(R0 - mp.mpf(x1), mp.mpf(m) - R0)
    floor = abs(mp.mpf(c)) * d ** len(a)
    w = floor / (2 * R0 ** r)
    return x1, m, R0, d, floor, w


def min_on_circle(c, a, R0, samples=4000):
    best = None
    for j in range(samples):
        t = R0 * mp.exp(2j * mp.pi * mp.mpf(j) / samples)
        v = abs(q_eval(c, a, t))
        if best is None or v < best:
            best = v
    return best


def roots_in_disk(c, a, r, z, R0):
    # D(t,z) = Q(t) + z t^r in the monomial basis, highest degree first
    coeffs = [mp.mpf(c)]
    for ak in a:
        new = [mp.mpf(0)] * (len(coeffs) + 1)
        for i, p in enumerate(coeffs):
            new[i] += -p                 # (-t) * p t^k
            new[i + 1] += mp.mpf(ak) * p  # ak * p t^k
        coeffs = new
    n = len(coeffs) - 1
    if z != 0:
        idx = n - r
        assert 0 <= idx < len(coeffs), "r exceeds deg Q; the degree jump is a separate case"
        coeffs[idx] += z
    rts = mp.polyroots(coeffs, maxsteps=200, extraprec=400)
    return [t for t in rts if abs(t) < R0], rts


def main():
    cases = [
        (1.0, [1.0, 1.0, 1.0, 2.0], 1, 3),
        (1.0, [1.0, 1.0, 1.0, 2.0], 2, 3),
        (2.5, [0.4, 0.4, 1.7, 3.1], 1, 2),
        (1.0, [1.0, 1.0], 1, 2),
        (0.7, [2.0, 2.0, 2.0, 2.0, 5.0], 3, 4),
    ]
    for c, a, r, rho in cases:
        x1, m, R0, d, floor, w = separating_data(c, a, r)
        assert sum(1 for ak in a if ak == x1) == rho, "case declares the wrong multiplicity"
        assert x1 < R0 < m, f"radius not separating: {x1} {R0} {m}"

        # 1. the elementary floor on the circle
        obs = min_on_circle(c, a, R0)
        assert obs >= floor, f"|Q| floor violated on |t|={R0}: {obs} < {floor}"

        # 2. zero-free circle, with the halved floor
        for zz in [w, -w, w * 1j, -w * 0.37j, mp.mpf(0)]:
            worst = None
            for j in range(2000):
                t = R0 * mp.exp(2j * mp.pi * mp.mpf(j) / 2000)
                v = abs(q_eval(c, a, t) + zz * t ** r)
                if worst is None or v < worst:
                    worst = v
            assert worst >= floor / 2, f"|D| below half the floor: {worst} < {floor / 2}"

        # 3. exactly rho roots inside, distinct for z != 0
        for zz in [w, w / 10, w / 1000, w * 0.61j]:
            inside, _ = roots_in_disk(c, a, r, zz, R0)
            assert len(inside) == rho, f"count {len(inside)} != rho {rho} at z={zz}"
            gaps = [abs(inside[i] - inside[j])
                    for i in range(len(inside)) for j in range(i + 1, len(inside))]
            if gaps:
                assert min(gaps) > 1e-12, f"cluster members collided at z={zz}"

        print(f"c={c} a={a} r={r}: x1={x1} m={m} ratio={mp.nstr(mp.mpf(m) / x1, 6)} "
              f"R0={mp.nstr(R0, 6)} floor={mp.nstr(floor, 6)} minQ={mp.nstr(obs, 6)} "
              f"w={mp.nstr(w, 6)} count={rho}")

    print("PASS: check_endpoint_separating_radius")


if __name__ == "__main__":
    main()
