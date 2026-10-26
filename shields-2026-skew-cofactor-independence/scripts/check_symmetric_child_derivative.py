"""The derivative identity behind the symmetric upper bound.

Paper section `sec:restoration` (Common beta entries and first variations).

The argument for the upper bound differentiates a relation at the private generator h_N and
lands on the normalized child.  Everything it needs is the single identity

    dU_z / dh_N  =  (-1)^(n-1) * U^{C'}_{z-u}     for z > u,
    dU_z / dh_N  =  0                             for z < u,

where u = b_{n-1} and the child C' is C with its outer row and column deleted and both lists
shifted down by u:

    A'_p = a_{p+1} - u   (p = 1..n-1),      B'_q = b_q - u   (q = 1..n-1).

Checked here, exactly, on symmetric dense cores:

  (1) C' is again symmetric dense, of span N' = N - 2u, and its lists are normalized;
  (2) the derivative identity, at EVERY available position, with the sign;
  (3) the map z -> z - u is a bijection from the representatives of C above u onto the
      representatives of C', which is what lets the induction run on representatives;
  (4) the midpoint z = N/2 maps to the child midpoint, so the induction covers it rather than
      leaving it as a special case;
  (5) at order one the child units are the distinct monomials h_w h_{N'-w}, which is the base.

Finite evidence, corroboration only.  The proof it corroborates is algebraic and needs no census;
nothing here is a premise for anything in the paper.
"""

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_widen_containment import cofactors, omega, unit, fmt, is_symmetric  # noqa: E402
from check_symmetric_lower_bound import symmetric_dense_cores  # noqa: E402


def ddh(poly, k):
    """Partial derivative with respect to the generator h_k."""
    out = {}
    for mono, c in poly.items():
        mult = mono.count(k)
        if not mult:
            continue
        rest = list(mono)
        rest.remove(k)
        key = tuple(sorted(rest))
        out[key] = out.get(key, Fraction(0)) + c * mult
    return {k2: v for k2, v in out.items() if v}


def child(A, B):
    """C with the outer row and column deleted, both lists shifted down by u = b_{n-1}."""
    n = len(A)
    u = B[n - 2]
    return tuple(a - u for a in A[1:]), tuple(b - u for b in B[:-1]), u


def main():
    st = dict(cores=0, positions=0, ident=0, zero_below=0, bij=0, midpoints=0, order1=0)
    bad = []

    for n in (2, 3, 4):
        cores = symmetric_dense_cores(n, 14)
        print(f"order {n}: {len(cores)} symmetric dense cores")
        for A, B in cores:
            st["cores"] += 1
            N = A[0]
            Ac, Bc, u = child(A, B)
            Np = N - 2 * u

            # (1) the child is symmetric dense, normalized, of span N - 2u
            assert Ac[0] == Np, f"child span {Ac[0]} != {Np} on {A}{B}"
            assert Bc[-1] == 0, f"child not normalized on {A}{B}"
            assert Ac[-1] > Bc[0], f"child not dense on {A}{B}"
            assert is_symmetric(Ac, Bc), f"child not symmetric on {A}{B}"

            D = cofactors(A, B)
            Dc = cofactors(Ac, Bc)
            omC, omc = omega(A, B), omega(Ac, Bc)
            sign = Fraction((-1) ** (n - 1))

            # (2) the derivative identity at every available position
            for z in omC:
                d = ddh(unit(A, B, z, D), N)
                if z < u:
                    if d:
                        bad.append(("nonzero below u", A, B, z, fmt(d)))
                    else:
                        st["zero_below"] += 1
                else:
                    w = z - u
                    want = {} if w not in omc else {
                        k: sign * v for k, v in unit(Ac, Bc, w, Dc).items()}
                    if d == want:
                        st["ident"] += 1
                    else:
                        bad.append(("identity", A, B, z, fmt(d), fmt(want)))
                st["positions"] += 1

            # (3) representatives above u biject with child representatives
            repsC = sorted(z - u for z in omC if z > u and 2 * z <= N)
            repsc = sorted(w for w in omc if 2 * w <= Np)
            if repsC == repsc:
                st["bij"] += 1
            else:
                bad.append(("bijection", A, B, repsC, repsc))

            # (4) the midpoint maps to the child midpoint
            if N % 2 == 0 and (N // 2) in omC:
                st["midpoints"] += 1
                assert N // 2 > u, f"midpoint below u on {A}{B}"
                assert (N // 2) - u == Np // 2, f"midpoint does not map to child midpoint {A}{B}"

            # (5) at order one the child units are the distinct monomials h_w h_(N'-w)
            if len(Ac) == 1:
                for w in omc:
                    U = unit(Ac, Bc, w, Dc)
                    assert U == {tuple(sorted((w, Np - w))): Fraction(1)}, (
                        f"order-one unit is not h_w h_(N'-w) on {Ac}{Bc} at w={w}: {fmt(U)}")
                    st["order1"] += 1

    print()
    print("RESULTS")
    print(f"  symmetric dense cores              {st['cores']}")
    print(f"  positions examined                 {st['positions']}")
    print(f"  derivative identity verified       {st['ident']}")
    print(f"    with sign (-1)^(n-1)")
    print(f"  derivative zero for z < u          {st['zero_below']}")
    print(f"  representative bijection z -> z-u  {st['bij']} of {st['cores']}")
    print(f"  midpoints mapped to child midpoint {st['midpoints']}")
    print(f"  order-one base units checked       {st['order1']}")
    print(f"  failures                           {len(bad)}")
    for b in bad[:5]:
        print("     ", b)

    assert not bad, "the derivative identity or the bijection failed"
    assert st["cores"] >= 40 and st["ident"] >= 100, st
    assert st["midpoints"] >= 1, "no midpoint was ever exercised"
    assert st["order1"] >= 1, "the order-one base was never exercised"
    assert st["zero_below"] >= 1, "the z < u branch was never exercised"
    print("\n  non-vacuity: identity, midpoint, order-one base and the z < u branch all fired")
    print("\nALL PASS")


if __name__ == "__main__":
    main()
