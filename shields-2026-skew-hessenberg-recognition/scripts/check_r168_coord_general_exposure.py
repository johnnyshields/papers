"""Coordinator's independent check of lane H's general-inner (EXPOSURE) (round 168).

CLAIM (r168-h.md): for a connected zero-free inner E, no Hessenberg assumption, with
E_m = E^{merger m} rotation-rigid for the parts m of alpha and for m = |alpha|,
    Cl(F_alpha(E)) = {F_beta(E), F_beta(E)* : r_beta = r_alpha}.
H's non-Hessenberg family: E_g = (2g+1, g+2, g+2; g, g), g even, g >= 4.

CONSTRUCTION, rebuilt from the definitions stated in r168-h.md, not from H's code:
    E = (a, I, b; G)  ->  E_m = (a, I, (a+b, I)^{m-1}, b; G^m),
    F_alpha = E_{alpha_1} .0 E_{alpha_2} .0 ...   (zero-gap joins).

MECHANISM: the arrangement enumerator of check_r168_coord_separated_support.py.
Row- and gap-multisets are Schur invariants, so every connected mate is an
arrangement; random-point evaluation mod 2^61 - 1 separates the rest rigorously.
The class is computed in full and compared with the predicted set as SETS.

Assertions:
  (1) E_g is connected, zero-free, and NOT Hessenberg (some lambda_i - mu_j - i + j
      >= 0 with i > j + 1), for g = 4, 6.
  (2) The rigidity inputs E_1, E_2, E_3 at g = 4 are rotation-rigid.
  (3) For alpha in a list including nonsymmetric, symmetric and three-part
      compositions, the computed class equals the predicted class exactly.
      Ribbon classes are taken from BTvW on these small compositions: r_beta = r_alpha
      iff beta in {alpha, reverse(alpha)} for every composition of length <= 3 used here.
  (4) CONTROL that must FIRE: replacing the predicted class by {F_alpha, F_alpha*}
      is rejected wherever alpha is not a palindrome.
"""
from check_r168_coord_separated_support import (arrangements, det_mod, POINTS,
                                                betas, rot, zero_free)


def power(E, m):
    rows, gaps = E
    a, I, b = rows[0], list(rows[1:-1]), rows[-1]
    R = [a] + I
    for _ in range(m - 1):
        R += [a + b] + I
    R += [b]
    return tuple(R), tuple(gaps) * m


def F(E, alpha):
    rows, gaps = [], []
    for k, m in enumerate(alpha):
        r, g = power(E, m)
        if k:
            gaps.append(0)
        rows += r
        gaps += g
    return tuple(rows), tuple(gaps)


def schur_class(src):
    sig = [det_mod(*src, pt) for pt in POINTS]
    return {c for c in arrangements(*src)
            if all(det_mod(*c, pt) == s for pt, s in zip(POINTS, sig))}


def hessenberg(rows, gaps):
    x, y = betas(rows, gaps)
    n = len(rows)
    return all(x[i] - y[j] < 0 for i in range(n) for j in range(n) if i > j + 1)


def main():
    for g in (4, 6):
        E = ((2 * g + 1, g + 2, g + 2), (g, g))
        assert zero_free(*E) and not hessenberg(*E), g
        print(f"PASS (1): E_{g} = {E} is connected, zero-free, not Hessenberg")

    E4 = ((9, 6, 6), (4, 4))
    for m in (1, 2, 3):
        Em = power(E4, m)
        assert schur_class(Em) == {Em, rot(*Em)}, (m, "power not rigid")
        print(f"PASS (2): E_4^(m={m}) = {Em} ({sum(Em[0])} cells) is rotation-rigid")

    fired = 0
    cases = [(4, (1, 2)), (4, (2, 2)), (4, (1, 3)), (4, (1, 1, 2)), (4, (1, 2, 1)), (6, (1, 2))]
    for g, alpha in cases:
        E = ((2 * g + 1, g + 2, g + 2), (g, g))
        src = F(E, alpha)
        betas_ = {alpha, tuple(reversed(alpha))}
        predicted = set()
        for b in betas_:
            predicted |= {F(E, b), rot(*F(E, b))}
        got = schur_class(src)
        assert got == predicted, (g, alpha, sorted(got ^ predicted)[:4])
        print(f"PASS (3): g={g} alpha={alpha} ({sum(src[0])} cells): class has exactly the "
              f"{len(predicted)} predicted members")
        if alpha != tuple(reversed(alpha)):
            assert got != {src, rot(*src)}, "CONTROL DID NOT FIRE"
            fired += 1
    assert fired >= 3
    print(f"PASS (4, control fires): the rotation-only prediction is rejected on {fired} cases")
    print("ALL PASS")


if __name__ == "__main__":
    main()
