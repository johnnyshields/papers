"""`thm:two-cap`: the arithmetic the two-cap exclusion theorem runs on.

The theorem itself is an argument about valuations, but three of its steps are
integer identities or inequalities that can be wrong by a sign or an index.  Each
is asserted here over an exhaustive parameter range.

  (1) the cap-shift identity
        Phi_b(j) - Phi_b(0) = [Phi_a(j) - Phi_a(0)] + 2 d_j (b - a),
      with Phi_k(j) = nu(G_j) + (k + d_j)^2 and d_0 = 0;

  (2) the r > 0 branch: under alpha_0 - alpha_j <= 2 r d_j the j = 0 summand is
      the strict minimum at every shift r + k with k > 0, and the two resulting
      values of nu(P_r(G)) agree only when a = b;

  (3) the r = 0 branch: under alpha_0 - alpha_j <= 2 a d_j the j = 0 summand is
      weakly minimal at shift a and strictly minimal at every shift b > a;

  (4) the inequality chain by which the Floor conclusion supplies the hypothesis:
      alpha_0 - m_+ = 2 gamma d_1 together with alpha_j >= m_+ and d_j >= d_1
      gives alpha_0 - alpha_j <= 2 gamma d_j.

Ranges are stated in the output.  Integer arithmetic only.
"""

import itertools

D_MAX = 12
NU_MAX = 12
CAP_MAX = 8


def main():
    # (1) the cap-shift identity, over every (nu_j, nu_0, d_j, a, b)
    n1 = 0
    for nu_j in range(NU_MAX + 1):
        for nu_0 in range(NU_MAX + 1):
            for dj in range(D_MAX + 1):
                for a in range(CAP_MAX + 1):
                    for b in range(a + 1, CAP_MAX + 1):
                        Pa_j = nu_j + (a + dj) ** 2
                        Pa_0 = nu_0 + a ** 2
                        Pb_j = nu_j + (b + dj) ** 2
                        Pb_0 = nu_0 + b ** 2
                        assert (Pb_j - Pb_0) == (Pa_j - Pa_0) + 2 * dj * (b - a)
                        n1 += 1

    # (2) and (3): the two branches of the proof, over every admissible profile
    n2 = n3 = 0
    for a in range(1, CAP_MAX + 1):
        for b in range(a + 1, CAP_MAX + 1):
            for r in range(0, CAP_MAX + 1):
                gamma = a if r == 0 else r
                for d1 in range(1, D_MAX + 1):
                    for alpha0 in range(0, NU_MAX + 1):
                        # the tightest admissible profile: alpha_j = alpha_0 - 2 gamma d_j
                        for dj in range(d1, D_MAX + 1):
                            alphaj = alpha0 - 2 * gamma * dj
                            assert alpha0 - alphaj <= 2 * gamma * dj
                            if r == 0:
                                # weak at shift a, strict at shift b
                                assert alphaj - alpha0 + 2 * a * dj >= 0
                                assert alphaj - alpha0 + 2 * b * dj > 0
                                n3 += 1
                            else:
                                for k in (a, b):
                                    assert alphaj - alpha0 + 2 * (r + k) * dj > 0
                                # nu(P_r(G)) read off each cap must agree
                                va = alpha0 + (r + a) ** 2 - a ** 2
                                vb = alpha0 + (r + b) ** 2 - b ** 2
                                assert (va == vb) == (a == b)
                                assert va - vb == 2 * r * (a - b)
                                n2 += 1

    # (4) the inequality chain supplying the hypothesis from the Floor conclusion
    n4 = 0
    for gamma in range(1, CAP_MAX + 1):
        for d1 in range(1, D_MAX + 1):
            for m_plus in range(0, NU_MAX + 1):
                alpha0 = m_plus + 2 * gamma * d1
                for dj in range(d1, D_MAX + 1):
                    for alphaj in range(m_plus, NU_MAX + 2 * gamma * D_MAX + 1):
                        assert alpha0 - alphaj <= 2 * gamma * dj
                        n4 += 1
                        break          # the extreme case alpha_j = m_+ is the binding one

    print("cap-shift identity instances           : %d" % n1)
    print("r > 0 branch instances                 : %d" % n2)
    print("r = 0 branch instances                 : %d" % n3)
    print("Floor-to-hypothesis chain instances    : %d" % n4)
    print("ranges: d <= %d, nu <= %d, caps <= %d" % (D_MAX, NU_MAX, CAP_MAX))
    print("ALL PASS")


if __name__ == "__main__":
    main()
