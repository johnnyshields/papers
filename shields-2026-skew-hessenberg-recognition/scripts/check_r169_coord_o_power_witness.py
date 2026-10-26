"""Coordinator check of lane O's witness E = (3,4,3,6,4;1^4) (round 169).

CLAIM (O, progress update): E is nonrigid, while E^m is rigid whenever gcd(m-1, 15) = 1,
so total-merger rigidity is strictly weaker than P(E).  Checked here at m = 1, 2 over the
FULL mate space (every arrangement of rows and gaps; row/gap multisets are Schur invariants),
by random evaluation mod 2^61-1.  Asserts: E has a nonrotation mate (this also serves as the
firing control of the mate finder); E^2 is rotation-rigid.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_r168_coord_separated_support import nonrotation_mates
from check_r168_coord_general_exposure import power

E = ((3, 4, 3, 6, 4), (1, 1, 1, 1))
n, extra = nonrotation_mates(*E)
assert extra, "E expected NONRIGID, but no nonrotation mate found"
print(f"PASS: E = {E} ({sum(E[0])} cells) is nonrigid: {len(extra)} nonrotation match(es) among {n} arrangements, e.g. {extra[0]}")
E2 = power(E, 2)
n, extra = nonrotation_mates(*E2)
assert not extra, ("E^2 expected rigid", extra[:3])
print(f"PASS: E^2 = {E2} ({sum(E2[0])} cells) is rotation-rigid against all {n} arrangements")
print("ALL PASS")
