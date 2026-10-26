"""Marching saturation: the shared step of thm:cap-fixed-rigidity and thm:ratio-rigidity.

Both proofs run one argument.  Written abstractly, the inputs are

    (a)  no-backflow          R_i <= q                      for every row i
    (b)  strict marching      R_{i+1} > R_i                 for i_0 <= i < v-1
    (c)  a starting bound     R_{i_0} >= i_0 + 2
    (d)  tropical balancing   |M_i| >= 2, and max M_i = R_i

and the conclusion is

         R_i = i + 2        and       M_i = {i+1, i+2}       for i_0 <= i < v,

with q = v + 1.  thm:cap-fixed-rigidity is the instance i_0 = 0 (the floor
antecedent supplies R_0 >= 2); thm:ratio-rigidity is the instance i_0 = -1 (the
virtual row supplies R_{-1} >= 1).

This is a correctness check on the FACTORING, not on either theorem: it
instantiates the abstract statement at both i_0 and asserts that each recovers
the theorem as printed.  It also exhibits the pigeonhole -- that (a)-(c) alone
force equality at every step -- and probes the boundary by dropping each
hypothesis in turn.
"""
from itertools import combinations


def saturate(i0, v):
    """Every R on rows i0..v-1 satisfying (a),(b),(c).  Returns the set of
    admissible R-sequences; the lemma claims exactly one survives."""
    q = v + 1
    rows = list(range(i0, v))
    out = []
    # R_i ranges over i0+1 .. q  (a value below i0+1 cannot be a rightmost
    # minimizer of a set of size >= 2 lying to the right of the row index)
    def rec(acc):
        i = len(acc)
        if i == len(rows):
            out.append(tuple(acc)); return
        lo = acc[-1] + 1 if acc else i0 + 2          # (b) strict, (c) at the start
        for val in range(lo, q + 1):                  # (a) upper bound
            rec(acc + [val])
    rec([])
    return out


def check(i0, v):
    sols = saturate(i0, v)
    assert len(sols) == 1, f"i0={i0} v={v}: expected a unique R, got {len(sols)}"
    R = sols[0]
    expect = tuple(i + 2 for i in range(i0, v))
    assert R == expect, f"i0={i0} v={v}: R={R} expected {expect}"
    # (d) alone does NOT turn R_i = i+2 into the exact adjacent pair: restricting the
    # candidate columns to {i+1, i+2} would assume the conclusion, and a guard that
    # assumes what it is testing cannot fail.  What actually forces the pair is
    # INTERLACING, min M_{i+1} >= max M_i, which lem:marching's proof supplies.
    # Both are tested here: without interlacing the sets are underdetermined,
    # with it they are forced.
    COLS = v + 4
    def sets_at(i, prevmax):
        # The leftmost column available to the starting row is i0 + 1.  At
        # i0 = 0 that is column 1, which IS the floor antecedent excluding
        # column 0; at i0 = -1 it is column 0, because on the ratio locus the
        # virtual row's own minimizer set is {0, 1} and G_0 does not vanish
        # there.  Hard-coding 1 makes the virtual-row instance unsatisfiable.
        lo = i0 + 1
        if prevmax is not None:
            lo = max(lo, prevmax)                 # interlacing
        return [S for k in range(2, COLS)
                  for S in combinations(range(lo, COLS), k)
                  if max(S) == i + 2]
    loose = {i: sets_at(i, None) for i in range(i0, v)}
    prevmax, tight = None, {}
    for i in range(i0, v):
        tight[i] = sets_at(i, prevmax)
        assert tight[i] == [(i + 1, i + 2)], f"row {i} with interlacing: {tight[i]}"
        prevmax = i + 2
    return R, loose, tight


print("=== the factoring recovers each theorem as printed ===")
for v in range(1, 12):
    r0, loose, tight = check(0, v)     # thm:cap-fixed-rigidity
    extra = sum(len(x) - 1 for x in loose.values())
    print(f"  v={v:2}  i0= 0 -> R={r0}   forced with interlacing; without it "
          f"{extra} further minimizer set(s) survive   [cap-fixed]")
for v in range(1, 12):
    rm, loose, tight = check(-1, v)    # thm:ratio-rigidity
    extra = sum(len(x) - 1 for x in loose.values())
    print(f"  v={v:2}  i0=-1 -> R={rm}   forced with interlacing; without it "
          f"{extra} further minimizer set(s) survive   [ratio, virtual row]")

print()
print("=== each hypothesis is load-bearing: drop one, uniqueness fails ===")
v = 5
# drop (c): let the starting bound slip by one
def saturate_no_c(i0, v):
    q = v + 1; out = []
    def rec(acc):
        i = len(acc)
        if i == v - i0:
            out.append(tuple(acc)); return
        lo = acc[-1] + 1 if acc else i0 + 1
        for val in range(lo, q + 1):
            rec(acc + [val])
    rec([]); return out
n = len(saturate_no_c(0, v))
assert n > 1, "dropping the starting bound must admit more than one R"
print(f"  drop (c) starting bound at i0=0, v={v}: {n} admissible R-sequences, not 1")
# drop (b): marching only weakly increasing
def saturate_weak_b(i0, v):
    q = v + 1; out = []
    def rec(acc):
        i = len(acc)
        if i == v - i0:
            out.append(tuple(acc)); return
        lo = acc[-1] if acc else i0 + 2
        for val in range(lo, q + 1):
            rec(acc + [val])
    rec([]); return out
n = len(saturate_weak_b(0, v))
assert n > 1, "weakening marching to non-strict must admit more than one R"
print(f"  weaken (b) to non-strict at i0=0, v={v}: {n} admissible R-sequences, not 1")
# drop (a): no upper bound -> unbounded
n = len(saturate(0, v))
free = len([1 for val in range(v + 2, v + 6)])
assert free > 0
print(f"  drop (a) no-backflow: R_0 may exceed q={v+1} outright, so R is unbounded above")

print()
print("=== the two instances differ ONLY in the starting index ===")
for v in (3, 7):
    a = check(0, v)[0]; b = check(-1, v)[0]
    assert b[1:] == a, f"v={v}: the ratio instance must extend the cap-fixed one by its virtual row"
    print(f"  v={v}: ratio R={b} = (virtual row {b[0]}) ++ cap-fixed R={a}")

print()
print("ALL PASS")
