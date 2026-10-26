r"""Paper section `sec:response` (`lem:sum-horizon`, `lem:boolean`, `prop:clocks`, reverse ordered case).

Numeric side conditions of the interchanged deck: the template sits at period index b, the ordinary
zero at the horizon index a > b, the Hall zero at (a + b) g, with coprime a > b >= 2, N = L g + r,
0 < r < g, 2a <= L (the hard domain, eq:horizon-bounds).  Checked on every such tuple:
  - the sum horizon a' = N - (a+b) g - r exceeds r and is at least (a - b) g  (lem:sum-horizon);
  - the horizon band [h g, h g + r] and its top diagonal lie inside [0, L g) for h in {a, a+b},
    so the g-periodic heights shift by (a-b) g stays below L g (strictness at the larger horizon);
  - the cap clock (L - a) g + sigma - tau is positive for 0 <= sigma, tau <= r  (lem:boolean).
Run: nice taskset -c 4 timeout 600 python3 check_reverse_deck.py
"""
from math import gcd

count = 0
for g in range(2, 9):
    for r in range(1, g):
        for b in range(2, 9):
            for a in range(b + 1, 14):
                if gcd(a, b) != 1:
                    continue
                for L in range(2 * a + 1, 2 * a + 6):
                    N = L * g + r
                    ap = N - (a + b) * g - r
                    assert ap > r, (g, r, a, b, L)
                    assert ap >= (a - b) * g, (g, r, a, b, L)
                    for h in (a, a + b):
                        assert h < L and (h * g + r) < N
                    shift_top = (L - a) * g + (a - b) * g
                    assert shift_top < L * g
                    for sg in (0, r):
                        for tu in (0, r):
                            assert (L - a) * g + sg - tu > 0
                    count += 1
assert count > 0
print("OK", count)
