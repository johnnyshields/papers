r"""Paper section `sec:fold` (Finite synchronization and the legal gcd chart).

Targets `lem:cycles` and the arithmetic of `eq:cycle-budget`.

`lem:cycles` is checked exhaustively on bounded parameters: for every `p, q` with
`1 <= q <= p <= 8` and every interval of `p + q + e` consecutive integers (`e = 0, 1, 2`), every
`p`-periodic binary word on it (all `2^p` of them, built from their `p` free values) satisfying
`u(k+q) <= u(k)` on the interval, or the reverse inequality, is `gcd(p, q)`-periodic on it.
The interval length `p + q` is also shown sharp: on an interval of length `p + q - 1` a
`p`-periodic word with the monotone inequality that is not `gcd`-periodic exists for some
`(p, q)`.  `eq:cycle-budget` is the integer arithmetic `p - q >= g >= c + 1  =>  2p - c - 1 >= p + q`
over every `g, c, L`; its first inequality `N - 2c - 1 >= 2p - c - 1` needs `N >= 2p + c`, which
is a hypothesis of the original problem and is not derived here.
"""
from itertools import product
from math import gcd

PMAX = 8


def periodic_word(bits, p, length):
    return [bits[k % p] for k in range(length)]


def monotone(u, q, direction):
    return all((u[k + q] <= u[k]) if direction < 0 else (u[k + q] >= u[k]) for k in range(len(u) - q))


def gcd_periodic(u, g):
    return all(u[k + g] == u[k] for k in range(len(u) - g))


def main():
    checked = 0
    sharp = False
    for p in range(1, PMAX + 1):
        for q in range(1, p + 1):
            g = gcd(p, q)
            for extra in (0, 1, 2):
                length = p + q + extra
                for bits in product((0, 1), repeat=p):
                    u = periodic_word(bits, p, length)
                    for direction in (-1, 1):
                        if monotone(u, q, direction):
                            assert gcd_periodic(u, g), (p, q, bits, direction)
                            checked += 1
            if g < p:
                for bits in product((0, 1), repeat=p):
                    u = periodic_word(bits, p, p + q - 1)
                    if monotone(u, q, -1) and not gcd_periodic(u, g):
                        sharp = True
    assert checked > 0 and sharp
    # eq:cycle-budget arithmetic
    n = 0
    for g in range(1, 7):
        for c in range(1, g):
            for pm in range(1, 8):
                for qm in range(1, pm):
                    p, q = pm * g, qm * g
                    if p - q >= g and g >= c + 1:
                        assert 2 * p - c - 1 >= p + q
                        n += 1
    assert n > 0
    print(f"monotone words checked {checked}; length p+q-1 is not enough (sharp); budget cases {n}")
    print("PASS")


if __name__ == "__main__":
    main()
