#!/usr/bin/env python3
"""Paper sections `sec:preliminaries` (Profiles, cuts, and ribbon substitution)
and `sec:saturation-proof` (The repeated-block inverse); results
`lem:seam-coefficients`, `lem:ribbon-endpoints`.

Check distinguished-gap coefficients without a largest-gap assumption.

Exact full permutation determinants are independent of the interval expansion
used in the proof.  The bounded sweep permits uncut gaps on either side of the
chosen value, adjacent chosen seams, absent chosen seams, and one-row inputs.
A separate positional check exercises the minimal two-row inner and repeated
numeric row labels without making any assertion of class-search completeness.
"""

from collections import defaultdict
from itertools import permutations, product


def valid(profile):
    rows, gaps = profile
    return bool(rows) and len(gaps) + 1 == len(rows) and all(r > 0 for r in rows) and all(
        0 <= g < min(rows[i], rows[i + 1]) for i, g in enumerate(gaps)
    )


def hessenberg(profile):
    rows, gaps = profile
    return valid(profile) and all(rows[i] > gaps[i - 1] + gaps[i]
                                  for i in range(1, len(rows) - 1))


def schur(profile):
    assert valid(profile)
    rows, gaps = profile
    n = len(rows)
    x, y = [0] * n, [0] * n
    x[-1] = rows[-1]
    for i in range(n - 2, -1, -1):
        y[i] = x[i + 1] - gaps[i]
        x[i] = y[i] + rows[i]
    answer = defaultdict(int)
    for perm in permutations(range(n)):
        indices = [x[i] - y[perm[i]] for i in range(n)]
        if any(j < 0 for j in indices):
            continue
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        answer[tuple(sorted(j for j in indices if j))] += sign
    return {mon: coef for mon, coef in answer.items() if coef}


def multiply(left, right):
    answer = defaultdict(int)
    for a, u in left.items():
        for b, v in right.items():
            answer[tuple(sorted(a + b))] += u * v
    return {mon: coef for mon, coef in answer.items() if coef}


def coefficient(poly, variable, exponent):
    return {tuple(j for j in mon if j != variable): value
            for mon, value in poly.items() if mon.count(variable) == exponent}


def cut(profile, d):
    rows, gaps = profile
    pieces, start = [], 0
    for i, gap in enumerate(gaps):
        if gap == d:
            pieces.append((rows[start:i + 1], gaps[start:i]))
            start = i + 1
    pieces.append((rows[start:], gaps[start:]))
    return pieces


def contract(profile, d):
    rows, gaps = profile
    output, remaining = [], []
    current = rows[0]
    for gap, row in zip(gaps, rows[1:]):
        if gap == d:
            current += row - d
        else:
            output.append(current)
            remaining.append(gap)
            current = row
    output.append(current)
    return tuple(output), tuple(remaining)


def extremes(profile, d):
    assert hessenberg(profile)
    assert all(row > d for row in profile[0])
    pieces, contracted = cut(profile, d), contract(profile, d)
    assert all(hessenberg(piece) for piece in pieces)
    assert hessenberg(contracted)
    expected = {(): 1}
    for piece in pieces:
        expected = multiply(expected, schur(piece))
    power = profile[1].count(d)
    merged = schur(contracted)
    assert all(d not in mon for mon in expected)
    assert all(d not in mon for mon in merged)
    polynomial = schur(profile)
    assert coefficient(polynomial, d, 0) == expected
    assert coefficient(polynomial, d, power) == {
        mon: (-1) ** power * value for mon, value in merged.items()
    }


def compositions(total):
    if total == 0:
        yield ()
    else:
        for first in range(1, total + 1):
            for tail in compositions(total - first):
                yield (first,) + tail


def assembled(a, middle, b, c, d, alpha):
    rows, gaps = (), ()
    z, k = a + b - d, len(middle) + 2
    for m in alpha:
        if rows:
            gaps += (d,)
        rows += (a,) + middle + ((z,) + middle) * (m - 1) + (b,)
        gaps += (c,) * (m * (k - 1))
    return rows, gaps


def split_by_positions(total, sizes, a, b, d):
    """Reconstruct from contracted rows and component row counts only."""
    rows, gaps = total
    cuts, position = set(), 1
    for size in sizes[:-1]:
        position += size - 1
        cuts.add(position)
    out_rows, out_gaps = [], []
    for position, row in enumerate(rows, 1):
        if position > 1:
            out_gaps.append(gaps[position - 2])
        if position in cuts:
            assert row == a + b - d
            out_rows.extend((b, a))
            out_gaps.append(d)
        else:
            out_rows.append(row)
    return tuple(out_rows), tuple(out_gaps)


def check_positions():
    count = 0
    for c in range(3):
        for d in (c + 1, c + 2):
            for a, b in product((c + d + 1, c + d + 2), repeat=2):
                for length in range(4):
                    minimum = max(2 * c, d) + 1
                    interiors = {(), (minimum,), (minimum, minimum),
                                 (minimum, minimum + 1),
                                 (minimum, minimum + 1, minimum),
                                 (a + b - d,) * length}
                    for middle in sorted(x for x in interiors if len(x) == length):
                        k = len(middle) + 2
                        for total in range(2, 7):
                            for alpha in compositions(total):
                                parent = assembled(a, middle, b, c, d, alpha)
                                assert hessenberg(parent)
                                merged = contract(parent, d)
                                assert merged == assembled(a, middle, b, c, d, (total,))
                                sizes = tuple(m * (k - 1) + 1 for m in alpha)
                                assert split_by_positions(merged, sizes, a, b, d) == parent
                                count += 1
    print(f"PASS positional reconstruction: {count} profiles, including empty interiors,")
    print("zero inner gaps, minimal endpoints, symmetric inners, and merger-row collisions")


def main():
    # A non-largest chosen gap: direct 3-by-3 expansion is an independent control.
    profile = ((4, 5, 6), (1, 2))
    assert schur(profile) == {(4, 5, 6): 1, (1, 6, 8): -1,
                             (2, 4, 9): -1, (1, 2, 12): 1}
    extremes(profile, 1)
    cases = larger = adjacent = absent = 0
    for d in (1, 2, 3):
        for n in range(1, 5):
            for rows in product(range(d + 1, d + 4), repeat=n):
                for gaps in product(range(4), repeat=n - 1):
                    profile = rows, gaps
                    if not hessenberg(profile):
                        continue
                    extremes(profile, d)
                    cases += 1
                    larger += d in gaps and any(g > d for g in gaps)
                    adjacent += any(gaps[i] == gaps[i + 1] == d for i in range(len(gaps) - 1))
                    absent += d not in gaps
    assert larger and adjacent and absent
    # The retained row bound is substantive: here a diagonal carries h_1 too.
    invalid = ((1, 3, 4), (0, 1))
    rhs = {(): 1}
    for piece in cut(invalid, 1):
        rhs = multiply(rhs, schur(piece))
    assert coefficient(schur(invalid), 1, 0) != rhs
    try:
        extremes(invalid, 1)
    except AssertionError:
        pass
    else:
        raise AssertionError("row-bound rejecting control failed")
    print(f"PASS distinguished gaps: {cases} profiles; {larger} with an uncut larger gap;")
    print(f"{adjacent} with adjacent chosen seams; {absent} with no chosen seam")
    print("PASS rejecting control: dropping the row bound destroys the coefficient identity")
    check_positions()
    print("ALL PASS")


if __name__ == "__main__":
    main()
