"""Exact finite checks of the component budget and overlap minimum formula.

The assertions are diagnostics for the manuscript's noncomputational proofs.
No external packages are required.
"""


def partitions(total, cap=None):
    if total == 0:
        yield ()
        return
    if cap is None:
        cap = total
    for first in range(min(cap, total), 0, -1):
        for tail in partitions(total - first, first):
            yield (first,) + tail


def cross_cost(parts):
    return sum(a * b for i, a in enumerate(parts) for b in parts[i + 1:])


def negative_shape(x, y):
    return tuple(t for t in reversed([sum(a < b for b in y) for a in x]) if t)


def minimum(rho):
    return 1 + max((part + i for i, part in enumerate(rho, 1)), default=0)


def realizing_lists(rho, n):
    padded = rho + (0,) * (n - len(rho))
    t = padded[::-1]
    x = tuple((n + 1) * (n - t[i]) - i - 1 for i in range(n))
    y = tuple((n + 1) * (n - j - 1) for j in range(n))
    return x, y


def check():
    allowed_six = {(5, 1): 5, (4, 2): 8, (3, 3): 9, (4, 1, 1): 9}
    actual = {p: cross_cost(p) for p in partitions(6)
              if len(p) >= 2 and cross_cost(p) <= 9}
    assert actual == allowed_six, actual
    for m in range(7, 17):
        actual = {p: cross_cost(p) for p in partitions(m)
                  if len(p) >= 2 and cross_cost(p) <= 9}
        expected = {(m - 1, 1): m - 1} if m <= 10 else {}
        assert actual == expected, (m, actual)
        for p in partitions(m):
            if len(p) >= 3:
                assert cross_cost(p) >= 2 * m - 3
            if len(p) == 2 and min(p) >= 2:
                assert cross_cost(p) >= 2 * (m - 2)
    for m in range(7, 15):
        actual = {p: cross_cost(p) for p in partitions(m)
                  if len(p) >= 2 and cross_cost(p) <= 10}
        expected = {(m - 1, 1): m - 1} if m <= 11 else {}
        if m == 7:
            expected[(5, 2)] = 10
        assert actual == expected, ('ten-negative high minimum', m, actual)
        if m == 7:
            try:
                assert actual == {(6, 1): 6}
            except AssertionError:
                print('CONTROL REJECTED: omitting the dense two-plus-five component split')
            else:
                raise AssertionError('Ten-negative component control did not fire')
    for total in range(1, 11):
        for rho in partitions(total):
            nmin = minimum(rho)
            for n in range(nmin, nmin + 3):
                x, y = realizing_lists(rho, n)
                assert all(x[i] > x[i + 1] and y[i] > y[i + 1]
                           for i in range(n - 1))
                assert all(x[i] > y[i] for i in range(n))
                assert all(x[i + 1] > y[i] for i in range(n - 1))
                assert negative_shape(x, y) == rho
                cofactor_connected = all(x[i + 2] > y[i] for i in range(n - 2))
                assert cofactor_connected == (n > nmin)
                assert negative_shape(x[1:], y[:-1]) == rho
                counts = []
                first = None
                for k in range(2, n + 1):
                    overlaps = [max(0, x[j + k - 1] - y[j] + k - 1)
                                for j in range(n - k + 1)]
                    count = sum(t <= k - 2 for t in overlaps)
                    counts.append(count)
                    if count and first is None:
                        first = k
                assert sum(counts) == total
                assert n + 3 - first == nmin
                # Homogenization preserves negative sites and creates no zero.
                assert all((2 * a + 1 - 2 * b < 0) == (a - b < 0)
                           for a in x for b in y)
                assert all(2 * a + 1 != 2 * b for a in x for b in y)


if __name__ == "__main__":
    check()
    print("PASS: nine- and ten-negative component budgets, realizability, overlap minimum, and homogenization diagnostics")
    print("ALL PASS")
