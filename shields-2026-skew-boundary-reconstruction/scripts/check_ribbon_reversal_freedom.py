"""Paper section `sec:application` (The seam chain and the composition problem): factor reversal is strictly coarser than reversal of the whole diagram.

A ribbon is recorded by its composition of row lengths.  Equality of ribbon
Schur functions is decided by reversal of the factors in the unique
irreducible factorization under the composition product

    alpha o beta = beta^{(*)alpha_1} . beta^{(*)alpha_2} . ... ,

where "." is concatenation of compositions and "(*)" is the near
concatenation that adds the adjoining parts.  This script confirms, by
exact expansion in the complete homogeneous basis, that reversing one
factor of a two-factor composition can produce a partner which is neither
the original composition nor its reverse.  Hence the orientation freedom
left by a serial seam chain is genuinely factor-wise, and cannot be
tightened to a single global reversal.

Route: r_alpha = sum over coarsenings beta of alpha of
(-1)^(l(alpha)-l(beta)) h_beta, expanded as a signed dictionary on
weakly decreasing subscript multisets.
"""

from itertools import product


def coarsenings(alpha):
    """All compositions obtained by merging adjacent parts of alpha."""
    n = len(alpha)
    for bits in product([0, 1], repeat=max(n - 1, 0)):
        out, cur = [], alpha[0]
        for i, b in enumerate(bits):
            if b:
                cur += alpha[i + 1]
            else:
                out.append(cur)
                cur = alpha[i + 1]
        out.append(cur)
        yield tuple(out)


def ribbon(alpha):
    """r_alpha in the h-basis, as {sorted subscript multiset: coefficient}."""
    exp = {}
    for beta in coarsenings(alpha):
        key = tuple(sorted(beta, reverse=True))
        exp[key] = exp.get(key, 0) + (-1) ** (len(alpha) - len(beta))
    return {k: v for k, v in exp.items() if v}


def near(a, b):
    return a[:-1] + (a[-1] + b[0],) + b[1:]


def npow(beta, k):
    out = beta
    for _ in range(k - 1):
        out = near(out, beta)
    return out


def compose(alpha, beta):
    out = ()
    for part in alpha:
        out = out + npow(beta, part)
    return out


def rev(alpha):
    return tuple(reversed(alpha))


def compositions(n):
    if n == 0:
        yield ()
        return
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            yield (first,) + rest


# --- the composition product is the one BTvW define ---------------------
assert compose((1, 2), (1, 2)) == (1, 2, 1, 3, 2)
assert compose((1, 2), (3,)) == (3, 6)
assert compose((3,), (1, 2)) == (1, 3, 3, 2)
assert compose((1,), (2, 1)) == (2, 1)
assert rev(compose((1, 2), (1, 2))) == compose(rev((1, 2)), rev((1, 2)))

# --- the named witness -------------------------------------------------
a, b = (1, 2), (1, 2)
lhs = compose(a, b)
rhs = compose(rev(a), b)
assert lhs == (1, 2, 1, 3, 2) and rhs == (1, 3, 2, 1, 2)
assert ribbon(lhs) == ribbon(rhs), "reversing one factor must preserve r"
assert rhs != lhs and rhs != rev(lhs), "and must not be a global reversal"
print("witness   %s ~ %s   with reverse %s" % (lhs, rhs, rev(lhs)))
print("  r =", sorted(ribbon(lhs).items(), reverse=True))

# --- exhaustive: the smallest composition admitting the phenomenon ------
found = []
for n in range(1, 11):
    tab = {}
    for al in compositions(n):
        tab.setdefault(tuple(sorted(ribbon(al).items())), []).append(al)
    for cls in tab.values():
        for al in cls:
            extra = [c for c in cls if c != al and c != rev(al)]
            if extra:
                found.append((n, al, sorted(extra)[0]))
    if found:
        break
assert found, "no factor-reversal pair found at all, which contradicts BTvW"
n0 = found[0][0]
assert n0 == 9, "expected the smallest instance at size 9, got %d" % n0
mins = sorted(set((x, y) for _, x, y in found))
print("smallest size with the phenomenon: %d, %d ordered pairs" % (n0, len(mins)))
for x, y in mins:
    assert ribbon(x) == ribbon(y) and y != rev(x)
    print("  %s ~ %s   (reverse of the first is %s)" % (x, y, rev(x)))

# --- equality classes at size 9 are at most factor reversal -------------
tab = {}
for al in compositions(9):
    tab.setdefault(tuple(sorted(ribbon(al).items())), []).append(al)
sizes = sorted({len(v) for v in tab.values()})
assert sizes == [1, 2, 4], "unexpected class sizes at size 9: %s" % sizes
print("class sizes at size 9:", sizes)

# --- the file's infinite family also works, and it is not minimal -------
for m in range(2, 7):
    e = (1, 2) + (1,) * m
    x, y = compose((1, 2), e), compose((2, 1), e)
    assert ribbon(x) == ribbon(y)
    assert y != x and y != rev(x)
print("family (1,2) o (1,2,1^m) vs (2,1) o (1,2,1^m) verified for m = 2..6")

print("ALL PASS")
