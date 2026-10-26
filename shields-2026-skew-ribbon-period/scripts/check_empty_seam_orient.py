r"""Paper section `app:empty` (Empty overlaps and zero span remainder).

Orientation of the seam natives in `lem:empty-seams`, from row and column multisets.

For ribbons D (mu B cells), A_0 (A cells), C (mu A cells), B_0 (B cells), gcd(A, B) = 1,
A > B >= 2, with R_F = D o A_0 and R_H = C o B_0 (Billera--Thomas--van Willigenburg composition),
equal row multisets and equal column multisets force A_0 and B_0 to be lines in one orientation:
both rows or both columns.  Checked exhaustively over the stated boxes; then, on random larger
boxes, checks the closed form of the row multiset of D o beta used in the Lean proof:
  rows(D o beta) = k_D {b_1, b_l} + |D| {b_2..b_{l-1}} + (|D| - k_D) {b_1 + b_l}   (l >= 2)
                 = {|beta| d : d in D}                                             (l = 1).
"""
import itertools
import random
from collections import Counter


def compositions(n):
    for cuts in itertools.product([0, 1], repeat=n - 1):
        out, cur = [], 1
        for c in cuts:
            if c:
                out.append(cur)
                cur = 1
            else:
                cur += 1
        out.append(cur)
        yield tuple(out)


def near(a, b):
    return a[:-1] + (a[-1] + b[0],) + b[1:]


def comp(alpha, beta):
    out = ()
    for a in alpha:
        x = beta
        for _ in range(a - 1):
            x = near(x, beta)
        out += x
    return out


def conj(alpha):
    n = sum(alpha)
    cuts = set(itertools.accumulate(alpha[:-1]))
    tc = sorted(n - c for c in range(1, n) if c not in cuts)
    out, prev = [], 0
    for c in tc + [n]:
        out.append(c - prev)
        prev = c
    return tuple(out)


def closed_rows(D, beta):
    l = len(beta)
    if l == 1:
        return Counter(beta[0] * d for d in D)
    c = Counter()
    k, n = len(D), sum(D)
    c[beta[0]] += k
    c[beta[-1]] += k
    for b in beta[1:-1]:
        c[b] += n
    c[beta[0] + beta[-1]] += n - k
    return c


def key(R):
    return (tuple(sorted(R)), tuple(sorted(conj(R))))


def orient_ok(A0, B0):
    return (len(A0) == 1 and len(B0) == 1) or (len(conj(A0)) == 1 and len(conj(B0)) == 1)


def run(A, B, mu):
    left = {}
    for D in compositions(mu * B):
        for A0 in compositions(A):
            left.setdefault(key(comp(D, A0)), []).append((D, A0))
    hits, bad = 0, []
    for C in compositions(mu * A):
        for B0 in compositions(B):
            for (D, A0) in left.get(key(comp(C, B0)), []):
                hits += 1
                if not orient_ok(A0, B0):
                    bad.append((D, A0, C, B0))
    return hits, bad


if __name__ == '__main__':
    from math import gcd
    boxes = [(A, B, mu) for B in range(2, 6) for A in range(B + 1, 10) for mu in (1, 2, 3)
             if gcd(A, B) == 1 and mu * A <= 14]
    total = 0
    for (A, B, mu) in boxes:
        hits, bad = run(A, B, mu)
        total += hits
        assert not bad, (A, B, mu, bad[:3])
    print(f'orientation: {len(boxes)} boxes, {total} multiset-equal pairs, all one orientation')
    random.seed(3)
    for _ in range(3000):
        D = tuple(random.randint(1, 4) for _ in range(random.randint(1, 5)))
        beta = tuple(random.randint(1, 4) for _ in range(random.randint(1, 5)))
        assert Counter(comp(D, beta)) == closed_rows(D, beta), (D, beta)
    print('closed row multiset of D o beta: 3000 random cases pass')
