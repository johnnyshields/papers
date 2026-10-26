"""Paper section `subsec:locus-family`.  Target labels: `prop:staircase-reversal`.

The specialization bridge of the reversal proposition.

check_abstract_reversal_identity.py verifies the two-series lemma on
generic coefficients.  This script verifies the three steps that carry that lemma
onto the actual capped boards, which is where the boundary hypothesis enters:

  (1)  even cap grid:   P_r(C(w)) = D(r, w)          for w_0 = 2,
  (2)  the ratio quantity:  F(w) := h_1 P_2 - P_3 = D(1, 2, w),
  (3)  the specialization  alpha_i = h_{2i},  beta_i = h_{2i+1}  carries the word
       matrix M_w of the abstract lemma onto D(1,2,w), so  det M_w = F(w),

with D(rho) = det( h_{rho_i + 2(j-i)} ).

Step (3) consumes the FULL word at length l = N, not the interior at l = N-2.
That distinction is recorded because getting it wrong is silent: the interior
encoding produces a matrix of the wrong size and agrees with F(w) on no word at
all, which looks like a refutation of the lemma rather than a mis-transcription.

The boundary letter is needed TWICE -- once for w so that (1) applies, and once
for w^* so that (1) applies to the reversed word as well.  That is exactly the
hypothesis w_0 = w_{N-1} = 2, and the negative control below shows what happens
without it.
"""

import itertools
import sys
import sympy as sp

H = {}


def h(k):
    if k < 0:
        return sp.Integer(0)
    if k == 0:
        return sp.Integer(1)
    if k not in H:
        H[k] = sp.Symbol("h%d" % k)
    return H[k]


def board(w):
    N = len(w)
    mu = list(range(N - 1, -1, -1))
    return [w[i] + mu[i] for i in range(N)], mu


def cofactors(w):
    lam, mu = board(w)
    n = len(lam)
    L = lam[0]
    A = [L - lam[i] + i for i in range(n)]
    d = [0] + [L - mu[j - 1] + j - 1 for j in range(1, n + 1)]
    M = sp.Matrix(n, n + 1, lambda i, j: h(d[j] - A[i]))
    C = [sp.expand(sp.Integer(-1) ** j
                   * M[:, [c for c in range(n + 1) if c != j]].det(method="berkowitz"))
         for j in range(n + 1)]
    return C, d


def P(w, r):
    C, d = cofactors(w)
    return sp.expand(sum(C[j] * h(r + d[j]) for j in range(len(C))))


def F(w):
    return sp.expand(h(1) * P(w, 2) - P(w, 3))


def D(rho):
    n = len(rho)
    return sp.expand(sp.Matrix(n, n,
                     lambda i, j: h(rho[i] + 2 * (j - i))).det(method="berkowitz"))


def alpha(i):
    return h(2 * i) if i >= 0 else sp.Integer(0)


def beta(i):
    return h(2 * i + 1) if i >= 0 else sp.Integer(0)


def M_word(x):
    """Rows: B, A, then X_{x_i} shifted right by i.  Columns 0..l+1."""
    l = len(x)
    rows = [[beta(c) for c in range(l + 2)], [alpha(c) for c in range(l + 2)]]
    for i, ch in enumerate(x, start=1):
        f = beta if ch == "B" else alpha
        rows.append([f(c - i) for c in range(l + 2)])
    return sp.Matrix(rows)


def encode(w):
    return tuple("A" if c == 2 else "B" for c in w)


NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
print("Specialization bridge, boundary-2 words, N = 4..%d\n" % NMAX)

for N in range(4, NMAX + 1):
    n1 = n2 = n3 = n4 = tot = 0
    pairs = held = 0
    for interior in itertools.product((2, 3), repeat=N - 2):
        w = [2] + list(interior) + [2]
        tot += 1
        n1 += all(sp.expand(P(w, r) - D([r] + w)) == 0 for r in (2, 3))
        n2 += sp.expand(F(w) - D([1, 2] + w)) == 0
        n3 += sp.expand(M_word(encode(w)).det(method="berkowitz") - F(w)) == 0
        ws = w[::-1]
        if w != ws:
            pairs += 1
            held += sp.expand(F(w) - F(ws)) == 0
    print("  N=%d  (%2d words)   P_r=D(r,w): %2d   F=D(1,2,w): %2d   "
          "det M_w=F(w): %2d   |   F(w)=F(w*) on %2d/%2d pairs"
          % (N, tot, n1, n2, n3, held, pairs))
    assert n1 == n2 == n3 == tot, N
    assert held == pairs, N

print("\nNEGATIVE CONTROL -- the interior encoding (l = N-2) that looks right and is not:")
bad = 0
for interior in itertools.product((2, 3), repeat=3):
    w = [2] + list(interior) + [2]
    if sp.expand(M_word(encode(interior)).det(method="berkowitz") - F(w)) != 0:
        bad += 1
print("  %d of 8 interior-encoded words disagree with F(w)  (expected 8)" % bad)
assert bad == 8

print("\nNEGATIVE CONTROL -- boundary letter 3 breaks step (1), hence the chain:")
broke = 0
tot3 = 0
for interior in itertools.product((2, 3), repeat=3):
    w = [3] + list(interior) + [3]
    tot3 += 1
    if sp.expand(P(w, 2) - D([2] + w)) != 0:
        broke += 1
print("  %d of %d boundary-3 words already fail P_2 = D(2,w)" % (broke, tot3))
assert broke == tot3

print("\nALL PASS")
