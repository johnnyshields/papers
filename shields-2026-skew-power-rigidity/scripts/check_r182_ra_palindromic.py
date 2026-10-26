"""Independent cut-coefficient and inflation-lowering checks for r181-u.

No author's checker or recorded-class census is used.  Cut sets are enumerated
as subsets, independently of the determinant implementation.  Exact integer
polynomials have h_0=1.  Controls reject a sign error, support-only recovery,
omitted degree/equality filters in lowering, and the reverse no-escape inference.
"""
from collections import Counter, defaultdict
from itertools import product
from time import monotonic
from check_r174_ra_proof_steps import betas, poly, cell_permutation

START = monotonic()

def say(text):
    print(f'{monotonic()-START:.2f}s {text}', flush=True)

def cuts(alpha):
    out, total = [], 0
    for a in alpha[:-1]:
        total += a
        out.append(total)
    return tuple(out)

def composition(M, positions):
    bounds = (0,)+tuple(sorted(positions))+(M,)
    return tuple(b-a for a, b in zip(bounds, bounds[1:]))

def coarsening(alpha):
    S = cuts(alpha)
    M, n = sum(alpha), len(alpha)
    out = Counter()
    for mask in range(1 << len(S)):
        gamma = composition(M, [z for i, z in enumerate(S) if mask >> i & 1])
        out[tuple(sorted(gamma))] += (-1)**(n-len(gamma))
    return {m: c for m, c in out.items() if c}

def two_piece(alpha):
    M, n = sum(alpha), len(alpha)
    if n == 1:
        return {}
    out = Counter(tuple(sorted((z, M-z))) for z in cuts(alpha))
    return {m: (-1)**(n-2)*c for m, c in out.items()}

def lower(pol, t, n, degree_filter=True, strict=False):
    if t == 0:
        return pol.copy()
    out = Counter()
    for mon, c in pol.items():
        if degree_filter and len(mon) != n:
            continue
        if not all(j > t if strict else j >= t for j in mon):
            continue
        out[tuple(j-t for j in mon if j != t)] += c
    return {m: c for m, c in out.items() if c}

def cut_fibers():
    count = Counter()
    for M in range(1, 15):
        fibers = defaultdict(list)
        for mask in range(1 << (M-1)):
            S = tuple(z for z in range(1, M) if mask >> (z-1) & 1)
            signature = tuple(sorted(Counter(min(z, M-z) for z in S).items()))
            fibers[signature].append(S)
            count['cut_sets'] += 1
        for signature, fiber in fibers.items():
            for S in fiber:
                if S != tuple(sorted(M-z for z in S)):
                    continue
                assert len(fiber) == 1
                recovered = set()
                for z, multiplicity in signature:
                    if 2*z == M:
                        assert multiplicity == 1
                        recovered.add(z)
                        count['central_cuts'] += 1
                    else:
                        assert multiplicity == 2
                        recovered.update((z, M-z))
                assert recovered == set(S)
                alpha = composition(M, S)
                assert alpha == alpha[::-1]
                count['palindromic_singleton_fibers'] += 1
        say(f'cut totals through weight {M}: {dict(count)}')
    # Same support, not same coefficient data: this rejects support alone,
    # not the stronger combination of support and the known row count.
    a, b = (1, 2, 1), (1, 3)
    assert set(two_piece(a)) == set(two_piece(b)) and two_piece(a) != two_piece(b)
    assert two_piece((1, 1, 1)) == {(1, 2): -2}
    assert two_piece((2, 2)) == {(2, 2): 1}
    say(f'cut counts={dict(count)}; support-only, sign, and central-position controls fire')

def determinant_and_lowering():
    fixtures = set()
    for length in range(3):
        for half in product((1, 2, 4), repeat=length):
            for middle in ((), (1,), (4,)):
                alpha = half+middle+half[::-1]
                if alpha:
                    fixtures.add(alpha)
    fixtures.update(((1, 3, 2, 2, 3, 1), (4, 1, 5, 1, 4),
                     (6, 7, 6), (9, 2, 4, 2, 9)))
    count = Counter()
    for alpha in sorted(fixtures):
        n = len(alpha)
        p = (alpha, (0,)*(n-1))
        A, B = betas(p)
        det = poly(A, B)
        assert det == coarsening(alpha)
        assert {m: c for m, c in det.items() if len(m) == 2} == two_piece(alpha)
        count['ribbon_determinants'] += 1
        for t in (0, 1, 4, 9):
            AA = tuple(a+t for a in A)
            inflated = poly(AA, B)
            assert lower(inflated, t, n) == det
            assert all(g+t < min(a+t, b+t) for g, a, b in zip(p[1], alpha, alpha[1:]))
            if n <= 5:
                shifted_profile = (tuple(a+t for a in alpha), (t,)*(n-1))
                assert cell_permutation(shifted_profile) == inflated
                count['independent_cell_determinants'] += 1
            count['lowering_identities'] += 1
            count['nonhessenberg_inflations'] += any(AA[i]-B[j] >= 0
                                                       for i in range(n) for j in range(i-1))
            if t:
                count['missing_degree_filter_controls'] += lower(inflated, t, n, degree_filter=False) != det
                count['discarded_h0_controls'] += lower(inflated, t, n, strict=True) != det
                count['inflated_common_beta_cases'] += bool(set(AA)&set(B))
        if count['ribbon_determinants'] % 12 == 0:
            say(f'lowering progress={dict(count)}')
    assert all(count[key] for key in ('missing_degree_filter_controls', 'discarded_h0_controls',
                                      'nonhessenberg_inflations', 'inflated_common_beta_cases'))
    # The live corollary is one-sided: an equality can split under inflation.
    a = ((1, 2, 1, 3, 2), (0,)*4)
    b = ((1, 3, 2, 1, 2), (0,)*4)
    A, B = betas(a)
    C, D = betas(b)
    assert poly(A, B) == poly(C, D) and a != b and a[0] != b[0][::-1]
    split = []
    for t in (1, 2, 4, 8):
        p = poly(tuple(x+t for x in A), B)
        q = poly(tuple(x+t for x in C), D)
        assert lower(p, t, 5) == lower(q, t, 5)
        if p != q:
            split.append(t)
    assert split
    say(f'determinant/lowering counts={dict(count)}; equal ribbons split at t={split}')

if __name__ == '__main__':
    cut_fibers()
    determinant_and_lowering()
    say('ALL PASS')
