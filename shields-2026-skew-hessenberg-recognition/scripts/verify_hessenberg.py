"""Exact independent checks of profiles, exposure data, and balanced inverses.

All accepted polynomial identities use complete symbolic polynomials.  Integer
specializations are not used to certify equality.  These finite tests corroborate,
but are not premises of, the uniform arguments in the paper.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product


def add(out, monomial, coefficient):
    out[monomial] += coefficient
    if not out[monomial]:
        del out[monomial]


def betas(rows, gaps):
    assert len(gaps) + 1 == len(rows)
    assert all(0 <= c < min(a, b) for a, b, c in zip(rows, rows[1:], gaps))
    x, y = [rows[-1]], [0]
    for a, c in zip(reversed(rows[:-1]), reversed(gaps)):
        yi = x[-1] - c
        y.append(yi)
        x.append(yi + a)
    return tuple(reversed(x)), tuple(reversed(y))


def determinant(x, y):
    """Subset determinant recurrence, retaining every monomial and its sign."""
    @lru_cache(None)
    def go(mask):
        i = mask.bit_count()
        if i == len(x):
            return {(): 1}
        out = Counter()
        for j, b in enumerate(y):
            if mask >> j & 1 or x[i] < b:
                continue
            d = x[i] - b
            sgn = (-1) ** ((mask >> (j + 1)).bit_count())
            for mon, coeff in go(mask | (1 << j)).items():
                add(out, tuple(sorted(mon + ((d,) if d else ()))), sgn * coeff)
        return dict(out)
    return go(0)


def interval(rows, gaps):
    out = Counter()
    n = len(rows)
    for bits in range(1 << (n - 1)):
        labels = []
        span = rows[0]
        sign = 1
        for i, c in enumerate(gaps):
            if bits >> i & 1:
                if c:
                    labels.append(c)
                span += rows[i + 1] - c
                sign *= -1
            else:
                labels.append(span)
                span = rows[i + 1]
        labels.append(span)
        add(out, tuple(sorted(labels)), sign)
    return dict(out)


def composite(rows, gaps, alpha):
    r, g = list(rows), list(gaps)
    joins = {sum(alpha[:i]) for i in range(1, len(alpha))}
    for i in range(1, sum(alpha)):
        if i in joins:
            g += [0] + list(gaps)
            r += list(rows)
        else:
            r[-1] += rows[0]
            r += list(rows[1:])
            g += list(gaps)
    return tuple(r), tuple(g)


def compositions(n):
    for cuts in range(1 << (n - 1)):
        a, last = [], 0
        for j in range(1, n):
            if cuts >> (j - 1) & 1:
                a.append(j - last)
                last = j
        yield tuple(a + [n - last])


def data(rows, gaps):
    x, y = betas(rows, gaps)
    S, p = x[0], rows[0] - gaps[0]
    assert rows[-1] - gaps[-1] == p
    A, B = {a + p for a in x[2:]}, set(y[:-2])
    J = A & B
    return S, p, A - J, B - J, J


def core(S, p, P, Q, M, K):
    U = {M*S+p, M*S} | {k*S for k in K}
    V = {0, p} | {k*S+p for k in K}
    U |= {j*S+a for j in range(M) for a in P}
    V |= {j*S+b for j in range(M) for b in Q}
    return tuple(sorted(U, reverse=True)), tuple(sorted(V, reverse=True))


def coefficient(f, label, power=1):
    return {tuple(x for x in mon if x != label): c
            for mon, c in f.items() if mon.count(label) == power}


def sorted_diagonal(U, V):
    u, v = sorted(U), sorted(V)
    assert len(u) == len(v)
    assert all(a > b for a, b in zip(u, v)), (u, v)
    return Counter(a-b for a, b in zip(u, v))


def decoder(f, S, M):
    """Quadratic two-arm reconstruction, independent of the supplied cut set."""
    support = {j for mon in f for j in range(1, M) if j*S in mon}
    if not support:
        return frozenset()
    d = min(support)
    fd = coefficient(f, d*S)
    if not coefficient(f, d*S, 2):
        return frozenset(M-j for mon in fd for j in range(1, M) if j*S in mon)
    doubles, singles = set(), []
    for i in range(1, M//2+1):
        if coefficient(f, i*S, 2):
            doubles |= {i, M-i}
        elif i != M-i and any(i*S in mon for mon in fd):
            singles.append(i)
    if singles:
        first = singles[0]
        doubles.add(first)
        ff = coefficient(f, first*S)
        for j in singles[1:]:
            doubles.add(M-j if any(j*S in mon for mon in ff) else j)
    return frozenset(doubles)


def tests():
    families = [((3,9,4),(1,2)), ((3,4,5,3),(1,1,1)),
                ((2,4,2),(1,1)), ((3,3,7,5),(1,1,3)),
                ((4,6,7,4),(3,1,3)), ((2,3,6,4),(1,1,3))]
    identities = tomography = geometry = ratios = 0
    for rows, gaps in families:
        assert determinant(*betas(rows,gaps)) == interval(rows,gaps)
        identities += 1
        S,p,P,Q,J = data(rows,gaps)
        for M in range(1,5):
            for alpha in compositions(M):
                r,g = composite(rows,gaps,alpha)
                x,y = betas(r,g)
                xp = tuple(a+p for a in x)
                T = {sum(alpha[i:]) for i in range(1,len(alpha))}
                K = set(range(1,M))-T
                expected_contacts = {j*S+a for j in range(M) for a in J}
                expected_contacts |= {k*S for k in T}|{k*S+p for k in T}
                assert set(xp)&set(y) == expected_contacts
                U,V=core(S,p,P,Q,M,K)
                assert set(xp)-expected_contacts == set(U)
                assert set(y)-expected_contacts == set(V)
                assert len(U)==len(V) and not set(U)&set(V)
                assert all(U[i+1]>V[i] for i in range(len(U)-1))
                geometry += 1
                # Independent full parent determinant checks at bounded board size.
                if len(x)<=10:
                    parent=determinant(xp,y)
                    f=determinant(U,V)
                    degree=min(map(len,parent))
                    low={mon:c for mon,c in parent.items() if len(mon)==degree}
                    sign=(-1)**sum(i+j for a in expected_contacts
                                    for i in [xp.index(a)+1] for j in [y.index(a)+1])
                    assert low=={mon:sign*c for mon,c in f.items()}
                    recovered=decoder(f,S,M)
                    assert recovered in (frozenset(K),frozenset(M-k for k in K))
                    tomography+=1
                if len(P)>=2 and P and Q:
                    P0,Q0=sorted(P),sorted(Q)
                    Ps={S+p-b for b in Q}; Qs={S+p-a for a in P}
                    Us,Vs=core(S,p,Ps,Qs,M,K)
                    for k in K-{M-a for a in K}:
                        lhs=sorted_diagonal(set(U)-{k*S},set(V)-{0})
                        rhs=sorted_diagonal(set(Us)-{k*S},set(Vs)-{0})
                        expected=Counter({})
                        expected.update([P0[0]-p,S+p-Q0[-1]])
                        expected.subtract([S-Q0[-1],P0[0]])
                        lhs.subtract(rhs)
                        assert +lhs == +expected and +(-lhs)==+(-expected)
                        ratios+=1
    print(f'PASS: {identities} independent interval/determinant identities; '
          f'{geometry} complete balanced beta/contact checks; '
          f'{tomography} full-polynomial signed lowest-component and decoder checks; '
          f'{ratios} direct boundary-cofactor ratios.')
    print('ALL PASS')

if __name__=='__main__':
    tests()
