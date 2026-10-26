r"""Paper section `sec:response` (The complete scalar and its second channel).

Complement dual of an ordinary cap template (`prop:clocks`: on a return band (I, C) to
(K \\ C, K \\ I), K = {0, ..., c}).

Formalized in `SkewRibbonPeriod/Main/FilterWindows/DualTemplate.lean`.  For every ordinary
(row or column) template over a small core, the dual keeps the strict core and the active indices,
replaces the common units by the vacancies and exchanges row and column.  Asserts, by exhaustive
enumeration, that every list of the dual is the complement in K of the exchanged list of the
original and that the upper and lower cap heights coincide.
"""
import itertools

def lists(c, I0, C0, Z, ZL, sigma, tau, kind):
    refR, refC = I0 | Z, C0 | Z
    lowR, lowC = I0 | ZL, C0 | ZL
    capR = refR | {sigma} if kind == "row" else refR
    capC = refC if kind == "row" else refC - {sigma}
    lcr = lowR - {tau} if kind == "col" else lowR
    lcc = lowC if kind == "col" else lowC | {tau}
    return refR, refC, lowR, lowC, capR, capC, lcr, lcc

def upper(capR, capC, u):
    return len([x for x in capR if x > u]) - len([x for x in capC if x > u])

def lower(lcc, lcr, u):
    return len([x for x in lcc if x <= u]) - len([x for x in lcr if x <= u])

def check(c):
    K = set(range(c + 1))
    n = 0
    for k in range(0, 3):
        for I0 in map(set, itertools.combinations(sorted(K), k)):
            rest = K - I0
            for C0 in map(set, itertools.combinations(sorted(rest), k)):
                vac = rest - C0
                for Z in map(set, itertools.chain.from_iterable(
                        itertools.combinations(sorted(vac), m) for m in range(len(vac) + 1))):
                    for ZL in (set(), set(sorted(vac)[:1]), vac):
                        for kind in ("row", "col"):
                            for sigma in K:
                                for tau in K:
                                    # activity
                                    if kind == "row":
                                        if sigma in I0 | Z or tau in C0 | ZL:
                                            continue
                                    else:
                                        if sigma not in C0 | Z or tau not in I0 | ZL:
                                            continue
                                    n += 1
                                    L = lists(c, I0, C0, Z, ZL, sigma, tau, kind)
                                    dZ = K - I0 - C0 - Z
                                    dZL = K - I0 - C0 - ZL
                                    dk = "col" if kind == "row" else "row"
                                    D = lists(c, I0, C0, dZ, dZL, sigma, tau, dk)
                                    refR, refC, lowR, lowC, capR, capC, lcr, lcc = L
                                    dR, dC, dlR, dlC, dcR, dcC, dlcr, dlcc = D
                                    assert dR == K - refC and dC == K - refR
                                    assert dlR == K - lowC and dlC == K - lowR
                                    assert dcR == K - capC and dcC == K - capR
                                    assert dlcr == K - lcc and dlcc == K - lcr
                                    for u in range(-1, c + 1):
                                        assert upper(dcR, dcC, u) == upper(capR, capC, u)
                                        assert lower(dlcc, dlcr, u) == lower(lcc, lcr, u)
    return n

if __name__ == "__main__":
    total = sum(check(c) for c in range(1, 5))
    assert total > 1000, total
    print("dual template checks:", total, "PASS")
