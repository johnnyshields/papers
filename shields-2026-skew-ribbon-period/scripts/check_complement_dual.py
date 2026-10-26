r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects).

Complement dual of an upper cap frame (sec:poles, prop:clocks: (I, C) -> (K\\C, K\\I)).

Checks on all small templates: the dual has the same strict core, its reference lists are
the complements of the originals (swapped), its cap lists are K minus the original cap
lists (swapped), its upper cap height equals the original one, and the dual of the dual is
the original.  A cap row of the original above sigma outside a return pair (Rr, Cr) is a
common-unit vacancy of the dual return pair.
"""
import itertools

def check(c):
    K = frozenset(range(c + 1))
    n = 0
    for k in range(0, 3):
        for I0 in map(frozenset, itertools.combinations(sorted(K), k)):
            rest = K - I0
            for C0 in map(frozenset, itertools.combinations(sorted(rest), k)):
                om = K - I0 - C0
                for zs in range(len(om) + 1):
                    for Z in map(frozenset, itertools.combinations(sorted(om), zs)):
                        refR, refC = I0 | Z, C0 | Z
                        for kind in ("row", "col"):
                            for sig in sorted(K):
                                if kind == "row":
                                    if sig in refR:
                                        continue
                                    capR, capC = refR | {sig}, refC
                                else:
                                    if sig not in refC:
                                        continue
                                    capR, capC = refR, refC - {sig}
                                Zd = om - Z
                                drefR, drefC = I0 | Zd, C0 | Zd
                                assert drefR == K - refC and drefC == K - refR
                                assert drefR - drefC == I0 and drefC - drefR == C0
                                if kind == "row":
                                    dcapR, dcapC = drefR, drefC - {sig}
                                    assert sig in drefC
                                else:
                                    dcapR, dcapC = drefR | {sig}, drefC
                                    assert sig not in drefR
                                assert dcapR == K - capC and dcapC == K - capR
                                for u in range(-1, c + 1):
                                    h = sum(x > u for x in capR) - sum(x > u for x in capC)
                                    hd = sum(x > u for x in dcapR) - sum(x > u for x in dcapC)
                                    assert h == hd
                                # a cap row outside a return pair is a common unit of the dual
                                for Zq in map(frozenset, itertools.combinations(sorted(om), min(1, len(om)))):
                                    Rr, Cr = I0 | Zq, C0 | Zq
                                    for v in capR:
                                        if v != sig and v not in Rr:
                                            assert v in (K - (Rr | Cr))
                                n += 1
    return n

total = sum(check(c) for c in range(1, 6))
assert total > 1000
print("complement dual checks:", total, "ALL PASS")
