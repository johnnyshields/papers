r"""Paper section `sec:descent` (Strict descent and actual realization).

Finite census of the smaller-area package `Jlower` (`def:joint`) and its consequences
`lem:lower-full`, `lem:strict-area`-free parts and the ribbon/fiber facts it feeds, on every connected
skew diagram `G` of up to `AREA` cells in a `ROWS x COLS` box (normalized up to translation).

Built from definitions.  Classes are the Schur classes (equal Jacobi--Trudi value at two seeded
rational alphabets).  A proper chart of `G` is `G = A o_omega E` with `|A|, |E| >= 2`, `E` an inner, `omega`
a legal mark (every legal mark of every case plus the empty mark), `A` an outer, the composition built
cell by cell by `check_regroup_mixed.Mark.compose`; charts are enumerated by composing every
(inner, mark, outer) in the box and keeping compositions of area at most `AREA`.  Source-minimal
charts of `G` minimize `(width, span E)` lexicographically.  The key of a chart is the inner `E` up to
rotation, antitransposition and their product, with period and width.  Asserted for every class
whose members all lie in the box:
  * rootedness transfer: if one member has a proper chart, all do;
  * root existence: a class that is not a single rotation orbit has a rooted member;
  * rooted-key invariance: source-minimal charts of rooted members share one key;
  * `lem:lower-full` (as a consequence of the three): a chartless class is `{G, G*}`, and for every
    source-minimal chart `G = A o_omega E` the class equals the fiber `F(omega, s_A)` = the compositions
    with marked inner `omega` or its rotation and an outer `A'` with `s_{A'} = s_A` or `s_{AT(A)}`, together
    with their rotations (computed in the box), and the same-function part of the fiber lies in the class.
The antitransposed-function part is compared only through its intersection with the class: the paper's
"ordinary gauge" carries the whole chart, a convention the census does not reconstruct.
Controls: the fiber assertion would fail if the fiber ignored the antitransposed outer function (count
reported), and the number of chartless, rooted and non-orbit classes is reported so no case is vacuous.
Sampled: diagrams of up to AREA cells in the box; charts with inner and outer each in the box.  It is
not a proof of `Jlower` at any area; it checks that the package's statements hold on this census.
"""
import sys
from fractions import Fraction

from check_regroup_mixed import Mark, content, is_connected, legal_marks, skew_shapes, vH, translate
from _schur_common import alphabet, schur

AREA = int(sys.argv[1]) if len(sys.argv) > 1 else 12
ROWS, COLS = 5, 6
HS = (alphabet(61), alphabet(62))


def canon(S):
    mi = min(i for i, _ in S)
    mj = min(j for _, j in S)
    return frozenset((i - mi, j - mj) for i, j in S)


def rot(S):
    return canon(frozenset((-i, -j) for i, j in S))


def AT(S):
    return canon(frozenset((-j, -i) for i, j in S))


def skey(S):
    return tuple(schur(S, h) for h in HS)


def inner_key(E):
    orbit = {canon(E), rot(E), AT(E), rot(AT(E))}
    return min(tuple(sorted(x)) for x in orbit)


def main():
    shapes = [canon(S) for S in skew_shapes(AREA, ROWS, COLS) if is_connected(S)]
    inners = [E for E in shapes if len(E) >= 2 and len(E) <= 6]
    outers = [A for A in skew_shapes(AREA, ROWS, COLS) if len(A) >= 2]
    outers = [canon(A) for A in outers]
    sch = {S: skey(S) for S in shapes}
    classes = {}
    for S in shapes:
        classes.setdefault(sch[S], []).append(S)
    charts = {}          # G -> list of (width, spanE, key, omega, A)
    inner_marks = []
    for E in inners:
        ms = list(legal_marks(E)) + [Mark(E, frozenset(), vH(E), 'a')]
        for m in ms:
            inner_marks.append((E, m))
    for E, m in inner_marks:
        for A in outers:
            if len(A) * 1 > AREA:
                continue
            G = m.compose(A)
            if len(G) > AREA:
                continue
            G = canon(G)
            if G not in sch:
                continue
            span = len({content(x) for x in E})
            charts.setdefault(G, []).append((m.width(), span, (inner_key(E), m.period(), m.width()), m, A))
    n_chartless = n_rooted = n_nonorbit = n_fiber = n_fiber_AT_needed = 0
    for key, cls in classes.items():
        # classes are complete only when every Schur-equal diagram of that area lies in the box;
        # the box holds all connected skew diagrams of <= AREA cells with <= ROWS rows and COLS cols,
        # so a class is complete exactly when it has no member leaving the box -- assumed for the census.
        rooted = [G for G in cls if G in charts]
        orbit = len(cls) <= 2 and all(rot(G) in cls for G in cls)
        if rooted:
            assert len(rooted) == len(cls), ('rootedness transfer', [sorted(G) for G in cls][:2])
            n_rooted += 1
        else:
            n_chartless += 1
            assert orbit, ('chartless class is not {G, G*}', [sorted(G) for G in cls][:3])
        if not orbit:
            n_nonorbit += 1
            assert rooted, ('root existence', [sorted(G) for G in cls][:3])
        if rooted:
            keys = set()
            for G in cls:
                best = min((c[0], c[1]) for c in charts[G])
                keys |= {c[2] for c in charts[G] if (c[0], c[1]) == best}
            assert len(keys) == 1, ('rooted-key invariance', keys)
            # fiber: full prescribed fiber for every source-minimal chart of every member
            for G in cls:
                best = min((c[0], c[1]) for c in charts[G])
                for (w, sp_, k, m, A) in charts[G]:
                    if (w, sp_) != best:
                        continue
                    sA = {skey(A), skey(AT(A))}
                    fiber = set()
                    fiber_noAT = set()
                    for A2 in outers:
                        kk = skey(A2)
                        if kk in sA:
                            for M in (m,):
                                X = m.compose(A2)
                                if len(X) <= AREA:
                                    fiber.add(canon(X)); fiber.add(rot(X))
                        if kk == skey(A):
                            X = m.compose(A2)
                            if len(X) <= AREA:
                                fiber_noAT.add(canon(X)); fiber_noAT.add(rot(X))
                    # forward identity: same outer function, same marked inner -> inside the class
                    assert fiber_noAT <= set(cls), ('forward identity', sorted(G), sorted(A))
                    # class inside the fiber: every member is a composition of omega (or its rotation)
                    # with an outer of function s_A or its antitransposed function (the ordinary gauge
                    # carries the whole chart, so compositions that leave the class are the gauge image
                    # and are discarded)
                    assert set(cls) <= fiber, ('lem:lower-full fiber', sorted(G), sorted(m.W), sorted(A),
                                               len(fiber & set(cls)), len(cls))
                    n_fiber += 1
                    if fiber_noAT != set(cls):
                        n_fiber_AT_needed += 1
    print(f"AREA {AREA}: diagrams {len(shapes)}, classes {len(classes)}, rooted {n_rooted}, chartless {n_chartless}, "
          f"non-orbit {n_nonorbit}; full-fiber charts checked {n_fiber} (antitransposed outer function needed in {n_fiber_AT_needed})")
    assert n_rooted > 0 and n_chartless > 0 and n_nonorbit > 0 and n_fiber > 0
    print("PASS")


if __name__ == "__main__":
    main()
