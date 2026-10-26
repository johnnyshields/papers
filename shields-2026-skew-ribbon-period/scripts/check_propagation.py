r"""Paper section `sec:geometry` (Periodic cores and actual boundary comparisons).

`lem:propagation`: if `A` has `T(D_1, v_1)` and `S = A o_zeta W` is a legal chart of period `d` and width `v_0`,
then `S` has `T(d D_1, d v_1 + v_0)`; the property is invariant under rotation and antitransposition; and
`T(D, v)` implies `T(hD, N mod hD)`.

`T(D, v)` for a connected diagram of span `N = L D + v`, `0 <= v < D`: both full boundary words are
`D`-periodic on the open middle `v < k < L D`, and the diagonals `v + jD`, `(j+1)D - 1` are singletons for
`0 <= j < L`.  Read literally from the beta lists.  The diagrams `A` are all small connected skew diagrams
with `T(D_1, v_1)` for some `D_1 >= 2`, `0 <= v_1 < D_1`, `L >= 2`; `S` is built from every legal mark of every
small inner.  The control: the conclusion fails for charts of `A` without `T(D_1, v_1)` (count reported), so the
hypothesis is load-bearing.  Sampled: `A` up to 8 cells, inners up to 5 cells.
"""
from check_regroup_mixed import legal_marks, skew_shapes, span, is_connected
from verify_charts import beta_lists, height_word
from check_phase_confinement import words


def has_T(S, D, v):
    N = span(S)
    if N < D or (N - v) % D:
        return False
    L = (N - v) // D
    if L < 1:
        return False
    a_w, b_w = words(S)
    for word in (a_w, b_w):
        for k in range(v + 1, L * D - D):
            if word[k] != word[k + D]:
                return False
    H = height_word(S)
    return all(H[v + j * D] == 1 and H[(j + 1) * D - 1] == 1 for j in range(L))


def antitranspose(S):
    c = frozenset((-j, -i) for i, j in S)
    mi = min(i for i, _ in c); mj = min(j for _, j in c)
    return frozenset((i - mi, j - mj) for i, j in c)


def main():
    outers = [A for A in skew_shapes(8, 4, 5) if is_connected(A) and len(A) >= 2]
    tags = {}
    for A in outers:
        N = span(A)
        for D1 in range(2, N):
            v1 = N % D1
            if N // D1 >= 2 and has_T(A, D1, v1):
                tags.setdefault(A, []).append((D1, v1))
    nprop = ncontrol = nrot = ngroup = 0
    for E in skew_shapes(5, 3, 3):
        if len(E) < 2:
            continue
        for m in legal_marks(E):
            d, v0 = m.period(), m.width()
            for A in outers:
                S = m.compose(A)
                for (D1, v1) in tags.get(A, []):
                    assert has_T(S, d * D1, d * v1 + v0), (sorted(E), sorted(m.W), sorted(A), D1, v1)
                    nprop += 1
                    assert has_T(antitranspose(S), d * D1, d * v1 + v0)
                    nrot += 1
                if A not in tags and span(A) >= 4:
                    for D1 in range(2, span(A)):
                        v1 = span(A) % D1
                        if not has_T(A, D1, v1) and not has_T(S, d * D1, d * v1 + v0):
                            ncontrol += 1
                            break
    for A, lst in tags.items():
        N = span(A)
        for (D, v) in lst:
            for h in (2, 3):
                if N // (h * D) >= 1:
                    assert has_T(A, h * D, N % (h * D)), (sorted(A), D, v, h)   # grouping
                    ngroup += 1
    print(f"propagated charts {nprop}, antitransposed {nrot}, grouped {ngroup}, controls (no T, conclusion fails) {ncontrol}")
    assert nprop > 0 and ncontrol > 0
    print("PASS")


if __name__ == "__main__":
    main()
