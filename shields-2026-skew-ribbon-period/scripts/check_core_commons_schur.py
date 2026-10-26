r"""Paper section `app:aligned` (`prop:noncell-realization`): is s_S a function of (s_core(S), commons)?

For every connected skew shape S of area <= 9 the script forms core(S) (beta lists with the common
betas removed from both lists) and records (s_core, sorted common betas, span); it asserts that this
triple determines s_S.
"""
from check_common_betas_original import schur, shapes_c, det_mod, hval
from check_substitute_source import from_lists
from check_row_probe_caps import betas


def core(S):
    X, Y = betas(S)
    c = set(X) & set(Y)
    xs = sorted([x for x in X if x not in c], reverse=True)
    ys = sorted([y for y in Y if y not in c], reverse=True)
    return xs, ys, sorted(c)


def main():
    seen = {}
    n = bad = 0
    for A in range(2, 10):
        for S in shapes_c(A):
            xs, ys, c = core(S)
            # the core as a diagram: rebuild with commons removed but the span kept (bits)
            X, Y = betas(S)
            sc = tuple(det_mod([[hval(t, x - y) for y in ys] for x in xs]) for t in range(2))
            key = (sc, tuple(c), X[0])
            n += 1
            s = schur(S)
            if key in seen and seen[key] != s:
                bad += 1
            seen.setdefault(key, s)
    print("shapes", n, "keys", len(seen), "violations", bad)
    assert bad == 0


if __name__ == "__main__":
    main()
