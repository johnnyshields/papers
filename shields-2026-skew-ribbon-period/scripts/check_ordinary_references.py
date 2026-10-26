r"""Paper section `sec:geometry` (Periodic cores and actual boundary comparisons), the complete weak
return frames: `eq:ordinary-references`, `eq:reference-differences`.

Reading.  The paper calls B_R^*, B_L^* the "complete reference lists" of the original period-p
copies, and its proof compares "the cap's complete flag word with its actual p-translate".  The
reading tested: for a source S with full lists X = (N, I), Y = (C, 0), the caps are
U_cap = {c} u I_+, C_+, I_-, V_cap = {0} u C_- of the frame lists, and the reference lists are the
same windows read one period p lower:

    I_R^* = (X on [N-p-c, N-p]) - (N-p-c),   C_R^* = (Y on [N-p-c, N-p)) - (N-p-c),
    I_L^* = (X on [p, p+c]) - p,             C_L^* = (Y on [p, p+c]) - p.

The comparison of two Schur-equal charts is not needed to state this: it is a relation between a
single chart of period p and its own p-translate.  Instances are built backwards from the mark:
every connected J with at most J_CELLS cells and legal ordinary case (a) mark of period p and
width w > 0, every divisor g of p with c = w mod g > 0 (so p = Ag, w = d_p g + c, 0 < c < g), and
the compositions S = Row_M o J (row frame) and Col_M o J (column frame) for M = 2, 3.  Asserted on
every instance, exactly:

  (each identity is asserted on every instance satisfying the phase bounds of
  lem:phase-confinement, t <= c and w - s <= c for a row outer, s <= c and w - t <= c for a column
  outer; for a column outer it is asserted to fail exactly off them, which is the control showing
  the bounds are load-bearing; for a row outer instances off the bounds are skipped)
  row frame:     sigma = s - d_p g, tau = t,   I_R^* = U_cap minus {sigma},  C_R^* = C_+,
                 I_L^* = I_-,  C_L^* = V_cap minus {tau};
  column frame:  sigma = t - d_p g, tau = s,   I_R^* = U_cap,  C_R^* = C_+ plus {sigma},
                 I_L^* = I_- plus {tau},  C_L^* = V_cap;

and, for both, the membership identities of eq:reference-differences, 1_{I_R^*} - 1_{C_R^*} =
1_{U_cap} - 1_{C_+} - 1_sigma and 1_{C_L^*} - 1_{I_L^*} = 1_{V_cap} - 1_{I_-} - 1_tau, asserted where the deletion or addition is real
(sigma, tau actually change the cap lists; the few degenerate instances are counted).  The
controls: replacing sigma by any other index of the window breaks the row identity on every
instance where sigma lies in U_cap; and the sets U_cap, I_R^* differ whenever sigma is in U_cap,
so the deletion is not a no-op.  (s, t) are the phases of the mark as defined by `phases`.

Uncovered: the mixed-(d) frame (its corrected and deficient phases z_0, o_0 are not defined in the
paper by a formula this script could transcribe), and the use of g-periodicity of the whole
cores, which a single chart through a period-p mark does not have.
"""
from _gluing_common import compose, legal
from _mark_builders import betas, diagrams, marks, phases

J_CELLS = 11


def lists(S, p, c):
    X, Y = betas(S)
    N = X[0]
    I = [x for x in X if x != N]
    C = [y for y in Y if y != 0]
    ref = {
        'U': {c} | {i - (N - c) for i in I if N - c <= i < N},
        'Cp': {j - (N - c) for j in C if N - c <= j < N},
        'Im': {i for i in I if 1 <= i <= c},
        'V': {0} | {j for j in C if 1 <= j <= c},
        'IR': {x - (N - p - c) for x in X if N - p - c <= x <= N - p},
        'CR': {y - (N - p - c) for y in Y if N - p - c <= y < N - p},
        'IL': {x - p for x in X if p <= x <= p + c},
        'CL': {y - p for y in Y if p <= y <= p + c},
    }
    return N, ref


def ind(S, x):
    return 1 if x in S else 0


def main():
    stat = {}
    row = col = nonnoop = broken = outside = 0
    for J in diagrams(J_CELLS):
        for mk in marks(J):
            if mk.case != 'a' or not legal(mk) or mk.width == 0:
                continue
            p, w = mk.period, mk.width
            s, t = phases(mk)
            for g in range(2, p + 1):
                c = w % g
                if p % g or c == 0:
                    continue
                dpg = w - c
                for frame in ('row', 'col'):
                    for M in (2, 3):
                        outer = (frozenset((0, j) for j in range(M)) if frame == 'row'
                                 else frozenset((i, 0) for i in range(M)))
                        S = compose(outer, mk)
                        N, R = lists(S, p, c)
                        assert N == M * p + w
                        if frame == 'row':
                            sigma, tau = s - dpg, t
                            holds = (R['IR'] == R['U'] - {sigma} and R['CR'] == R['Cp']
                                     and R['IL'] == R['Im'] and R['CL'] == R['V'] - {tau})
                            assert holds or not (t <= c and w - s <= c), (sorted(J), p, w, g, M)
                            if not holds:
                                continue
                            row += 1
                            if sigma in R['U']:
                                nonnoop += 1
                                assert R['IR'] != R['U']
                                for other in range(c + 1):
                                    if other != sigma and other in R['U']:
                                        broken += R['IR'] != R['U'] - {other}
                        else:
                            sigma, tau = t - dpg, s
                            holds = (R['IR'] == R['U'] and R['CR'] == R['Cp'] | {sigma}
                                     and R['IL'] == R['Im'] | {tau} and R['CL'] == R['V'])
                            assert holds == (s <= c and w - t <= c), (sorted(J), p, w, g, M)
                            if not holds:
                                outside += 1
                                continue
                            col += 1
                        if frame == 'row':
                            deleted = sigma in R['U']
                        else:
                            deleted = sigma not in R['Cp']
                        tdel = (tau in R['V']) if frame == 'row' else (tau not in R['Im'])
                        stat[(frame, deleted, tdel)] = stat.get((frame, deleted, tdel), 0) + 1
                        if not (deleted and tdel):
                            continue
                        for u in range(-1, c + 2):
                            assert (ind(R['IR'], u) - ind(R['CR'], u)
                                    == ind(R['U'], u) - ind(R['Cp'], u) - (u == sigma))
                            assert (ind(R['CL'], u) - ind(R['IL'], u)
                                    == ind(R['V'], u) - ind(R['Im'], u) - (u == tau))
    print(f'row frames {row} (sigma in U_cap in {nonnoop}), column frames {col}; '
          f'wrong deletion index rejected {broken} times; '
          f'outside the phase bounds the identity fails: {outside}')
    print('(frame, sigma active, tau active):', sorted(stat.items(), key=str))
    assert row > 500 and col > 500 and nonnoop > 100 and broken > 0 and outside > 0
    print('ALL PASS')


if __name__ == '__main__':
    main()
