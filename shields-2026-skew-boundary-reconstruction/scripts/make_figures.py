"""Generators for the paper's two figures, and the exact checks behind them.

Every number that reaches a figure or a caption is recomputed here from the
paper's own definitions -- eq:Adef, eq:dexplicit, eq:capmatrix, eq:cofactor,
eq:alpha-general, eq:F-general -- over integer coefficients, and asserted
against the printed values of ex:actual-equal-chain.  Nothing is transcribed.

  fig:boundary-observations   what thm:boundary-reconstruction says, on the
                              paper's own equal pair: the two observations that
                              separate parents whose skew Schur functions agree.
  fig:cancellation-geometry   why it works, at square weight: the lower hull of
                              (d_j, alpha_j), the common-row supporting slopes
                              2A_i that expose the adjacent edges, and the
                              positive-cap slope -2a that exposes column one.

Run from scripts/:  python3 make_figures.py --output-dir ../figures
"""
import argparse
from itertools import permutations

# ---------- exact h-polynomials: {sorted tuple of subscripts: int coeff}
def hm(k):
    if k < 0:  return {}
    if k == 0: return {(): 1}
    return {(k,): 1}

def mul(p, q):
    o = {}
    for a, ca in p.items():
        for b, cb in q.items():
            k = tuple(sorted(a + b)); o[k] = o.get(k, 0) + ca * cb
    return {k: v for k, v in o.items() if v}

def add(p, q):
    o = dict(p)
    for k, v in q.items(): o[k] = o.get(k, 0) + v
    return {k: v for k, v in o.items() if v}

def scale(p, c): return {k: v * c for k, v in p.items()} if c else {}

def det(rows):
    n = len(rows); acc = {}
    for perm in permutations(range(n)):
        sgn, pr = 1, list(perm)
        for i in range(n):
            for j in range(i + 1, n):
                if pr[i] > pr[j]: sgn = -sgn
        t = {(): 1}
        for i, j in enumerate(perm):
            t = mul(t, rows[i][j])
            if not t: break
        if t: acc = add(acc, scale(t, sgn))
    return acc

def show(p):
    if not p: return "0"
    def key(m): return (sum(m), m)
    out = []
    for mono in sorted(p, key=key):
        c = p[mono]
        body = "".join(f"h_{e}" for e in mono) or "1"
        out.append(("+" if c > 0 else "-") + (f"{abs(c)}" if abs(c) != 1 else "") + body)
    t = "".join(out)
    return t[1:] if t.startswith("+") else t

sq = lambda k: k * k

def coords(lam, mu):
    n = len(lam); L = lam[0]
    A = [L - lam[i] + i for i in range(n)]
    d = [0] + [L - mu[j - 1] + j - 1 for j in range(1, n + 1)]
    return A, d

def cofactors(lam, mu):
    A, d = coords(lam, mu)
    n = len(lam)
    M = [[hm(d[j] - A[i]) for j in range(n + 1)] for i in range(n)]
    return [scale(det([[M[i][t] for t in range(n + 1) if t != j] for i in range(n)]),
                  (-1) ** j) for j in range(n + 1)], A, d

def wto(p):
    return None if not p else min(sum(sq(e) for e in m) for m in p)

def schur(lam, mu):
    """ordinary Jacobi-Trudi determinant of lam/mu, dropping empty rows"""
    rows = [(lam[i], (mu + [0] * len(lam))[i]) for i in range(len(lam))]
    rows = [(a, b) for a, b in rows if a - b > 0]
    if not rows: return {(): 1}
    n = len(rows)
    M = [[hm(rows[i][0] - rows[j][1] - i + j) for j in range(n)] for i in range(n)]
    return det(M)

def delete_top(lam, mu):
    return list(lam[1:]), list(mu[1:])

def extend_ne(lam, mu, a):
    """X.(a): a row of length a attached to the northeast, meeting the old top
    row in exactly one column (the paper's own description, used in
    cor:two-positive-extensions' proof)."""
    return [lam[0] + a - 1] + list(lam), [lam[0] - 1] + list(mu)

# ---------------------------------------------------------------- the example
MU = [3, 2, 1, 0]
LX = [4, 4, 4, 2]
LY = [4, 4, 3, 3]

def check():
    CX, AX, dX = cofactors(LX, MU)
    CY, AY, dY = cofactors(LY, MU)
    assert dX == dY == [0, 1, 3, 5, 7], dX
    assert AX == [0, 1, 2, 5], AX
    assert AY == [0, 1, 3, 4], AY
    G = [add(CX[j], scale(CY[j], -1)) for j in range(5)]
    # compare as POLYNOMIALS, not as printed strings -- term order is the
    # printer's choice and the paper's is not this one
    printed = {0: {},
               1: {(2, 5): 1, (3, 4): -1},
               2: {(1, 4): 1, (5,): -1},
               3: {(3,): 1, (1, 2): -1},
               4: {}}
    for j in range(5):
        assert G[j] == printed[j], (j, show(G[j]))
    nu = [wto(g) for g in G]
    alpha = [None if nu[j] is None else nu[j] + sq(dX[j]) for j in range(5)]
    assert alpha == [None, 26, 26, 30, None], alpha
    v = next(i for i in range(4) if AX[i] != AY[i]); assert v == 2
    # eq:F-general at square weight: F_i(j) = alpha_j - 2 A_i d_j + A_i^2
    Ms = {}
    for i in (0, 1):
        F = {j: alpha[j] - 2 * AX[i] * dX[j] + AX[i] ** 2 for j in (1, 2, 3)}
        m = min(F.values()); Ms[i] = sorted(j for j in F if F[j] == m)
    assert Ms[0] == [1, 2] and Ms[1] == [2, 3], Ms
    # cor:boundary-separation at a: wt(G_j h_{a+d_j}) = alpha_j - d_j^2 + (a+d_j)^2
    caps = {}
    for a in (1, 2, 3):
        W = {j: alpha[j] - sq(dX[j]) + sq(a + dX[j]) for j in (1, 2, 3)}
        m = min(W.values()); caps[a] = (sorted(j for j in W if W[j] == m), W)
    for a in (1, 2, 3):
        assert caps[a][0] == [1], (a, caps[a])
    # the two separations the first figure prints
    sX, sY = schur(LX, MU), schur(LY, MU)
    assert sX == sY, "the pair must be skew-equal"
    bX, bY = schur(*delete_top(LX, MU)), schur(*delete_top(LY, MU))
    diff_bar = add(bX, scale(bY, -1))
    assert diff_bar == {(3, 4): 1, (2, 5): -1}, show(diff_bar)
    ext = {}
    for a in (1, 2, 3):
        eX, eY = schur(*extend_ne(LX, MU, a)), schur(*extend_ne(LY, MU, a))
        ext[a] = add(eX, scale(eY, -1))
        assert ext[a], f"extension by {a} must separate"
    # parent normalized actions at q = v+1 = 3 (eq:sigma-def)
    sig = {X: wto(C[3]) + sq(dX[3]) for X, C in (("X", CX), ("Y", CY))}
    return dict(A=AX, AY=AY, d=dX, G=G, alpha=alpha, v=v, q=v + 1, M=Ms,
                caps=caps, diff_bar=diff_bar, ext=ext, sigma_q=sig)

# ------------------------------------------------------------------ drawing
# A drawing is placed at \linewidth, so printed
# WIDTH is already spent and the only lever on it is a tighter x-range;
# printed HEIGHT follows figsize height against figsize width.  Nothing here
# is equal-aspect by accident -- the cell grids set aspect("equal") on
# purpose, because a skew diagram's cells must be square.

def cells(lam, mu):
    """the cells of lam/mu as (row, col), 0-based from the top-left, in the
    English convention the paper's coordinates assume"""
    mu = list(mu) + [0] * (len(lam) - len(mu))
    return [(i, c) for i in range(len(lam)) for c in range(mu[i], lam[i])]

def draw_diagram(ax, lam, mu, *, inner=True, mark=None, ncols=None, nrows=None,
                 row_offset=0):
    """one skew diagram.  `mark` is a set of rows drawn hatched.  `row_offset`
    pushes the whole diagram down inside a common grid, which is what makes the
    first-row deletion legible: Xbar's surviving rows are drawn where they sat
    in X, so the reader sees the top row gone rather than the diagram sliding
    up to fill its place."""
    import matplotlib.patches as mp
    mu = list(mu) + [0] * (len(lam) - len(mu))
    ncols = ncols or max(lam); nrows = nrows or len(lam)
    if inner:
        # The inner boundary is drawn as DE-DUPLICATED EDGES, not as one dotted
        # rectangle per cell.  Per-cell rectangles stroke every interior edge
        # twice -- once as one cell's right edge and again as its neighbor's
        # left -- and the two dash phases do not align, so an interior line
        # prints doubly dotted while the outer border prints singly.  Collecting
        # the edges in a set draws each exactly once, which is also what lets the
        # dash period be opened up: a sparse pattern makes the doubling worse,
        # not better, so this fix has to come first.
        seg = set()
        for i in range(len(lam)):
            for c in range(mu[i]):
                y0, y1 = -i - 1 - row_offset, -i - row_offset
                seg.add(((c, y1), (c + 1, y1)))          # top
                seg.add(((c, y0), (c + 1, y0)))          # bottom
                seg.add(((c, y0), (c, y1)))              # left
                seg.add(((c + 1, y0), (c + 1, y1)))      # right
        for (x0, y0), (x1, y1) in sorted(seg):
            ax.plot([x0, x1], [y0, y1], color="0.78", lw=0.6,
                    ls=(0, (1, 3.2)), solid_capstyle="butt", zorder=0)
    for (i, c) in cells(lam, mu):
        hatched = mark is not None and i in mark
        ax.add_patch(mp.Rectangle((c, -i - 1 - row_offset), 1, 1,
                                  facecolor="0.90" if hatched else "white",
                                  edgecolor="0.15", lw=1.0,
                                  hatch="////" if hatched else None))
    ax.set_xlim(-0.15, ncols + 0.15); ax.set_ylim(-nrows - 0.15, 0.15)
    ax.set_aspect("equal"); ax.axis("off")

def figure_one(D, out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    a = 3
    bX, bMU = delete_top(LX, MU); bY, bMUy = delete_top(LY, MU)
    eX, eMU = extend_ne(LX, MU, a); eY, eMUy = extend_ne(LY, MU, a)
    # The ROW grid is shared -- that is what makes the deletion and the
    # attachment legible -- but the COLUMN count is per column of panels.
    # Sharing the column count too drew the left two columns on a six-wide grid
    # while they occupy four, wasting a third of each panel's width; and printed
    # width is already spent at \linewidth, so dead space at a panel's edge is
    # the only thing that can be reclaimed (printed height follows the aspect).  The
    # width_ratios then match the column counts, so every cell prints the same
    # size and all of them print larger.
    NR = len(eX)
    NCOL = [max(max(LX), max(LY)), max(max(bX), max(bY)), max(max(eX), max(eY))]
    fig, axes = plt.subplots(2, 3, figsize=(7.2, 4.6),
                             gridspec_kw=dict(width_ratios=NCOL))
    # the extension adds a row ABOVE the old top row, so the originals and the
    # deletions are pushed down one row to sit under it in the same grid.
    panels = [
      [("$X$", LX, MU, {0}, 1), ("$\\overline{X}$", bX, bMU, None, 2),
       ("$X\\cdot(3)$", eX, eMU, {0}, 0)],
      [("$Y$", LY, MU, {0}, 1), ("$\\overline{Y}$", bY, bMUy, None, 2),
       ("$Y\\cdot(3)$", eY, eMUy, {0}, 0)],
    ]
    for r in range(2):
        for c in range(3):
            title, lam, mu, mark, off = panels[r][c]
            draw_diagram(axes[r][c], lam, mu, mark=mark, ncols=NCOL[c],
                         nrows=NR, row_offset=off)
            axes[r][c].set_title(title, fontsize=11.5, pad=3)
    # Each column carries its whole statement in one header block at the top of
    # the figure: what the column does to the pair, and what that yields.  The
    # inequalities are not placed under the bottom row: that would put the
    # two halves of one sentence three inches apart and make the reader carry
    # the operation past both diagrams to reach its conclusion.  Column zero is
    # headed too -- it performs no operation, but an unheaded column reads as a
    # column whose header was forgotten, and naming the input as the equal pair
    # is what makes the other two headers read as operations upon it.
    #
    # The offsets are in POINTS from the top edge of each panel's allocated box,
    # not in axes fractions, so the two header lines keep their spacing and
    # their clearance above the panel titles whatever the row height works out
    # to.  The panel title itself occupies about 3 to 19 points above that edge.
    HEAD_MATH, HEAD_WORD = 36, 58
    for c, word, math in (
            (0, "the equal pair", "$s_X=s_Y$"),
            (1, "delete the first row",
                "$s_{\\overline{X}}\\neq s_{\\overline{Y}}$"),
            (2, "attach a row of length $3$",
                "$s_{X\\cdot(3)}\\neq s_{Y\\cdot(3)}$")):
        # the operation in gray, its consequence in the same black math as the
        # panel titles: the figure reads as description, then statement.
        axes[0][c].annotate(word, xy=(0.5, 1.0), xycoords="axes fraction",
                            textcoords="offset points", xytext=(0, HEAD_WORD),
                            ha="center", va="bottom", fontsize=10, color="0.30")
        axes[0][c].annotate(math, xy=(0.5, 1.0), xycoords="axes fraction",
                            textcoords="offset points", xytext=(0, HEAD_MATH),
                            ha="center", va="bottom", fontsize=11.5)
    # top leaves the header block's own height (58pt to its baseline plus its
    # ascent) and a thin margin over it; bottom leaves almost nothing, since
    # nothing is printed under the second row any more.
    fig.subplots_adjust(left=0.02, right=0.98, top=0.755, bottom=0.035,
                        wspace=0.08, hspace=0.38)
    fig.savefig(out + "/monge-boundary-observations.pdf")
    fig.savefig(out + "/monge-boundary-observations.png", dpi=200)
    plt.close(fig)

# The two margins around fig2's legend, as fractions of figure height, set
# directly because neither is reachable through the usual levers.  The layout
# they replace put 0.069in above the legend and 0.366in below it, over five
# times as much sheet under it as over it; the legend reads as a caption of the
# panel above rather than as a stray block, so the larger margin belongs on the
# side away from the axes.
GAP_ABOVE_LEGEND = 0.052        # ~0.20in at the current figure height
GAP_BELOW_LEGEND = 0.034        # ~0.13in


def figure_two(D, out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    d, al, A = D["d"], D["alpha"], D["A"]
    pts = [(d[j], al[j], j) for j in (1, 2, 3)]
    fig, ax = plt.subplots(figsize=(7.2, 3.9))
    # the two common-row supporting lines, slope -2A_i is NOT this one:
    # F_i(j) = alpha_j - 2 A_i d_j + A_i^2 is minimized along lines of slope
    # +2A_i in the (d, alpha) plane, which is what exposes an adjacent edge.
    xs = [-1.5, 7.1]
    for i, style, col in ((0, "-", "0.20"), (1, "--", "0.20")):
        Fmin = min(al[j] - 2 * A[i] * d[j] + A[i] ** 2 for j in (1, 2, 3))
        ys = [Fmin + 2 * A[i] * x - A[i] ** 2 for x in xs]
        touch = sorted(j for j in (1, 2, 3)
                       if al[j] - 2 * A[i] * d[j] + A[i] ** 2 == Fmin)
        ax.plot(xs, ys, style, color=col, lw=1.2, zorder=1,
                label=f"common row $i={i}$: slope ${2*A[i]}$, exposes "
                      f"$\\{{{touch[0]},{touch[1]}\\}}$")
    # the positive cap a = 1: weights alpha_j - d_j^2 + (a+d_j)^2, level sets
    # of slope -2a; it touches column one alone.
    a = 1
    Wmin = min(al[j] - sq(d[j]) + sq(a + d[j]) for j in (1, 2, 3))
    ys = [Wmin - sq(a) - 2 * a * x for x in xs]
    tch = sorted(j for j in (1, 2, 3) if al[j] - sq(d[j]) + sq(a + d[j]) == Wmin)
    assert tch == [1], tch
    ax.plot(xs, ys, "-.", color="0.45", lw=1.2, zorder=1,
            label=f"positive cap $a={a}$: slope $-{2*a}$, exposes "
                  f"$\\{{{tch[0]}\\}}$ alone")
    ax.plot([d[1], d[2]], [al[1], al[2]], color="0.10", lw=2.4, zorder=2)
    ax.plot([d[2], d[3]], [al[2], al[3]], color="0.10", lw=2.4, zorder=2)
    # Point labels are placed per point, because the generic offset that suits
    # j = 1 puts j = 2's label ON the rising hull edge and j = 3's under the
    # slope-2 support.  One line each, and an opaque box, so a line crossing
    # behind a label cannot strike through it.
    # Every label goes to the RIGHT of its point, into the one region of the
    # panel no line crosses.  For d in [1, 3] the band above alpha = 26 is empty:
    # the slope-0 support runs along 26, the slope-2 support is below it there
    # (22 at d = 1, 26 only at d = 3) and the slope--2 cap support is below it
    # too (25.2 at d = 1.4).  So j = 1 goes up-right.  At j = 2 the rising hull
    # edge leaves upward, so that label goes down-right instead, into the wedge
    # between the hull and the descending cap support.  j = 3 goes down-right,
    # below the point rather than above it, which is what separates it from the
    # first-split annotation overhead.
    off = {1: (-9, -17), 2: (11, -16), 3: (9, -17)}
    ha = {1: "right", 2: "left", 3: "left"}
    for (x, y, j) in pts:
        ax.plot([x], [y], "o", ms=7, color="white", mec="0.10", mew=1.4, zorder=4)
        ax.annotate(f"$j={j}$: $({x},{y})$", (x, y), textcoords="offset points",
                    xytext=off[j], fontsize=10.5, zorder=5, ha=ha[j],
                    bbox=dict(boxstyle="round,pad=0.14", fc="white",
                              ec="none", alpha=0.92))
    q = D["q"]
    ax.axvline(d[q], color="0.55", lw=0.9, ls=(0, (4, 3)), zorder=0)
    # horizontal, at the top, clear of both the hull and the legend -- rotated
    # into the panel it crossed the legend and the rising edge at once.
    ax.annotate(f"first split: column $q={q}$ at shift $d_{q}={d[q]}$",
                xy=(d[q] - 0.15, 31.35), fontsize=10,
                va="top", ha="right", color="0.35")
    # The data occupy alpha in [26, 30].  A wider range would shrink every feature on
    # the panel, since printed height is the extent over the range times the axes
    # height; range and figsize are set together, so the spacing is bought with sheet
    # rather than out of the drawing, and the range still shows all three supports
    # leaving the hull.
    ax.set_xlim(-1.5, 7.1); ax.set_ylim(23.9, 31.6)
    ax.set_xlabel("cap shift $d_j$", fontsize=11.5)
    ax.set_ylabel("normalized action $\\alpha_j$", fontsize=11.5)
    ax.set_xticks([d[j] for j in (1, 2, 3)]); ax.set_yticks([26, 30])
    ax.tick_params(labelsize=10.5)
    ax.spines[["top", "right"]].set_visible(False)
    # The legend goes BELOW the axes, outside the data area.  Three long entries
    # inside a panel this small collide with whichever line they are not
    # describing, and shortening them to fit would delete the slopes, which are
    # the content.  Placing it outside costs sheet, which § Figure sizing says
    # is the cheap resource.
    # borderaxespad=0 so the anchor IS the legend's top edge.  At its default
    # the legend sits half a font-size below wherever it is anchored, which put
    # both measured margins off their requested values by that constant.
    leg = ax.legend(loc="upper center", ncol=1,
                    fontsize=10.5, frameon=False, borderpad=0.2,
                    borderaxespad=0.0,
                    handlelength=2.8, labelspacing=0.32)
    # The two margins around the legend are set directly, in figure fractions,
    # because the obvious lever does not work: tight_layout counts the legend
    # in its solve, so lowering bbox_to_anchor made it lift the axes to
    # compensate and BOTH margins grew together -- measured at 0.069/0.366in
    # before and 0.141/0.474in after, when the second number was meant to
    # shrink.  Taking the legend out of the solve and positioning it against
    # the figure decouples them: the axes are laid out on their own
    # decorations, and the anchor below then trades one margin for the other.
    leg.set_in_layout(False)
    fig.tight_layout()

    inv = fig.transFigure.inverted()

    def below_axes():
        """Depth of the ticks and x-label beneath the axes rectangle, and the
        absolute height of the x-label's lower edge.  The legend is hidden for
        the measurement or it measures itself."""
        leg.set_visible(False)
        fig.canvas.draw()
        tb = ax.get_tightbbox(fig.canvas.get_renderer()).transformed(inv)
        leg.set_visible(True)
        return ax.get_position().y0 - tb.y0, tb.y0

    fig.canvas.draw()
    leg_h = leg.get_window_extent().transformed(inv).height
    decor, _ = below_axes()
    # Reserve exactly what the stack beneath the axes needs.  Without this the
    # layout fills the sheet with the axes and the legend lands off the page.
    fig.subplots_adjust(bottom=GAP_BELOW_LEGEND + leg_h + GAP_ABOVE_LEGEND + decor)

    _, label_bottom = below_axes()
    leg.set_bbox_to_anchor((0.5, label_bottom - GAP_ABOVE_LEGEND),
                           transform=fig.transFigure)
    fig.savefig(out + "/monge-cancellation-geometry.pdf")
    fig.savefig(out + "/monge-cancellation-geometry.png", dpi=200)
    plt.close(fig)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-dir", default="../figures")
    ap.add_argument("--check-only", action="store_true")
    args = ap.parse_args()
    D = check()
    print("=== ex:actual-equal-chain, recomputed exactly ===")
    print(f"  d        = {tuple(D['d'])}")
    print(f"  A^X      = {tuple(D['A'])}    A^Y = {tuple(D['AY'])}   v = {D['v']}, q = {D['q']}")
    for j in range(5): print(f"  G_{j}      = {show(D['G'][j]):16} alpha_{j} = {D['alpha'][j]}")
    print(f"  M_0      = {D['M'][0]}   M_1 = {D['M'][1]}")
    print(f"  s_Xbar - s_Ybar = {show(D['diff_bar'])}")
    for a in (1, 2, 3):
        print(f"  cap a={a}: summand weights {D['caps'][a][1]}, minimizer {D['caps'][a][0]};"
              f"  s_(X.({a})) - s_(Y.({a})) = {show(D['ext'][a])}")
    print(f"  parent actions at q: sigma_q(X) = {D['sigma_q']['X']}, sigma_q(Y) = {D['sigma_q']['Y']}"
          f"  -> alpha_q = {D['alpha'][3]}")
    if not args.check_only:
        import os
        os.makedirs(args.output_dir, exist_ok=True)
        figure_one(D, args.output_dir)
        figure_two(D, args.output_dir)
        print(f"wrote both figures to {args.output_dir}")
    print()
    print("ALL PASS")
