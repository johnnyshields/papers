#!/usr/bin/env python3
"""Figure for the chart definition of Section 2.

Draws one legal chart F = D o_w E: the marked inner w, the outer D, and the
composition F, with the two copies of the inner outlined so the shared mark is
visible as the overlap.

The example is not asserted to be legal, it is certified: the mark is built and
then put through the legality predicate of ``verify_common_factor_graphs``,
which decides conditions (I)--(IV), and the composition is computed twice --
once structurally and once through the offset formula of the paper's displayed
placement equation -- with the two required to agree.  ``--check-only`` runs
every check and imports no plotting library, so it is safe in ``run_all.sh``.

Usage:
    python3 make_figures.py --check-only      # verify the example only
    python3 make_figures.py                   # verify, then write figures/
"""

import argparse
import os

import verify_common_factor_graphs as V

E_UNIT = (0, 1)          # the east unit vector e

# The pinned example: a six-cell inner whose mark is a vertical domino at each
# end, ordinary case (a), overlap width 2 against period 3.
E = frozenset({(-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (0, 0)})
W_LOWER = frozenset({(-1, 0), (0, 0)})
W_UPPER = frozenset({(-2, 2), (-1, 2)})
V_DISP = (-1, 2)
CASE = 'a'
OUTER = frozenset({(0, 0), (0, 1)})      # the two-cell row outer D


def mark():
    return V.Mark(E, W_LOWER, W_UPPER, CASE, V_DISP)


def offsets(outer, disp, case):
    """Copy origins L_w(d), the paper's placement formula for the ordinary cases."""
    out = {}
    for (i, j) in outer:
        t = j - i
        axial = i if case == 'a' else -i
        out[(i, j)] = (t * disp[0] + axial * E_UNIT[0],
                       t * disp[1] + axial * E_UNIT[1])
    return out


def check(verbose=True):
    mk = mark()
    say = print if verbose else (lambda *a, **k: None)

    # the mark is legal, by the paper's own predicate for (I)--(IV)
    assert V.legal(mk), "the pinned mark is not legal"
    w = V.span(W_LOWER)
    q = V.span(E) - w
    assert w == 2 and q == 3, (w, q)
    assert 0 <= w < q, "condition (II) requires 0 <= w < q"
    assert V.shift(W_LOWER, V_DISP) == W_UPPER, "W_+ must be W_- + v"
    assert V.span(W_LOWER) == V.span(W_UPPER)
    assert V.southwest(E) in W_LOWER and V.northeast(E) in W_UPPER
    middle = E - W_LOWER - W_UPPER
    assert len(middle) == 2 and V.is_connected_skew(V.normalize(middle))
    say(f"  mark: legal, case ({CASE}), |E|={len(E)}, w={w}, q={q}, v={V_DISP}")

    # the composition, by two independent routes
    F1 = V.normalize(V.compose(OUTER, mk))
    F2 = V.normalize(V.compose_by_offsets(OUTER, mk))
    assert F1 == F2, "the structural and offset routes disagree"
    assert V.is_connected_skew(F1)
    assert len(F1) == 2 * len(E) - len(W_LOWER), len(F1)
    say(f"  composition: both routes agree, |F|={len(F1)} = 2|E|-|W|, connected")

    # the drawn copies really do tile F, overlapping in exactly the mark
    org = offsets(OUTER, V_DISP, CASE)
    copies = [V.shift(E, o) for o in org.values()]
    assert len(copies) == 2
    union = frozenset().union(*copies)
    assert V.normalize(union) == F1, "the drawn copies do not union to F"
    overlap = copies[0] & copies[1]
    assert len(overlap) == w, "the two copies must overlap in the mark"
    say(f"  copies: {len(copies)} placements union to F, overlap {len(overlap)} cells")

    say("  ALL PASS")
    return mk, F1, org


LIGHT = "0.87"          # the first copy, and the mark inside the inner
WHITE = "white"         # the second copy

# The drawing is included at a fraction of \linewidth, so everything in it is
# scaled by that fraction when printed.  Type set at the nominal size would come
# out illegible, so the point sizes are divided by the same fraction and the
# printed sizes are what the names say.
INCLUDE_FRACTION = 0.6
LABEL_PT = round(10.5 / INCLUDE_FRACTION)
GLYPH_PT = round(8.0 / INCLUDE_FRACTION)


def draw_cells(ax, cells, *, offset=(0, 0), fills=None, glyphs=None,
               hatched=frozenset(), lw=1.0):
    """Unit cells at (row, col); rows run downward in the English convention.

    ``fills`` maps a cell to a face color, ``glyphs`` maps a cell to a short
    label drawn inside it, and ``hatched`` is the set of cells drawn hatched;
    all default to a plain white cell.
    """
    import matplotlib.patches as mp
    fills = fills or {}
    glyphs = glyphs or {}
    for (i, j) in cells:
        y = -(i + offset[0])
        x = j + offset[1]
        face = fills.get((i, j), WHITE)
        ax.add_patch(mp.Rectangle((x, y - 1), 1, 1, facecolor=face,
                                  edgecolor="0.15", lw=lw, zorder=2,
                                  hatch="////" if (i, j) in hatched else None))
        if (i, j) in glyphs:
            ax.text(x + 0.5, y - 0.5, glyphs[(i, j)], ha="center", va="center",
                    fontsize=GLYPH_PT, zorder=3)


def cols(s):
    return min(j for _, j in s), max(j for _, j in s)


def rows(s):
    return min(i for i, _ in s), max(i for i, _ in s)


def figure(out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    _, F, org = check(verbose=False)

    # One axes for every group, so the cell size is identical across panels and
    # no panel is silently scaled relative to another.
    fig, ax = plt.subplots(figsize=(7.0, 2.5))

    gap = 1.6
    x = 0.0
    labels = []
    extents = []

    def put(cells, label, fills=None, glyphs=None, hatched=frozenset()):
        nonlocal x
        c0, c1 = cols(cells)
        r0, r1 = rows(cells)
        # centre every panel on a common horizontal axis
        off = (-(r0 + r1) / 2.0, x - c0)
        draw_cells(ax, cells, offset=off, fills=fills, glyphs=glyphs,
                   hatched=hatched)
        labels.append((x + (c1 - c0 + 1) / 2.0, label))
        extents.append(r1 - r0 + 1)
        x += (c1 - c0 + 1) + gap

    # the marked inner: the two end copies carry their signs, the middle is plain
    glyphs = {c: "$-$" for c in W_LOWER}
    glyphs.update({c: "$+$" for c in W_UPPER})
    fills = {c: LIGHT for c in W_LOWER | W_UPPER}
    put(E, r"$\omega$", fills=fills, glyphs=glyphs)

    put(OUTER, r"$D$")

    # the composition: the two copies are shaded apart, so F reads as two copies
    # of the inner meeting in the mark rather than as one undifferentiated shape
    copies = [V.shift(E, o) for o in sorted(org.values())]
    overlap = copies[0] & copies[1]
    union = frozenset().union(*copies)
    sw = V.southwest(union)
    back = (-sw[0], -sw[1])
    first = V.shift(copies[0] - overlap, back)
    lap = V.shift(overlap, back)
    # three levels: one copy shaded, the other plain, and the shared mark
    # hatched, so the overlap is not mistaken for part of either copy
    fills = {c: LIGHT for c in first | lap}
    put(V.normalize(union), r"$F$", fills=fills, hatched=lap)

    xmax = x - gap
    half = max(extents) / 2.0
    for xc, text in labels:
        ax.text(xc, -half - 0.55, text, ha="center", va="top", fontsize=LABEL_PT)

    x0, x1 = -0.3, xmax + 0.3
    y0, y1 = -half - 1.25, half + 0.25
    ax.set_xlim(x0, x1)
    ax.set_ylim(y0, y1)
    ax.set_aspect("equal")
    ax.axis("off")
    # The drawing is placed at \linewidth, so printed width is already spent and
    # the only lever on cell size is the aspect: a figure wider than the data box
    # letterboxes and prints the cells smaller than the column allows.  Take the
    # ratio from the drawn limits rather than fixing it by hand, so restacking a
    # panel or retuning a range cannot silently shrink the figure.
    width = 7.0
    fig.set_size_inches(width, width * (y1 - y0) / (x1 - x0))
    fig.tight_layout(pad=0.15)
    os.makedirs(out, exist_ok=True)
    fig.savefig(out + "/chart-composition.pdf")
    fig.savefig(out + "/chart-composition.png", dpi=200)
    print(f"  wrote {out}/chart-composition.pdf and .png")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check-only", action="store_true",
                    help="verify the example and import no plotting library")
    ap.add_argument("--out", default=os.path.join(os.path.dirname(__file__) or ".",
                                                  "..", "figures"))
    a = ap.parse_args()
    if a.check_only:
        check()
        return
    check()
    figure(os.path.normpath(a.out))


if __name__ == "__main__":
    main()
