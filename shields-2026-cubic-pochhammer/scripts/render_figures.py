#!/usr/bin/env python3
r"""Paper section `sec:threshold` (The sharp multiplicity threshold): render the
manuscript's figure to a one-figure-per-page PDF.

The paper carries a single float, `fig:multiplicity-threshold`, a `pgfplots`
axis holding the four normalized degree-three constant-weight kernels.  Journal
submission systems want the artwork as its own file, one figure per page, with
the caption left in the manuscript text.  This script extracts the axis
environment from the manuscript itself -- not from a hand-kept copy, so the
artwork cannot drift from the paper -- and typesets it on its own A4 page in

    shields-2026-cubic-pochhammer-figures.pdf

The generated wrapper is written to scripts/figures_pages.tex for inspection
(scripts/.gitignore excludes *.tex, as for every generated snippet here).

Output format is PDF because that is what Elsevier accepts for vector artwork
(EPS is the only other accepted vector format; SVG is not accepted).

Every structural property of the output is asserted, so a broken extraction
fails the script rather than producing a plausible-looking wrong figure.  The
governing invariant is that the number of figure floats in the manuscript equals
the number of pages rendered here, checked against the built PDF rather than
against a hard-coded page count -- so a float added to the paper and forgotten
here fails this script instead of silently shipping incomplete artwork.

This is a submission-artifact builder rather than a mathematical check: the
claims the figure makes are verified by `make_figure_multiplicity.py`, which
also compares every inlined coordinate against a fresh derivation.  What is
checked here is that the artwork file is the manuscript's own figure, complete
and vector.
"""

import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PAPER_DIR = Path(__file__).resolve().parent.parent
PAPER = PAPER_DIR / "shields-2026-cubic-pochhammer.tex"
WRAPPER = PAPER_DIR / "scripts" / "figures_pages.tex"
OUTPUT = PAPER_DIR / "shields-2026-cubic-pochhammer-figures.pdf"

# every float to render, in the order it appears in the manuscript; one page
# each.  `plots` is the expected number of \addplot blocks -- the four data
# curves, the dashed central-value rule, and the two interior-maximum markers:
# a change means the figure was edited and its caption claims need rechecking
# too.  `landmarks` is text that must survive into the page, so a silently
# empty or clipped render fails: the axis labels, the top tick 1.2 that puts
# the r = 4 and r = 5 overshoots on scale, and all four legend entries, so a
# dropped curve is caught.  `segments` is a floor on the vector path segments
# on that page.
FIGURES = (
    {
        "label": "fig:multiplicity-threshold",
        "plots": 7,
        "segments": 400,
        "landmarks": ("q", "0.25", "1.2",
                      "r = 2", "r = 3", "r = 4", "r = 5"),
    },
)

A4_PT = (595.276, 841.89)


# ---------------------------------------------------------------------------
# extraction
# ---------------------------------------------------------------------------
COMMENT = re.compile(r"(?<!\\)%.*")


def uncommented(tex):
    r"""`tex` with its TeX comments removed, for counting only.

    A curve disabled with a leading `%` is still the string `\addplot`, so a
    raw count would pass while the page lost a whole curve.  The segment floor
    below does not reliably catch that on its own: one of the four data curves
    is about a quarter of the page's path segments, so losing it lands close to
    the floor rather than well under it.  Counting the uncommented text closes
    the gap.  Only the count sees this -- the body handed to pdflatex keeps its
    comments, since stripping them can join a line to the next one.
    """
    return COMMENT.sub("", tex)


def find_environment(text, env, must_contain=None, start=0):
    """Return (body, span) of the first `env` environment, brace-depth aware.

    Nested environments of the same name are matched correctly; `must_contain`
    skips environments that do not hold the given substring.
    """
    begin, end = rf"\begin{{{env}}}", rf"\end{{{env}}}"
    pos = start
    while True:
        i = text.find(begin, pos)
        if i < 0:
            raise LookupError(f"no \\begin{{{env}}} found after offset {pos}")
        depth, j = 1, i + len(begin)
        while depth:
            nxt_b, nxt_e = text.find(begin, j), text.find(end, j)
            if nxt_e < 0:
                raise LookupError(f"unterminated {env} environment at offset {i}")
            if 0 <= nxt_b < nxt_e:
                depth, j = depth + 1, nxt_b + len(begin)
            else:
                depth, j = depth - 1, nxt_e + len(end)
        body = text[i + len(begin) : j - len(end)]
        if must_contain is None or must_contain in body:
            return body, (i, j)
        pos = j


def extract_panels(paper_text):
    """Return the axis body of every configured float, in manuscript order."""
    # uncommented, for the same reason the \addplot count is: a float parked
    # behind a `%` is not artwork, and counting it would make the page-count
    # invariant below demand a page for it
    n_floats = uncommented(paper_text).count(r"\begin{figure}")
    assert n_floats == len(FIGURES), (
        f"paper has {n_floats} figure floats but {len(FIGURES)} are configured; "
        "a figure was added or removed"
    )

    panels = []
    for spec in FIGURES:
        label = spec["label"]
        # match the declaration, not the name: another float's caption may
        # cross-reference this label, and a bare substring would find that one
        figure, _ = find_environment(
            paper_text, "figure", must_contain=rf"\label{{{label}}}"
        )
        picture, _ = find_environment(figure, "tikzpicture")

        bodies = []
        pos = 0
        while True:
            try:
                axis, (_, j) = find_environment(picture, "axis", start=pos)
            except LookupError:
                break
            bodies.append(axis)
            pos = j
        assert len(bodies) == 1, (
            f"{label}: expected one axis environment, found {len(bodies)}; "
            "a second panel would need placing relative to the first, which "
            "this wrapper does not strip"
        )
        body = bodies[0]

        counted = uncommented(body).count(r"\addplot")
        assert counted == spec["plots"], (
            f"{label}: expected {spec['plots']} plot commands, found {counted}; "
            "the figure changed -- update FIGURES and recheck the caption claims"
        )
        panels.append(body)

    assert len(panels) == n_floats
    return panels


# ---------------------------------------------------------------------------
# wrapper document
# ---------------------------------------------------------------------------
PREAMBLE = r"""% Generated by scripts/render_figures.py -- do not edit by hand.
% One figure per page; extracted from shields-2026-cubic-pochhammer.tex.
\documentclass[11pt,a4paper]{article}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,mathtools}
\usepackage{pgfplots}
\pgfplotsset{compat=1.18}
%(macros)s
\pagestyle{empty}
\begin{document}
"""

PAGE = r"""
\begin{center}
\vspace*{\fill}
\begin{tikzpicture}
\begin{axis}%(body)s\end{axis}
\end{tikzpicture}
\vspace*{\fill}
\end{center}
\newpage
"""

MACRO = re.compile(r"^\\newcommand\{\\[A-Za-z]+\}(\[\d+\])?\{.*\}$", re.M)


def paper_macros(paper_text):
    """The artwork must render standalone, so the wrapper inherits every
    zero-argument macro the manuscript defines -- a figure body using one
    (\\Tur, say) would otherwise fail to compile or, worse, render wrong."""
    head = paper_text[: paper_text.index(r"\begin{document}")]
    return "\n".join(m.group(0) for m in MACRO.finditer(head))


def build_wrapper(panels, macros):
    pages = "".join(PAGE % {"body": body} for body in panels).rstrip()
    # the trailing \newpage would leave an empty final page
    assert pages.endswith(r"\newpage")
    pages = pages[: -len(r"\newpage")]
    return PREAMBLE.replace("%(macros)s", macros) + pages + "\n\\end{document}\n"


def compile_pdf(wrapper_path):
    with tempfile.TemporaryDirectory() as build:
        cmd = [
            "pdflatex",
            "-interaction=nonstopmode",
            "-halt-on-error",
            f"-output-directory={build}",
            wrapper_path.name,
        ]
        for _ in range(2):
            proc = subprocess.run(
                cmd, cwd=wrapper_path.parent, capture_output=True, text=True
            )
            if proc.returncode != 0:
                sys.stderr.write(proc.stdout[-4000:])
                raise SystemExit("pdflatex failed")
        log = (Path(build) / (wrapper_path.stem + ".log")).read_text(
            encoding="utf-8", errors="replace"
        )
        for bad in ("LaTeX Error", "Undefined control sequence", "Emergency stop"):
            assert bad not in log, f"build log reports: {bad}"
        produced = Path(build) / (wrapper_path.stem + ".pdf")
        assert produced.exists(), "pdflatex produced no PDF"
        shutil.copyfile(produced, OUTPUT)


# ---------------------------------------------------------------------------
# verification of the produced PDF
# ---------------------------------------------------------------------------
def verify(n_panels):
    import fitz

    doc = fitz.open(OUTPUT)
    assert doc.page_count == n_panels, (
        f"expected {n_panels} pages, got {doc.page_count}"
    )

    for k, page in enumerate(doc):
        w, h = page.rect.width, page.rect.height
        assert abs(w - A4_PT[0]) < 1 and abs(h - A4_PT[1]) < 1, (
            f"page {k + 1} is {w:.1f}x{h:.1f}pt, expected A4"
        )
        # vector content present, and nothing rasterized.  Paths are grouped by
        # PyMuPDF, so a 120-point polyline counts once; the segment count is
        # what tracks the plotted data.
        paths = page.get_drawings()
        segments = sum(len(p["items"]) for p in paths)
        assert len(paths) >= 6, f"page {k + 1} has only {len(paths)} vector paths"
        assert not page.get_images(), (
            f"page {k + 1} contains a raster image; artwork must stay vector"
        )
        text = page.get_text()
        assert segments >= FIGURES[k]["segments"], (
            f"page {k + 1} has only {segments} path segments; curve data lost?"
        )
        for landmark in FIGURES[k]["landmarks"]:
            assert landmark in text, (
                f"page {k + 1} ({FIGURES[k]['label']}) is missing the "
                f"landmark {landmark!r}"
            )
        print(
            f"  page {k + 1}: {w:.0f}x{h:.0f}pt, "
            f"{len(paths)} paths / {segments} segments"
        )
    doc.close()


def main():
    text = PAPER.read_text(encoding="utf-8")

    # the float-count and plot-count invariants are pure Python and always run:
    # a float added to the paper and forgotten here must fail on a clean clone,
    # whose requirements.txt carries only sympy and mpmath
    panels = extract_panels(text)
    n = len(panels)
    s = "" if n == 1 else "s"
    print("PASS  extracted " + ", ".join(spec["label"] for spec in FIGURES))

    missing = [] if shutil.which("pdflatex") else ["pdflatex"]
    try:
        import fitz  # noqa: F401
    except ImportError:
        missing.append("PyMuPDF")
    if missing:
        print(f"SKIP: rendering needs {' and '.join(missing)}; the "
              f"{n}-float invariant and the per-figure plot counts "
              "were checked")
        print(f"\nALL PASS: render_figures -- {n} figure float{s} configured "
              "and counted (render skipped)")
        return

    WRAPPER.write_text(build_wrapper(panels, paper_macros(text)), encoding="utf-8")
    print(f"PASS  wrote {WRAPPER.relative_to(PAPER_DIR)}")

    compile_pdf(WRAPPER)
    verify(n)
    assert n == uncommented(text).count(r"\begin{figure}")
    print(
        f"PASS  wrote {OUTPUT.relative_to(PAPER_DIR)} "
        f"({OUTPUT.stat().st_size / 1024:.0f} KB)"
    )
    print(f"\nALL PASS: render_figures -- {n} figure float{s} in the "
          f"manuscript, {n} vector page{s} rendered")


if __name__ == "__main__":
    main()
