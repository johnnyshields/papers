#!/usr/bin/env python3
r"""Render the manuscript's figure to a one-figure-per-page PDF.

The paper carries a single float, fig:det-M1, holding one pgfplots axis.
Journal submission systems want the artwork as its own file, one figure per
page, with the caption left in the manuscript text.  This script extracts the
axis environment from the manuscript itself -- not from a hand-kept copy, so
the artwork cannot drift from the paper -- and typesets it on its own A4 page in

    shields-2026-turan-bessel-figure.pdf

The generated wrapper is written to scripts/figures_pages.tex for inspection
(scripts/.gitignore excludes *.tex, as for every generated snippet here).

Output format is PDF because that is what Elsevier accepts for vector artwork
(EPS is the only other accepted vector format; SVG is not accepted).

Every structural property of the output is asserted, so a broken extraction
fails the script rather than producing a plausible-looking wrong figure.
"""

import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PAPER_DIR = Path(__file__).resolve().parent.parent
PAPER = PAPER_DIR / "shields-2026-turan-bessel.tex"
WRAPPER = PAPER_DIR / "scripts" / "figures_pages.tex"
OUTPUT = PAPER_DIR / "shields-2026-turan-bessel-figure.pdf"

# every float to render, in page order; one page per axis environment found
FIGURE_LABELS = ("fig:det-M1",)

# expected \addplot count per axis, flattened in page order; a change here means
# the figure was edited and its caption claims need rechecking too
EXPECTED_ADDPLOTS = (4,)

# text that must survive into each page, so a silently empty or reordered
# render fails
LANDMARKS = (
    ("0.3690738484", "indefinite", "0.25", "0.50"),
)

A4_PT = (595.276, 841.89)


# ---------------------------------------------------------------------------
# extraction
# ---------------------------------------------------------------------------
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


def split_options(optstring):
    """Split a pgfkeys option list on depth-0 commas."""
    out, depth, cur = [], 0, ""
    for ch in optstring:
        if ch in "{[(":
            depth += 1
        elif ch in "}])":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


def strip_relative_placement(axis_block):
    """Drop the depth-0 options that place this axis against a sibling axis.

    Only acts when a depth-0 `at=` option actually names another axis; then the
    `anchor=`/`yshift=`/`xshift=` options that go with it are dropped as well.
    Options nested inside `title style={...}` etc. are untouched.  A lone axis
    has nothing to strip, and the function is a no-op.
    """
    m = re.match(r"(\s*\[)(.*?)(\]\s*)", axis_block, re.DOTALL)
    if not m:
        return axis_block, False
    head, opts, tail = m.groups()
    parsed = split_options(opts)
    anchors_a_sibling = any(
        re.match(r"\s*at\s*=", o) and "panel" in o for o in parsed
    )
    if not anchors_a_sibling:
        return axis_block, False
    kept = [
        o
        for o in parsed
        if not (
            (re.match(r"\s*at\s*=", o) and "panel" in o)
            or re.match(r"\s*(anchor|yshift|xshift)\s*=", o)
        )
    ]
    rebuilt = head + ",".join(kept) + tail + axis_block[m.end() :]
    return rebuilt, True


def extract_panels(paper_text):
    """Return every axis environment of every configured float, in page order."""
    n_floats = paper_text.count(r"\begin{figure}")
    assert n_floats == len(FIGURE_LABELS), (
        f"paper has {n_floats} figure floats but {len(FIGURE_LABELS)} are "
        "configured; a figure was added or removed"
    )

    panels = []
    for label in FIGURE_LABELS:
        figure, _ = find_environment(paper_text, "figure", must_contain=label)
        picture, _ = find_environment(figure, "tikzpicture")
        pos = 0
        while True:
            try:
                body, (_, j) = find_environment(picture, "axis", start=pos)
            except LookupError:
                break
            panels.append(body)
            pos = j

    assert len(panels) == len(EXPECTED_ADDPLOTS), (
        f"expected {len(EXPECTED_ADDPLOTS)} axis environments across "
        f"{', '.join(FIGURE_LABELS)}, found {len(panels)}"
    )
    for k, (body, expected) in enumerate(zip(panels, EXPECTED_ADDPLOTS)):
        got = body.count(r"\addplot")
        assert got == expected, (
            f"panel {k + 1}: expected {expected} \\addplot blocks, found {got}; "
            "the figure changed -- update EXPECTED_ADDPLOTS and recheck the "
            "caption claims"
        )

    cleaned = []
    for body in panels:
        body, _ = strip_relative_placement(body)
        assert "panel" not in body or "panelA" not in body, (
            "axis still references a sibling axis after stripping"
        )
        cleaned.append(body)
    return cleaned


# ---------------------------------------------------------------------------
# wrapper document
# ---------------------------------------------------------------------------
PREAMBLE = r"""% Generated by scripts/render_figures.py -- do not edit by hand.
% One figure per page; extracted from shields-2026-turan-bessel.tex.
\documentclass[11pt,a4paper]{article}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,mathtools}
\usepackage{pgfplots}
\pgfplotsset{compat=1.18}
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


def build_wrapper(panels):
    pages = "".join(PAGE % {"body": body} for body in panels).rstrip()
    # the trailing \newpage would leave an empty final page
    assert pages.endswith(r"\newpage")
    pages = pages[: -len(r"\newpage")]
    return PREAMBLE + pages + "\n\\end{document}\n"


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
        # PyMuPDF, so a 100-point polyline counts once; the segment count is
        # what tracks the plotted data.
        paths = page.get_drawings()
        segments = sum(len(p["items"]) for p in paths)
        assert len(paths) >= 10, f"page {k + 1} has only {len(paths)} vector paths"
        assert segments >= 100, (
            f"page {k + 1} has only {segments} path segments; curve data lost?"
        )
        assert not page.get_images(), (
            f"page {k + 1} contains a raster image; artwork must stay vector"
        )
        text = page.get_text()
        for landmark in LANDMARKS[k]:
            assert landmark in text, (
                f"page {k + 1} is missing the landmark {landmark!r}"
            )
        print(
            f"  page {k + 1}: {w:.0f}x{h:.0f}pt, "
            f"{len(paths)} paths / {segments} segments"
        )
    doc.close()


def main():
    assert shutil.which("pdflatex"), "pdflatex not found"
    panels = extract_panels(PAPER.read_text(encoding="utf-8"))
    print(f"extracted {len(panels)} panels from {', '.join(FIGURE_LABELS)}")

    WRAPPER.write_text(build_wrapper(panels), encoding="utf-8")
    print(f"wrote {WRAPPER.relative_to(PAPER_DIR)}")

    compile_pdf(WRAPPER)
    verify(len(panels))
    print(
        f"wrote {OUTPUT.relative_to(PAPER_DIR)} "
        f"({OUTPUT.stat().st_size / 1024:.0f} KB)"
    )


if __name__ == "__main__":
    main()
