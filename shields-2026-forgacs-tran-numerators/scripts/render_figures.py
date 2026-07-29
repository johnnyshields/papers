#!/usr/bin/env python3
r"""Render the manuscript's figure panels to a one-panel-per-page PDF.

Figure 1 of the paper (fig:decomposition-and-defect) is a single float holding
two pgfplots axis environments, panel (A) and panel (B), under one caption.
Journal submission systems want the artwork as its own file, one figure per
page, with the caption left in the manuscript text.  This script extracts the
two axis environments from the manuscript itself -- not from a hand-kept copy,
so the artwork cannot drift from the paper -- and typesets each on its own A4
page in

    shields-2026-forgacs-tran-numerators-figures.pdf

Panel (B) is positioned relative to panel (A) inside the float
(at={(panelA.below south west)}); that placement is stripped here, since each
panel stands alone.  The generated wrapper is written to
scripts/figures_pages.tex for inspection.

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
PAPER = PAPER_DIR / "shields-2026-forgacs-tran-numerators.tex"
WRAPPER = PAPER_DIR / "scripts" / "figures_pages.tex"
OUTPUT = PAPER_DIR / "shields-2026-forgacs-tran-numerators-figures.pdf"

FIGURE_LABEL = "fig:decomposition-and-defect"

# expected \addplot count per panel, in source order; a change here means the
# figure was edited and the caption claims need rechecking too
EXPECTED_ADDPLOTS = (5, 7)

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
    Options nested inside `title style={...}` etc. are untouched.
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
    n_floats = paper_text.count(r"\begin{figure}")
    assert n_floats == 1, (
        f"paper has {n_floats} figure floats but only {FIGURE_LABEL} is "
        "configured; a figure was added or removed"
    )

    figure, _ = find_environment(paper_text, "figure", must_contain=FIGURE_LABEL)
    picture, _ = find_environment(figure, "tikzpicture")

    panels, pos = [], 0
    while True:
        try:
            body, (_, j) = find_environment(picture, "axis", start=pos)
        except LookupError:
            break
        panels.append(body)
        pos = j

    assert len(panels) == len(EXPECTED_ADDPLOTS), (
        f"expected {len(EXPECTED_ADDPLOTS)} axis environments in "
        f"{FIGURE_LABEL}, found {len(panels)}"
    )
    for k, (body, expected) in enumerate(zip(panels, EXPECTED_ADDPLOTS)):
        got = body.count(r"\addplot")
        assert got == expected, (
            f"panel {k + 1}: expected {expected} \\addplot blocks, found {got}; "
            "the figure changed -- update EXPECTED_ADDPLOTS and recheck the "
            "caption claims"
        )

    cleaned = []
    for k, body in enumerate(panels):
        body, stripped = strip_relative_placement(body)
        if k > 0:
            assert stripped, (
                f"panel {k + 1} carries no sibling-relative placement to strip; "
                "check whether the figure layout changed"
            )
        assert "panelA" not in body or k == 0, (
            f"panel {k + 1} still references panelA after stripping"
        )
        cleaned.append(body)

    # panel A must not depend on anything either
    assert "panelB" not in cleaned[0], "panel A references panelB"
    return cleaned


# ---------------------------------------------------------------------------
# wrapper document
# ---------------------------------------------------------------------------
PREAMBLE = r"""% Generated by scripts/render_figures.py -- do not edit by hand.
% One figure panel per page; extracted from
% shields-2026-forgacs-tran-numerators.tex (fig:decomposition-and-defect).
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
    pages = "".join(PAGE % {"body": body} for body in panels)
    # the trailing \newpage would leave an empty final page
    pages = pages.rstrip()
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
        # PyMuPDF, so a 300-point polyline counts once; the segment count is
        # what tracks the plotted data.
        paths = page.get_drawings()
        segments = sum(len(p["items"]) for p in paths)
        assert len(paths) >= 10, f"page {k + 1} has only {len(paths)} vector paths"
        assert segments >= 150, (
            f"page {k + 1} has only {segments} path segments; curve data lost?"
        )
        assert not page.get_images(), (
            f"page {k + 1} contains a raster image; artwork must stay vector"
        )
        text = page.get_text()
        assert text.strip(), f"page {k + 1} has no text (labels lost?)"
        print(
            f"  page {k + 1}: {w:.0f}x{h:.0f}pt, "
            f"{len(paths)} paths / {segments} segments"
        )

    # panel-specific landmarks, so a page-order swap is caught
    p1, p2 = doc[0].get_text(), doc[1].get_text()
    assert "(A)" in p1, "page 1 is not panel (A)"
    assert "(B)" in p2, "page 2 is not panel (B)"
    assert "40" in p1, "panel (A) y-tick labels missing"
    assert "exceptional" in p2 and "indices" in p2, (
        "panel (B) annotation missing"
    )
    assert "14" in p2 and "38" in p2, "panel (B) legend entries missing"
    doc.close()


def main():
    assert shutil.which("pdflatex"), "pdflatex not found"
    paper_text = PAPER.read_text(encoding="utf-8")
    panels = extract_panels(paper_text)
    print(f"extracted {len(panels)} panels from {FIGURE_LABEL}")

    WRAPPER.write_text(build_wrapper(panels), encoding="utf-8")
    print(f"wrote {WRAPPER.relative_to(PAPER_DIR)}")

    compile_pdf(WRAPPER)
    verify(len(panels))
    size = OUTPUT.stat().st_size
    print(f"wrote {OUTPUT.relative_to(PAPER_DIR)} ({size / 1024:.0f} KB)")


if __name__ == "__main__":
    main()
