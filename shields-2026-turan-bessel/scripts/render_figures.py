#!/usr/bin/env python3
r"""Render the manuscript's figures to a one-figure-per-page PDF.

The paper carries three floats: fig:phase-diagram, a bare tikzpicture schematic,
fig:defect-localization (a bare tikzpicture) and fig:wall-fan (a pgfplots axis).  Journal
submission systems want the artwork as its own file, one figure per page, with
the caption left in the manuscript text.  This script extracts the
axis environment from the manuscript itself -- not from a hand-kept copy, so
the artwork cannot drift from the paper -- and typesets it on its own A4 page in

    shields-2026-turan-bessel-figures.pdf

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
OUTPUT = PAPER_DIR / "shields-2026-turan-bessel-figures.pdf"

# every float to render, in the order it appears in the manuscript; one page
# each.  `kind` is "axis" for a pgfplots axis inside the tikzpicture and "tikz"
# for a bare tikzpicture whose body is the artwork.  `plots` is the expected
# number of \addplot blocks (axis) or \draw commands (tikz): a change means the
# figure was edited and its caption claims need rechecking too.  `landmarks` is
# text that must survive into the page, so a silently empty or reordered render
# fails, and `segments` is a floor on the vector path segments on that page.
FIGURES = (
    {
        "label": "fig:phase-diagram",
        "kind": "tikz",
        "plots": 5,
        "segments": 8,
        "landmarks": ("pointwise positivity", "coefficientwise failure",
                      "one positive zero"),
    },
    {
        "label": "fig:defect-localization",
        "kind": "tikz",
        "plots": 26,
        "segments": 80,
        "landmarks": ("0.3690738484", "indefinite", "self-pair", "mixed pairing"),
    },
    {
        "label": "fig:wall-fan",
        "kind": "axis",
        "plots": 26,
        "segments": 40,
        "landmarks": ("0.90", "1.15", "48"),
    },
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
    """Return (kind, body) for every configured float, in manuscript order."""
    n_floats = paper_text.count(r"\begin{figure}")
    assert n_floats == len(FIGURES), (
        f"paper has {n_floats} figure floats but {len(FIGURES)} are configured; "
        "a figure was added or removed"
    )

    panels = []
    for spec in FIGURES:
        label, kind = spec["label"], spec["kind"]
        # match the declaration, not the name: another float's caption may
        # cross-reference this label, and a bare substring would find that one
        figure, _ = find_environment(
            paper_text, "figure", must_contain=rf"\label{{{label}}}"
        )
        picture, _ = find_environment(figure, "tikzpicture")

        if kind == "tikz":
            try:
                find_environment(picture, "axis")
            except LookupError:
                pass
            else:
                raise AssertionError(
                    f"{label} is configured as a bare tikzpicture but now holds "
                    "an axis environment"
                )
            body, counted = picture, picture.count(r"\draw")
        else:
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
                f"{label}: expected one axis environment, found {len(bodies)}"
            )
            body, _ = strip_relative_placement(bodies[0])
            assert "panelA" not in body, (
                f"{label}: axis still references a sibling axis after stripping"
            )
            counted = body.count(r"\addplot")

        assert counted == spec["plots"], (
            f"{label}: expected {spec['plots']} plot commands, found {counted}; "
            "the figure changed -- update FIGURES and recheck the caption claims"
        )
        panels.append((kind, body))

    assert len(panels) == n_floats
    return panels


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
%(macros)s
\pagestyle{empty}
\begin{document}
"""

PAGE = r"""
\begin{center}
\vspace*{\fill}
%(art)s
\vspace*{\fill}
\end{center}
\newpage
"""

ART = {
    "axis": "\\begin{tikzpicture}\n\\begin{axis}%s\\end{axis}\n\\end{tikzpicture}",
    "tikz": "\\begin{tikzpicture}%s\\end{tikzpicture}",
}


MACRO = re.compile(r"^\\newcommand\{\\[A-Za-z]+\}(\[\d+\])?\{.*\}$", re.M)


def paper_macros(paper_text):
    """The artwork must render standalone, so the wrapper inherits every
    zero-argument macro the manuscript defines -- a figure body using one
    (\\MD, say) would otherwise fail to compile or, worse, render wrong."""
    head = paper_text[: paper_text.index(r"\begin{document}")]
    return "\n".join(m.group(0) for m in MACRO.finditer(head))


def build_wrapper(panels, macros):
    pages = "".join(
        PAGE % {"art": ART[kind] % body} for kind, body in panels
    ).rstrip()
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
        # PyMuPDF, so a 100-point polyline counts once; the segment count is
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
    print("extracted "
          + ", ".join(f"{s['label']} ({s['kind']})" for s in FIGURES))

    missing = [] if shutil.which("pdflatex") else ["pdflatex"]
    try:
        import fitz  # noqa: F401
    except ImportError:
        missing.append("PyMuPDF")
    if missing:
        print(f"SKIP: rendering needs {' and '.join(missing)}; the "
              f"{len(panels)}-float invariant and the per-figure plot counts "
              "were checked")
        print(f"\nALL PASS: render_figures -- {len(panels)} floats configured "
              "and counted (render skipped)")
        return

    WRAPPER.write_text(build_wrapper(panels, paper_macros(text)), encoding="utf-8")
    print(f"wrote {WRAPPER.relative_to(PAPER_DIR)}")

    compile_pdf(WRAPPER)
    verify(len(panels))
    assert len(panels) == text.count(r"\begin{figure}")
    print(
        f"wrote {OUTPUT.relative_to(PAPER_DIR)} "
        f"({OUTPUT.stat().st_size / 1024:.0f} KB)"
    )
    print(f"\nALL PASS: render_figures -- {len(panels)} figure floats in the "
          f"manuscript, {len(panels)} vector pages rendered")


if __name__ == "__main__":
    main()
