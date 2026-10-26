#!/usr/bin/env python3
"""Cross-reference guard for every script in this directory, and for `README.md`.

Every reference to the paper is one of its `\\label`s, never a printed number.  Two checks:

  (1) every label-shaped token (`lem:...`, `thm:...`, `eq:...`, `sec:...`, ...) named in a
      guarded file is defined by a `\\label` in the manuscript;
  (2) no guarded file cites this paper by number -- `Lemma 2.4`, `Section 3`, `Theorem 6.1`,
      `Appendix B`, `(2.12)`.  Another work's numbering is exempt where it is attributed by a
      capitalized possessive or a named work (`Olson-Harris's Lemma 3.1`, `DLMF 10.38`), or
      where a whole unit declares it in `EXTERNAL_NUMBERING`; the README's first-column
      pinpoints (`| §4 Thm 4.1 | ...`) are exempt by their shape.

The scanner is mutation-tested at the start of every run: a planted defect of each kind must
be reported and each exempt form must stay silent, so a guard that scans nothing fails.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent / "shields-2026-skew-boundary-reconstruction.tex"

PREFIXES = ("lem", "prop", "thm", "cor", "eq", "sec", "subsec", "app", "def", "ex", "rem",
            "fig", "conj", "prob", "tab", "hyp")
LABEL_RE = re.compile(r"\b(?:%s):[A-Za-z0-9][A-Za-z0-9:_-]*" % "|".join(sorted(set(PREFIXES))))
NUMBER_RE = re.compile(
    r"\b(?:Lemma|Theorem|Proposition|Corollary|Section|Sections|Appendix|Remark|Example|"
    r"Definition|Conjecture|Figure)s?\s+[A-Z]?\d+(?:\.\d+)*[a-z]?\b"
    r"|\bApp(?:endix)?\s+[A-Z]\b"
    r"|(?<![\w.])\(\d+\.\d+\)")
# another work's numbering: capitalized possessive, or a named work, directly before it
ATTRIBUTED_RE = re.compile(r"(?:[A-Z][\w-]*['\u2019]s|DLMF|NIST)\s+$")


def defined_labels(tex):
    return set(re.findall(r"\\label\{([^}]+)\}", tex))


# A unit whose subject is another work's numbering declares it here, by file and work.  Its label
# checks still run; only the number scan is waived for it, and the run says which unit claimed it.
EXTERNAL_NUMBERING = {
    "check_composition_irreducibility.py": "McNamara and van Willigenburg, Trans. AMS 361 (2009)",
}


def clean(tok):
    return tok.rstrip(":-_")


def scan(text, labels, is_readme=False, external_numbering=False):
    """Return a list of (kind, line number, token)."""
    out = []
    for no, line in enumerate(text.splitlines(), 1):
        if is_readme and re.match(r"\|\s*(?:\u00a7|\\S)", line):
            cells = line.split("|")
            line = "|".join([""] + cells[2:])  # first-column pinpoint is exempt
        for m in LABEL_RE.finditer(line):
            tok = clean(m.group(0))
            if tok not in labels:
                out.append(("undefined label", no, tok))
        for m in NUMBER_RE.finditer(line):
            if external_numbering or ATTRIBUTED_RE.search(line[:m.start()]):
                continue
            out.append(("number citation", no, m.group(0)))
    return out


def self_test(labels):
    lab = sorted(labels)[0]
    planted = f"see `{lab}` and `lem:no-such-label-xyz` and Lemma 3.4 and Section 2 and (2.12)\n"
    kinds = [k for k, _, _ in scan(planted, labels)]
    assert kinds.count("undefined label") == 1, kinds
    assert kinds.count("number citation") == 3, kinds
    assert scan("Olson-Harris's Lemma 3.1 and DLMF Section 10.38\n", labels) == []
    assert scan("| \u00a76 Thm 6.1 | `x.py` | `%s` |\n" % lab, labels, is_readme=True) == []
    assert scan("| \u00a76 Thm 6.1 | `x.py` | Lemma 3.4 |\n", labels, is_readme=True)[0][0] == "number citation"
    # a declared external-numbering unit keeps its label check and drops only the number scan
    kinds = [k for k, _, _ in scan(planted, labels, external_numbering=True)]
    assert kinds == ["undefined label"], kinds
    print("PASS  scanner fires on planted defects and stays silent on exempt forms")


def guarded_files():
    """Every Python file beside this one (the shared modules and the FULL checks included, not only the
    scripts `run_all.sh` names), plus the README."""
    files = sorted(HERE.glob("*.py"))
    files.append(HERE / "README.md")
    return files


def main():
    labels = defined_labels(PAPER.read_text(encoding="utf-8"))
    assert len(labels) > 100, len(labels)
    self_test(labels)
    bad = []
    files = guarded_files()
    for f in files:
        if f.name == "check_paper_crossrefs.py":
            continue  # its own docstring and tests carry the planted forms
        ext = f.name in EXTERNAL_NUMBERING
        if ext:
            print("NOTE  %s cites %s by its own numbering (declared); label checks still run"
                  % (f.name, EXTERNAL_NUMBERING[f.name]))
        for kind, no, tok in scan(f.read_text(encoding="utf-8"), labels, f.name == "README.md", ext):
            bad.append(f"{f.name}:{no}: {kind}: {tok}")
    for b in bad:
        print("FAIL ", b)
    assert not bad, f"{len(bad)} cross-reference defects"
    print(f"PASS  {len(files)} files, {len(labels)} labels: every label resolves, no number citations")
    print("ALL PASS")


if __name__ == "__main__":
    sys.exit(main())
