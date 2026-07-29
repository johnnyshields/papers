#!/usr/bin/env python3
"""Citation check, cross-cutting: every DLMF locator cited in
shields-2026-turan-bessel.tex, against the local section copies in refs/.

Checks the mathematical content behind each locator, not merely that the label
string occurs somewhere on the page.  Hard failure on any mismatch: unresolved
locators are collected and raise SystemExit at the end, and a missing refs/ copy
raises FileNotFoundError rather than being silently skipped.

Locators cited by the paper, and where: 5.15.1 (sec:gram and sec:continuation),
10.25.2 (eq:I-Z), 10.17.1 / 10.40.1 / 10.40(iii) (the Lemma 7.1 proof),
10.38 (sec:context).
"""
import html
import os
import re
import unicodedata

_HERE = os.path.dirname(os.path.abspath(__file__))
_PAPER = os.path.dirname(_HERE)
REFS = os.path.join(_PAPER, "refs")
TEX = os.path.join(_PAPER, "shields-2026-turan-bessel.tex")

def text_of(fname):
    s = open(os.path.join(REFS, fname), encoding="utf-8").read()
    s = re.sub(r"<style[^>]*>.*?</style>", " ", s, flags=re.I | re.S)
    t = re.sub(r"<[^>]+>", " ", s)
    return re.sub(r"\s+", " ", html.unescape(t))

def squash(s):
    """Strip whitespace AND the invisible math-layout characters DLMF interleaves
    (U+2061 FUNCTION APPLICATION, U+2062 INVISIBLE TIMES, U+2063/4, ZWSP, and any
    other Cf-category formatting char), so glyph sequences compare literally."""
    out = [c for c in s
           if not c.isspace()
           and unicodedata.category(c) != "Cf"
           and c not in "\u2061\u2062\u2063\u2064\u200b\u2064"]
    return "".join(out)

def eq(txt, label, span=340, must=()):
    """Rendered text following `label`.  When `must` is given, scan every
    occurrence and return the first whose window contains all those substrings
    (post-squash) -- DLMF mentions equation numbers in prose as well as at the
    numbered display."""
    best = None
    for m in re.finditer(re.escape(label) + r"(?!\d)", txt):
        w = txt[m.end(): m.end() + span]
        if best is None:
            best = w
        # require the must-strings near the START of the window, so we land on the
        # numbered display rather than a prose cross-reference that merely
        # mentions the label and happens to be followed by the equation.
        if must and all(t in squash(w)[:150] for t in must):
            return w
    assert best is not None, f"label {label} absent"
    return best

fails = []
def check(label, cond, detail=""):
    print(f"  {'OK  ' if cond else 'FAIL'}  {label}" + (f"\n          {detail}" if detail else ""))
    if not cond:
        fails.append(label)

G   = text_of("NISTDLMFGamma_5.15.html")
B17 = text_of("NISTDLMFBessel_10.17.html")
B25 = text_of("NISTDLMFBessel_10.25.html")
B40 = text_of("NISTDLMFBessel_10.40.html")
O38 = text_of("NISTDLMFOrder_10.38.html")

print("archive integrity")
for nm, t in [("5.15", G), ("10.17", B17), ("10.25", B25), ("10.40", B40), ("10.38", O38)]:
    check(f"{nm}: Greek intact, no mojibake",
          ("Ïˆ" not in t and "Î½" not in t) and (("ψ" in t) or ("ν" in t) or ("Γ" in t)))

# ---- eq. 5.15.1, cited for psi_1(y) = sum_{r>=0} (y+r)^{-2} -----------------
print("\n5.15.1  (trigamma series; cited at eq:trigamma-integral and eq:trigamma-partial-fraction)")
e = eq(G, "5.15.1")
s = squash(e)
check("is psi'(z) = sum_{k=0}^inf 1/(k+z)^2",
      "ψ" in e and "′" in e and "1(k+z)2" in s and "∑k=0" in s, e[:120].strip())
check("§5.15 is the Polygamma Functions section", "Polygamma" in G[:4000])

# ---- eq. 10.17.1, cited jointly with 10.40.1 for the log I_nu expansion -----
print("\n10.17.1  (cited with 10.40.1 for log I_nu = z - (1/2)log(2 pi z) - (4nu^2-1)/(8z) + O(z^-2))")
e = eq(B17, "10.17.1", must=("ak", "(4ν2−12)")); s = squash(e)
check("defines the Hankel coefficients a_k(nu)", "a" in e and "ν" in e and "!" in s, e[:140].strip())
check("a_k(nu) numerator starts (4nu^2-1^2)(4nu^2-3^2)",
      "(4ν2−12)" in s and "(4ν2−32)" in s,
      "so a_1(nu) = (4nu^2-1)/8, matching the paper's (4nu^2-1)/(8z) term")
check("§10.17 is 'Asymptotic Expansions for Large Argument'",
      "Asymptotic Expansions for Large Argument" in B17[:8000])

# ---- eq. 10.25.2, cited for I_{a-1}(2 sqrt lambda) = lambda^{(a-1)/2} Z ----
print("\n10.25.2  (cited at eq:I-Z)")
e = eq(B25, "10.25.2", must=("Iν(z)=", "Γ(ν+k+1)")); s = squash(e)
check("is I_nu(z) = (z/2)^nu sum (z^2/4)^k / (k! Gamma(nu+k+1))",
      "Iν" in s and "(12z)ν" in s and "(14z2)k" in s and "Γ(ν+k+1)" in s, e[:170].strip())
# The paper's substitution nu = a-1, z = 2 sqrt(lambda) turns 10.25.2 into eq:I-Z:
#   (z/2)^nu -> lambda^{(a-1)/2}; (z^2/4)^k -> lambda^k; Gamma(nu+k+1) -> Gamma(a+k).
# That is an identity about the paper, not about this archive, so it is NOT checked
# here -- verify_bessel_reduction.py asserts eq. (6.1) numerically.  Printed as a
# note rather than as a check(), so nothing claims a verdict it did not compute.
print("  note  substituting nu=a-1, z=2 sqrt(lambda) gives lambda^{(a-1)/2} Z(a,lambda)")
print("          -- asserted in verify_bessel_reduction.py, eq. (6.1)")
check("§10.25 defines the modified Bessel functions",
      "Modified Bessel Functions" in B25[:8000])

# ---- eq. 10.40.1 and §10.40(iii) -------------------------------------------
print("\n10.40.1 and §10.40(iii)  (cited in the proof of lem:large-argument-limit)")
e = eq(B40, "10.40.1", span=460, must=("Iν", "ez", "|phz|≤12π−δ")); s = squash(e)
check("is the I_nu large-argument expansion with e^z/(2 pi z)^{1/2} prefactor",
      "Iν" in s and "ez" in s and "(2πz)12" in s, e[:170].strip())
check("carries the sector |ph z| <= pi/2 - delta",
      "12π−δ" in s or "|phz|≤12π−δ" in s,
      "matches the paper's 'arg z bounded away from +-pi/2'")
titles = dict(re.findall(r"§?10\.40\((i+v?|v)\)\s*([A-Z][A-Za-z ]{6,60})", B40))
print("          subsections:", {k: v.strip()[:46] for k, v in titles.items()})
check("10.40(iii) = 'Error Bounds for Complex Argument and Order'",
      "Error Bounds for Complex Argument and Order" in titles.get("iii", ""),
      "the paper's uniformity clause needs COMPLEX order -- correct locator")
check("10.40(ii) = 'Error Bounds for Real Argument and Order' (so (ii) would be wrong)",
      "Error Bounds for Real Argument and Order" in titles.get("ii", ""))
check("exactly four subsections (i)-(iv)", set(titles) == {"i", "ii", "iii", "iv"},
      str(sorted(titles)))
# the nu-derivative part: K_nu only, first order -- why the citation shortcut fails
e8 = eq(B40, "10.40.8", span=200, must=("∂Kν",))
check("10.40.8 (nu-derivative) is for K_nu, first order only",
      "K" in e8 and "∂" in e8 and "I" not in squash(e8).replace("Improved", ""),
      e8[:120].strip())

# ---- §10.38 ----------------------------------------------------------------
print("\n§10.38  (cited in sec:context)")
check("10.38 is 'Derivatives with Respect to Order'",
      "Derivatives with Respect to Order" in O38[:8000])
check("10.38 has equation bodies (10.38.1)", "10.38.1" in O38)

# ---- every cited locator is covered ---------------------------------------
print("\ncoverage: every DLMF locator in the .tex resolves locally")
tex = open(TEX, encoding="utf-8").read()
cited = set()
for m in re.finditer(r"\\cite\[([^\]]*)\]\{(NISTDLMF[A-Za-z]+)\}", tex):
    cited |= set(re.findall(r"\d+\.\d+(?:\.\d+)?(?:\((?:i+v?|v)\))?", m.group(1)))
pages = {"5.15.1": G, "10.17.1": B17, "10.25.2": B25,
         "10.40.1": B40, "10.40(iii)": B40, "10.38": O38}
print("          cited:", sorted(cited))
for tok in sorted(cited):
    check(f"{tok} present in its local section page",
          tok in pages and (tok.split("(")[0] in pages[tok]))
check("no cited locator lacks a page", not (cited - set(pages)), str(sorted(cited - set(pages))))
# symmetric: a page we check that the paper no longer cites is equally a defect
check("no checked page is uncited", not (set(pages) - cited), str(sorted(set(pages) - cited)))

print()
if fails:
    raise SystemExit("FAILED: " + "; ".join(fails))
print("ALL PASS: verify_dlmf_locators -- every cited DLMF locator matches its local copy")
