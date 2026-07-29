#!/usr/bin/env python3
"""Sense-check the paper's terms against the extracted text of every cited work.

For each probe phrase, report which cited works use it and quote one context
line, so a term the field uses for a *different* object is visible.
"""
import hashlib, os, re, sys, glob

REFS = "/mnt/c/workspace/riemann2/rh-v3/papers/turan-bessel/refs"
CACHE = "/tmp/draft-terminology-cache"

def cache_path(path):
    st = os.stat(path)
    h = hashlib.sha1(("%s|%d|%d" % (os.path.abspath(path), st.st_size,
                                    int(st.st_mtime))).encode()).hexdigest()[:20]
    return os.path.join(CACHE, h + ".txt")

# map cache file -> ref basename
texts = {}
for f in sorted(os.listdir(REFS)):
    p = os.path.join(REFS, f)
    if not os.path.isfile(p):
        continue
    cp = cache_path(p)
    if os.path.exists(cp):
        texts[f] = open(cp, encoding="utf-8", errors="replace").read()
# arXiv source tarballs: the loader extracts .tex; try sibling cache too
print("cached works: %d of %d files in refs/" % (len(texts), len(os.listdir(REFS))))
missing = [f for f in sorted(os.listdir(REFS))
           if os.path.isfile(os.path.join(REFS, f)) and f not in texts]
print("no cache for: %s\n" % (", ".join(missing) or "none"))

PROBES = [
    "coefficientwise", "coefficient-wise", "coefficient wise",
    "Turanian", "Turanians", "Turan determinant", "Turan-type determinant",
    "Euler derivative", "Euler operator",
    "absolutely monotone", "absolutely monotonic", "absolute monotonicity",
    "completely monotone", "completely monotonic",
    "Schur complement", "Schur determinant", "Schur matrix",
    "Bessel-Schur", "matrix Turan",
    "log-concavity in the parameter", "order derivative",
    "mixed derivative", "diagonal congruence", "congruence",
]

def norm(s):
    s = s.replace("á", "a").replace("é", "e").replace("–", "-")
    s = s.replace("—", "-").replace("’", "'")
    return re.sub(r"\s+", " ", s)

for probe in PROBES:
    pat = re.compile(re.escape(probe).replace(r"\ ", r"[\s\-]+"), re.I)
    hits = []
    for name, txt in texts.items():
        t = norm(txt)
        found = list(pat.finditer(t))
        if found:
            m = found[0]
            ctx = t[max(0, m.start()-110):m.end()+110].strip()
            hits.append((name, len(found), ctx))
    print("=" * 78)
    print("PROBE  %-30s  %d work-file(s)" % (probe, len(hits)))
    for name, n, ctx in sorted(hits, key=lambda r: -r[1])[:6]:
        print("  [%s] x%d" % (name, n))
        print("      ...%s..." % ctx[:230])
    if not hits:
        print("  (no cited work uses this)")
    print()
