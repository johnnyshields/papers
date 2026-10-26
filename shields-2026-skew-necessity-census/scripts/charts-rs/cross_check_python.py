#!/usr/bin/env python3
"""Compare the Rust port with the pinned Python on every connected profile of 2..M cells.

For each profile F, the legal marks of F (read as an inner) and the search-B charts of F reported by
`skew-charts dump --max M` must equal those of the pinned `skew_compose.py`, as sets.  This tests the
port of Hypotheses I--IV, the attachment cases, the composition, and search B directly against the
code the paper's results through 26 were computed with.

Usage: python3 cross_check_python.py --binary PATH [--max 11]
"""
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PINNED = HERE.parent / 'census-rs' / '_pinned'
SNAPSHOT = json.loads((PINNED / 'snapshot.json').read_bytes())


def load(name):
    path = PINNED / name
    assert hashlib.sha256(path.read_bytes()).hexdigest() == SNAPSHOT['files'][name]['sha256']
    spec = importlib.util.spec_from_file_location('pinned_' + path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = load('skew_core.py')
K = load('skew_compose.py')


def cells(x):
    return frozenset(tuple(c) for c in x)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--binary', required=True)
    ap.add_argument('--max', type=int, default=11)
    args = ap.parse_args()
    out = subprocess.run([args.binary, 'dump', '--max', str(args.max), '--threads', '1'],
                         check=True, capture_output=True, text=True).stdout
    n = nmarks = ncharts = 0
    for line in out.splitlines():
        rec = json.loads(line)
        F = C.cells(tuple(map(tuple, rec['profile'])))
        rust_marks = {(cells(m['b']), cells(m['t']), m['case'], tuple(m['v']), m['q']) for m in rec['marks']}
        py_marks = set(K.marks(F))
        assert rust_marks == py_marks, ('marks differ', rec['profile'], rust_marks ^ py_marks)
        rust_band = {(cells(c['d']), cells(c['e']), cells(c['mark']['b']), cells(c['mark']['t']),
                      c['mark']['case'], c['mark']['q']) for c in rec['band']}
        py_band = {k + (q,) for k, q in K.finder_band(F).items()}
        assert rust_band == py_band, ('search B differs', rec['profile'])
        n += 1
        nmarks += len(py_marks)
        ncharts += len(py_band)
    assert n == sum(C.dp_counts(args.max)[2:])
    print(f'PASS: on all {n} connected profiles of 2..{args.max} cells the Rust port returns the pinned '
          f'Python\'s {nmarks} legal marks and {ncharts} search-B charts exactly')


if __name__ == '__main__':
    main()
