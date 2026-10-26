#!/usr/bin/env python3
"""Compare completed Rust areas with the independent Python census checkpoints.

Only reads the Python harness's trusted local pickle files; no census routines
are imported. A gate certificate is written only after every assertion passes.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
import os
from pathlib import Path
import pickle
import time


def atomic_json(path, obj):
    data = json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()
    path = Path(path)
    for attempt in range(9):
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_suffix(path.suffix + '.tmp')
            with open(tmp, 'wb') as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(tmp, path)
            return
        except OSError:
            if attempt == 8:
                raise
            time.sleep(min(2 ** attempt, 30))


def members(classes):
    return sorted(tuple(sorted((tuple(p[0]), tuple(p[1])) for p in cl)) for cl in classes)


def python_area(path):
    # These are user-specified, trusted local census outputs, not downloaded data.
    with open(path, 'rb') as stream:
        result = pickle.load(stream)
    hist = Counter()
    nonrotation = []
    profiles = orbits = 0
    for shard in result['shards'].values():
        hist.update(shard['hist'])
        profiles += shard['profiles']
        orbits += shard['reps']
        nonrotation.extend(shard['nontrivial'])
    return dict(area=result['N'], profiles=profiles, rotation_orbits=orbits,
                classes=sum(hist.values()), histogram={str(k): v for k, v in hist.items() if v},
                nonrotation=nonrotation)


def compare(rust, python):
    for field in ('area', 'profiles', 'rotation_orbits', 'classes', 'histogram'):
        assert rust[field] == python[field], (rust['area'], field, rust[field], python[field])
    assert members(rust['nonrotation']) == members(python['nonrotation']), ('member sets', rust['area'])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--python-work', default='/home/shields/r167-lanes/_basepaper/full')
    ap.add_argument('--work', default='/mnt/d/mvw-rust')
    ap.add_argument('--summary', default=str(Path(__file__).resolve().parent / 'results'))
    ap.add_argument('--through', type=int, default=26)
    args = ap.parse_args()
    assert 1 <= args.through <= 26
    rows = []
    nt23 = members23 = 0
    for area in range(1, args.through + 1):
        py_path = Path(args.python_work) / f'area-{area:02}.pkl'
        rs_path = Path(args.work) / f'area-{area:02}.json'
        rust = json.loads(rs_path.read_bytes())
        python = python_area(py_path)
        compare(rust, python)
        bad = copy.deepcopy(rust)
        bad['classes'] += 1
        try:
            compare(bad, python)
        except AssertionError:
            pass
        else:
            raise AssertionError('planted wrong class count was accepted')
        if area <= 23:
            nt23 += rust['nonrotation_classes']
            members23 += rust['nonrotation_members']
        rows.append(dict(area=area, profiles=rust['profiles'], classes=rust['classes'],
                         histogram=rust['histogram'], nonrotation=rust['nonrotation_classes'],
                         members=rust['nonrotation_members'],
                         rust_sha256=hashlib.sha256(rs_path.read_bytes()).hexdigest(),
                         python_sha256=hashlib.sha256(py_path.read_bytes()).hexdigest()))
        print(f"PASS N={area}: profiles, rotation orbits, classes, full histogram, all member sets", flush=True)
    if args.through >= 23:
        assert (nt23, members23) == (1104, 4424), (nt23, members23)
    certificate = dict(passed=True, through=args.through, compared=rows,
                       controls=dict(planted_wrong_count_rejected=True),
                       through23=dict(nonrotation_classes=nt23, members=members23))
    atomic_json(Path(args.work) / 'cross-check.json', certificate)
    atomic_json(Path(args.summary) / 'cross-check.json', certificate)
    print(f'ALL PASS: independent exact cross-check through {args.through}; through 23: {nt23} classes / {members23} members')


if __name__ == '__main__':
    main()
