#!/usr/bin/env python3
"""Audit final census files and chart certificates before resuming a stopped run.

Only final .json names are accepted as results. Temporary files and hot sorted
runs never certify a completed area or shard.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
from cross_check import atomic_json
from run_logged import publish

HERE = Path(__file__).resolve().parent


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def prof(raw):
    return tuple(raw[0]), tuple(raw[1])


def rotate(p):
    return p[0][::-1], p[1][::-1]


def valid(p, area):
    r, g = p
    return (r and sum(r) == area and all(x > 0 for x in r)
            and len(g)+1 == len(r)
            and all(0 <= v < min(r[i], r[i+1]) for i, v in enumerate(g)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work', type=Path, default=Path('/mnt/d/mvw-rust'))
    ap.add_argument('--scratch', type=Path, default=Path('/home/shields/r167-lanes/_rust35'))
    ap.add_argument('--interrupted-area', type=int, default=34)
    args = ap.parse_args()
    scale = {r['area']: r for r in json.loads((args.work / 'scale.json').read_bytes())}
    snapshot = json.loads((HERE / '_pinned/snapshot.json').read_bytes())
    for name, info in snapshot['files'].items():
        assert digest(HERE / '_pinned' / name) == info['sha256'], ('changed pinned source', name)
    checked = []
    timing_copies_repaired = []
    for path in sorted(args.work.glob('area-[0-9][0-9].json')):
        a = json.loads(path.read_bytes())
        n = a['area']
        assert path.name == f'area-{n:02}.json' and a['format'] == 'skew-census-v1'
        assert a['controls_passed'] is True
        assert a['profiles'] == scale[n]['profiles']
        assert a['rotation_orbits'] == scale[n]['rotation_orbits']
        assert 2*a['rotation_orbits']-a['profiles'] == a['fixed']
        assert sum(a['histogram'].values()) == a['classes']
        assert sum(int(k)*v for k, v in a['histogram'].items()) == a['profiles']
        assert len(a['nonrotation']) == a['nonrotation_classes']
        seen = set()
        expected = Counter({1: a['fixed'], 2: a['rotation_orbits']-a['fixed']})
        for cl in a['nonrotation']:
            ps = {prof(p) for p in cl}
            assert len(ps) == len(cl) and not (seen & ps)
            seen |= ps
            assert all(valid(p, n) and rotate(p) in ps for p in ps)
            reps = {min(p, rotate(p)) for p in ps}
            assert len(reps) >= 2
            assert len({tuple(sorted(p[0])) for p in ps}) == 1
            assert len({tuple(sorted(p[1])) for p in ps}) == 1
            for p in reps:
                expected[1 if p == rotate(p) else 2] -= 1
            expected[len(ps)] += 1
        assert len(seen) == a['nonrotation_members']
        assert {str(k): v for k, v in expected.items() if v} == a['histogram']
        repository_path = HERE / 'results' / path.name
        if digest(path) != digest(repository_path):
            copied = json.loads(repository_path.read_bytes())
            assert set(copied) == set(a)
            for key in a:
                if key in ('seconds', 'shard_seconds'):
                    assert math.isclose(copied[key], a[key], rel_tol=1e-14, abs_tol=1e-12), (n, key)
                else:
                    assert copied[key] == a[key], ('repository data differs', n, key)
            assert publish(repository_path, path.read_bytes())
            timing_copies_repaired.append(n)
        checked.append(n)
    assert checked == list(range(1, len(checked)+1)), 'noncontiguous complete areas'
    gate = json.loads((args.work / 'cross-check.json').read_bytes())
    assert gate['passed'] and gate['through'] == 26
    for row in gate['compared']:
        assert digest(args.work / f"area-{row['area']:02}.json") == row['rust_sha256']
    root_areas = []
    for n in range(27, len(checked)+1):
        a = json.loads((args.work / f'area-{n:02}.json').read_bytes())
        r = json.loads((args.work / f'roots-keys-{n:02}.json').read_bytes())
        assert r['census_sha256'] == digest(args.work / f'area-{n:02}.json')
        assert r['classes'] == r['source_minimal_key_classes'] == a['nonrotation_classes']
        assert r['members'] == r['rooted'] == r['band_window_agreement_members'] == a['nonrotation_members']
        for name, info in snapshot['files'].items():
            assert r['finder_hashes'][name] == info['sha256']
        assert r['finder_snapshot_utc'] == snapshot['captured_utc']
        assert len(r['witnesses']) == len(a['nonrotation'])
        for i, witness in enumerate(r['witnesses']):
            assert witness['index'] == i and witness['window_agreement']
            assert witness['finder_hashes'] == r['finder_hashes']
            assert witness['chosen_source_minimal_key'] in witness['source_minimal_keys']
            assert [p['profile'] for p in witness['members']] == a['nonrotation'][i]
            for member in witness['members']:
                p = prof(member['profile'])
                q = member['chart']['period']
                diagonals = sum(p[0])-sum(p[1])
                assert member['score'] == [diagonals % q, q+diagonals % q]
                assert q in member['periods']
                assert member['all_charts'] >= member['source_minimal_charts'] >= 1
        summary = {k: v for k, v in r.items() if k != 'witnesses'}
        assert summary == json.loads((HERE / 'results' / f'roots-keys-{n:02}.json').read_bytes())
        root_areas.append(n)
    interrupted = args.interrupted_area
    assert interrupted not in checked, 'requested interrupted area is already final'
    assert not (args.work / f'roots-keys-{interrupted:02}.json').exists()
    assert not (args.work / f'complete-{interrupted:02}.json').exists()
    checkpoints = list((args.work / 'checkpoints' / f'area-{interrupted:02}').glob('*.json'))
    checkpoint_profiles = 0
    for path in checkpoints:
        s = json.loads(path.read_bytes())
        parts = [int(x) for x in path.stem.split('-')]
        assert s['format'] == 'skew-census-v1' and s['parts'] == parts and sum(parts) == interrupted
        assert sum(int(k)*v for k, v in s['histogram'].items()) == s['profiles']
        assert 2*s['rotation_orbits']-s['profiles'] == s['fixed']
        checkpoint_profiles += s['profiles']
    hot = args.scratch / 'hot' / f'area-{interrupted:02}'
    runs = list(hot.rglob('*.bin')) if hot.exists() else []
    temporary = list(args.work.glob('*.tmp'))
    temporary += list((args.work / 'checkpoints' / f'area-{interrupted:02}').glob('*.tmp'))
    report = dict(checked_utc=datetime.now(timezone.utc).isoformat(), complete_census_areas=checked,
                  complete_roots_key_areas=root_areas, interrupted_area=interrupted,
                  complete_shards=len(checkpoints), checkpoint_profiles=checkpoint_profiles,
                  required_shards=scale[interrupted]['row_multisets'],
                  unfinished_sort_runs=len(runs), unfinished_sort_bytes=sum(p.stat().st_size for p in runs),
                  ignored_temporary_files=[str(p.relative_to(args.work)) for p in temporary],
                  timing_serialization_copies_restored=timing_copies_repaired,
                  passed=True)
    atomic_json(args.work / f'recovery-audit-{interrupted:02}.json', report)
    atomic_json(HERE / 'results' / f'recovery-audit-{interrupted:02}.json', report)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
