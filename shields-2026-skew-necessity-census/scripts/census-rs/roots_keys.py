#!/usr/bin/env python3
"""Call the existing complete chart finders on Rust census member lists.

Every member receives a proper Hypotheses I--IV chart. All source-minimal key
sets are compared within each class, and the ordinary-gauge key is asserted to
be unique. Checkpoints contain full witnesses, not only success counts.
"""
import argparse
from collections import Counter
import hashlib
import gc
import importlib.util
import json
import multiprocessing as mp
import os
from pathlib import Path
import resource
import sys
import time
from functools import lru_cache

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
from cross_check import atomic_json

SNAPSHOT = json.loads((HERE / '_pinned' / 'snapshot.json').read_bytes())
FINDER_HASHES = {name: info['sha256'] for name, info in SNAPSHOT['files'].items()}


def load_pinned(name):
    path = HERE / '_pinned' / name
    assert hashlib.sha256(path.read_bytes()).hexdigest() == FINDER_HASHES[name], ('pinned source changed', name)
    spec = importlib.util.spec_from_file_location('census_pinned_' + path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = load_pinned('skew_core.py')
K = load_pinned('skew_compose.py')
W = None


def score(F, q):
    width = K.nd(F) % q
    return width, q + width


@lru_cache(maxsize=None)
def outer_polynomial(D):
    return tuple(sorted(C.jt_poly(C.profile_of_cells(D)).items()))


def key_of(chart, corrupt=False):
    D, E, B, T, case, v, _ = chart
    outer = K.transpose(D) if corrupt else D
    return K.canon_marked(E, B, T, case, v), outer_polynomial(outer)


def gauge_key(chart):
    D, E, B, T, case, v, q = chart
    if B and case == 'b':
        alternatives = set()
        for bottom, top, kind, shift, period in K.marks(E):
            if kind == 'a' and period == q and shift == (v[0] + 1, v[1] + 1):
                assert K.compose(K.antitranspose(D), E, bottom, top, kind, shift) == K.compose(*chart[:6])
                alternatives.add(key_of((K.transpose(D), E, bottom, top, kind, shift, period)))
        if alternatives:
            assert len(alternatives) == 1
            return next(iter(alternatives))
    return key_of(chart)


def chart_ok(F, chart, q):
    D, E, B, T, case = chart
    if min(len(D), len(E)) < 2 or not K.is_connected_skew(D) or not K.is_connected_skew(E):
        return 'not a proper chart'
    legal = [m for m in K.marks(E) if m[:3] == (B, T, case) and m[4] == q]
    if len(legal) != 1:
        return 'illegal mark'
    if K.compose(D, E, B, T, case, legal[0][3]) != F:
        return 'recomposition failed'
    if not K.private_heights_hold(F, D, E, q) or not K.size_bound_holds(F, D, E, q):
        return 'private heights or size bound failed'
    if score(F, q) != (K.nd(B), K.nd(E)):
        return 'chart score failed'
    return None


def window_charts(F):
    raw = W.w_roots(F)
    normalized = {}
    empty_a = {}
    empty_b = {}
    for (D, E, B, T, case), q in raw.items():
        mark = [m for m in W.marks_q(E, q) if m[:3] == (B, T, case)]
        assert len(mark) == 1
        assert W.eng.compose(D, E, B, T, case, mark[0][3]) == F
        if not B and case == 'b':
            assert not T
            D, case = K.antitranspose(D), 'a'
            empty_b[(D, E, B, T, case)] = q
        elif not B and case == 'a':
            empty_a[(D, E, B, T, case)] = q
        key = (D, E, B, T, case)
        assert chart_ok(F, key, q) is None
        assert K.nd(B) == K.nd(E)-q
        if key in normalized:
            assert normalized[key] == q
        normalized[key] = q
    assert empty_a == empty_b, ('window empty readings disagree after gauge', C.profile_of_cells(F))
    return normalized, len(empty_b)


def profile(raw):
    return tuple(raw[0]), tuple(raw[1])


def serialize_chart(c):
    D, E, B, T, case, v, q = c
    return dict(outer_profile=C.profile_of_cells(D), inner_profile=C.profile_of_cells(E),
                outer_cells=sorted(D), inner_cells=sorted(E), bottom_mark=sorted(B),
                top_mark=sorted(T), case=case, displacement=v, period=q)


def measure(classes, limit):
    # Spread the sample through the deterministic member ordering, including ends.
    members = sorted(profile(p) for cl in classes for p in cl)
    idx = sorted({i * (len(members)-1) // max(1, limit-1) for i in range(min(limit, len(members)))})
    band = sub = 0.
    for i in idx:
        F = C.cells(members[i])
        t = time.monotonic()
        b = K.finder_band(F)
        band += time.monotonic()-t
        t = time.monotonic()
        s = K.finder_subdiagram(F)
        sub += time.monotonic()-t
        assert b == s and b
    result = dict(sample=len(idx), members=len(members), band_seconds=band, subdiagram_seconds=sub,
                  projected_band_core_seconds=band * len(members) / len(idx),
                  projected_subdiagram_core_seconds=sub * len(members) / len(idx))
    print('MEASURE', json.dumps(result), flush=True)
    return result


def process_class(item):
    index, raw_class, both = item
    start = time.monotonic()
    records = []
    common_keys = common_gauge = None
    chart_count = 0
    raw_empty_b = 0
    for raw in raw_class:
        p = profile(raw)
        F = C.cells(p)
        band = K.finder_band(F)
        assert band, ('rootless census member', p)
        window, empty_b_count = window_charts(F)
        assert band == window, ('band/window chart sets differ', p, set(band)-set(window), set(window)-set(band))
        raw_empty_b += empty_b_count
        if both:
            assert band == K.finder_subdiagram(F), ('finders disagree', p)
        charts = []
        for chart, q in band.items():
            assert chart_ok(F, chart, q) is None, (p, chart)
            D, E, B, T, case = chart
            v = K.find_mark(E, B, T, case)[3]
            charts.append((D, E, B, T, case, v, q))
        charts.sort(key=lambda c: (score(F, c[6]), serialize_order(c)))
        best = min(score(F, c[6]) for c in charts)
        source = [c for c in charts if score(F, c[6]) == best]
        keys = frozenset(key_of(c) for c in source)
        gauge = frozenset(gauge_key(c) for c in source)
        assert len(gauge) == 1, ('multiple gauge keys', p)
        if common_keys is None:
            common_keys, common_gauge = keys, gauge
        assert common_keys == keys, ('source-minimal key sets differ within class', raw_class)
        assert common_gauge == gauge, ('gauge keys differ within class', raw_class)
        chosen = source[0]
        assert K.compose(*chosen[:6]) == F
        records.append(dict(profile=p, chart=serialize_chart(chosen), score=best,
                            all_charts=len(charts), source_minimal_charts=len(source),
                            periods=sorted({c[6] for c in charts})))
        chart_count += len(charts)
    # A corrupted key must be distinguishable whenever transposition changes the outer.
    corrupted = key_of(chosen, corrupt=True)
    corruption_splits = corrupted not in common_keys
    return dict(index=index, finder_hashes=FINDER_HASHES, members=records, source_minimal_keys=sorted(common_keys),
                chosen_source_minimal_key=min(common_keys),
                key_modulo_ordinary_gauge=next(iter(common_gauge)), charts=chart_count,
                both_finders=both, window_agreement=True, raw_window_empty_b=raw_empty_b,
                corruption_splits=corruption_splits,
                seconds=time.monotonic()-start)


def serialize_order(c):
    return (c[6], tuple(sorted(c[0])), tuple(sorted(c[1])), tuple(sorted(c[2])), c[4])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work', default='/mnt/d/mvw-rust')
    ap.add_argument('--summary', default=str(HERE / 'results'))
    ap.add_argument('--min', type=int, default=27)
    ap.add_argument('--max', type=int, default=30)
    ap.add_argument('--jobs', type=int, default=16)
    ap.add_argument('--sample', type=int, default=32)
    ap.add_argument('--band-only', action='store_true', help='use subdiagram finder only on sample; window comparison remains exhaustive')
    ap.add_argument('--window-script', default=str(HERE.parents[2] / 'skew-equiv/scripts/check_cdp2_vOIM_lib.py'))
    args = ap.parse_args()
    assert 1 <= args.jobs <= 16
    global W
    spec = importlib.util.spec_from_file_location('window_finder_external', args.window_script)
    W = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(W)
    for label, module in (('window_finder', W), ('window_helpers', W.P), ('window_engine', W.eng)):
        FINDER_HASHES[label] = hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
    # A negative control for all three complete finders.
    hook = C.cells(((2, 1), (0,)))
    assert not K.finder_band(hook) and not K.finder_subdiagram(hook) and not W.w_roots(hook)
    print('PASS control: rootless hook rejected by all three finders', flush=True)
    for area in range(args.min, args.max+1):
        K._MARKS.clear()
        K._SWH.clear()
        K._CHARTS.clear()
        outer_polynomial.cache_clear()
        W.clear_caches()
        start = time.monotonic()
        source_path = Path(args.work) / f'area-{area:02}.json'
        census = json.loads(source_path.read_bytes())
        classes = census['nonrotation']
        source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
        final = Path(args.work) / f'roots-keys-{area:02}.json'
        if final.exists():
            saved = json.loads(final.read_bytes())
            if (saved['census_sha256'] == source_hash
                    and saved.get('finder_hashes') == FINDER_HASHES
                    and saved.get('band_window_agreement_members') == census['nonrotation_members']
                    and (args.band_only or saved['both_finders'])):
                assert saved['rooted'] == census['nonrotation_members']
                assert saved['source_minimal_key_classes'] == len(classes)
                enriched = False
                for witness in saved['witnesses']:
                    if 'chosen_source_minimal_key' not in witness:
                        witness['chosen_source_minimal_key'] = min(witness['source_minimal_keys'])
                        enriched = True
                if enriched:
                    atomic_json(final, saved)
                small = {k: v for k, v in saved.items() if k != 'witnesses'}
                atomic_json(Path(args.summary) / f'roots-keys-{area:02}.json', small)
                print(f"RESUMED roots/keys N={area}: {saved['classes']} classes, {saved['members']} members", flush=True)
                continue
        measure_path = Path(args.work) / f'finder-measurement-{area:02}.json'
        cached = json.loads(measure_path.read_bytes()) if measure_path.exists() else {}
        if cached.get('census_sha256') == source_hash and cached.get('finder_hashes') == FINDER_HASHES:
            measurement = cached['measurement']
            print('MEASURE cached', json.dumps(measurement), flush=True)
        else:
            measurement = measure(classes, args.sample)
            atomic_json(measure_path, dict(census_sha256=source_hash, finder_hashes=FINDER_HASHES, measurement=measurement))
        # Do not fork the exhaustive sample's potentially large caches into every worker.
        K._MARKS.clear()
        K._SWH.clear()
        K._CHARTS.clear()
        outer_polynomial.cache_clear()
        W.clear_caches()
        gc.collect()
        checkpoint = Path(args.work) / 'roots-checkpoints' / f'area-{area:02}'
        checkpoint.mkdir(parents=True, exist_ok=True)
        done = {}
        for index in range(len(classes)):
            path = checkpoint / f'{index:06}.json'
            if path.exists():
                record = json.loads(path.read_bytes())
                assert record['census_sha256'] == source_hash
                assert [profile(p['profile']) for p in record['members']] == [profile(p) for p in classes[index]]
                if not record.get('window_agreement') or record.get('finder_hashes') != FINDER_HASHES:
                    continue
                if not args.band_only:
                    assert record['both_finders']
                done[index] = record
        tasks = [(index, cl, not args.band_only) for index, cl in enumerate(classes) if index not in done]
        last = time.monotonic()
        with mp.get_context('fork').Pool(args.jobs, maxtasksperchild=100) as pool:
            for record in pool.imap_unordered(process_class, tasks, chunksize=1):
                record['census_sha256'] = source_hash
                done[record['index']] = record
                atomic_json(checkpoint / f"{record['index']:06}.json", record)
                if time.monotonic()-last >= 30:
                    print(f'PROGRESS roots N={area} {len(done)}/{len(classes)} classes', flush=True)
                    last = time.monotonic()
        records = [done[i] for i in range(len(classes))]
        members = sum(len(cl['members']) for cl in records)
        assert members == census['nonrotation_members']
        corruption_splits = sum(cl['corruption_splits'] for cl in records)
        assert corruption_splits > 0
        periods = Counter(cl['members'][0]['chart']['period'] for cl in records)
        result = dict(area=area, census_sha256=source_hash, finder_hashes=FINDER_HASHES,
                      finder_snapshot_utc=SNAPSHOT['captured_utc'], classes=len(classes), members=members,
                      rooted=members, source_minimal_key_classes=len(classes),
                      charts=sum(cl['charts'] for cl in records), both_finders=not args.band_only,
                      members_checked_by_both=sum(len(cl['members']) for cl in records if cl['both_finders']),
                      band_window_agreement_members=members,
                      raw_window_empty_b=sum(cl['raw_window_empty_b'] for cl in records),
                      empty_mark_gauge='empty-b outer replaced by antitranspose; nonempty marks unchanged',
                      sample_measurement=measurement, corrupted_key_classes_split=corruption_splits,
                      period_histogram=dict(sorted(periods.items())),
                      seconds=time.monotonic()-start,
                      worker_seconds=sum(cl['seconds'] for cl in records),
                      peak_parent_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      peak_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                      jobs=args.jobs, witnesses=records)
        atomic_json(final, result)
        # Full charts remain in the configurable output directory. The repository
        # contains the census members and this small roots/keys summary.
        small = {k: v for k, v in result.items() if k != 'witnesses'}
        atomic_json(Path(args.summary) / f'roots-keys-{area:02}.json', small)
        print(f"PASS roots/keys N={area}: {len(classes)} classes, {members} rooted members, "
              f"{result['charts']} charts, band/window agree on all, subdiagram_all={result['both_finders']}, "
              f"raw_empty_b={result['raw_window_empty_b']}, {result['seconds']:.3f}s", flush=True)


if __name__ == '__main__':
    main()
