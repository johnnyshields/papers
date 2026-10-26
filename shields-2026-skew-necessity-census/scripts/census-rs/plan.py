#!/usr/bin/env python3
"""Size future areas from completed measurements; estimates are not census results."""
import argparse
import json
from pathlib import Path
from cross_check import atomic_json


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work', default='/mnt/d/mvw-rust')
    ap.add_argument('--summary', default=str(Path(__file__).resolve().parent / 'results'))
    ap.add_argument('--base', type=int, required=True)
    ap.add_argument('--through', type=int, default=35)
    ap.add_argument('--threads', type=int, default=16, help='worker count for projections')
    args = ap.parse_args()
    work = Path(args.work)
    base = json.loads((work / f'area-{args.base:02}.json').read_bytes())
    scale = json.loads((work / 'scale.json').read_bytes())
    assert 1 <= args.threads <= 16
    sec_per_billion = base['seconds'] * 1e9 / base['profiles']
    projected_rate = sec_per_billion * base['threads'] / args.threads
    projected = []
    cumulative = 0.
    for row in scale:
        n = row['area']
        if args.base < n <= args.through:
            # Quadratic determinant work per profile is a conservative first sizing
            # model, not a guaranteed bound; external sort and contention can differ.
            seconds = projected_rate * row['profiles'] / 1e9 * (n / args.base) ** 2
            cumulative += seconds
            projected.append(dict(area=n, profiles=row['profiles'], seconds=seconds,
                                  cumulative_seconds=cumulative,
                                  largest_profiles=row['largest_profiles'],
                                  largest_canonical_record_bytes_upper=16 * row['largest_profiles']))
    result = dict(measured_area=args.base, measured_seconds=base['seconds'],
                  measured_seconds_per_billion_profiles=sec_per_billion,
                  measured_threads=base['threads'], projected_threads=args.threads,
                  projection_model='profiles times quadratic area ratio and inverse worker count',
                  projected=projected)
    atomic_json(work / f'projection-from-{args.base:02}.json', result)
    atomic_json(Path(args.summary) / f'projection-from-{args.base:02}.json', result)
    print(f"Measured N={args.base}: {sec_per_billion:.2f}s per billion profiles, {base['threads']} threads")
    for row in projected:
        print(f"PROJECT N={row['area']}: {row['seconds']/3600:.3f}h; cumulative {row['cumulative_seconds']/3600:.3f}h")


if __name__ == '__main__':
    main()
