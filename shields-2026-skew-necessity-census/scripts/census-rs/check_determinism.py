#!/usr/bin/env python3
"""Compare mathematical census outputs while excluding timing/resource metadata."""
import argparse
import json
from pathlib import Path
from cross_check import atomic_json


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('reference', type=Path)
    ap.add_argument('rerun', type=Path)
    ap.add_argument('--through', type=int, default=20)
    ap.add_argument('--summary', type=Path, default=Path(__file__).resolve().parent / 'results')
    args = ap.parse_args()
    fields = ('area', 'profiles', 'rotation_orbits', 'fixed', 'classes', 'histogram',
              'nonrotation', 'exact_groups', 'exact_profiles', 'exact_false_merges_split',
              'first_collision_groups', 'second_evaluations', 'first_false_merges_split')
    reference_threads, rerun_threads = set(), set()
    reference_spilled = rerun_spilled = 0
    for area in range(1, args.through+1):
        name = f'area-{area:02}.json'
        a = json.loads((args.reference / name).read_bytes())
        b = json.loads((args.rerun / name).read_bytes())
        for field in fields:
            assert a[field] == b[field], (area, field)
        reference_threads.add(a['threads'])
        rerun_threads.add(b['threads'])
        reference_spilled += a['spilled_records']
        rerun_spilled += b['spilled_records']
    certificate = dict(passed=True, through=args.through, fields=list(fields),
                       reference_threads=sorted(reference_threads), rerun_threads=sorted(rerun_threads),
                       reference_spilled_records=reference_spilled, rerun_spilled_records=rerun_spilled)
    atomic_json(args.reference / 'validation-determinism.json', certificate)
    atomic_json(args.summary / 'validation-determinism.json', certificate)
    print(f'PASS deterministic mathematical outputs and exact-confirmation counts, 1..{args.through}; spills={rerun_spilled}')


if __name__ == '__main__':
    main()
