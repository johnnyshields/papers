#!/usr/bin/env python3
"""Report the slowest completed shards without modifying checkpoints."""
import argparse
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work', default='/mnt/d/mvw-rust')
    ap.add_argument('--area', type=int, required=True)
    args = ap.parse_args()
    paths = (Path(args.work) / 'checkpoints' / f'area-{args.area:02}').glob('*.json')
    shards = [json.loads(p.read_bytes()) for p in paths]
    for s in sorted(shards, key=lambda s: -s['seconds'])[:20]:
        print(s['parts'], 'seconds', round(s['seconds'], 3), 'profiles', s['profiles'],
              'exact', s['exact_profiles'], 'spilled', s['spilled_records'])
    print('shards', len(shards), 'sum seconds', sum(s['seconds'] for s in shards))


if __name__ == '__main__':
    main()
