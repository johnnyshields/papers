#!/usr/bin/env python3
"""Run successive complete census/root/key areas under a persistent wall-time budget.

Invoke under nohup, timeout, nice, and prlimit, as documented in README.md.
Every completed area is published before the next area starts. The deadline is
persistent across restarts; an area already started is finished, not discarded.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
from cross_check import atomic_json

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work', type=Path, default=Path('/mnt/d/mvw-rust'))
    ap.add_argument('--scratch', type=Path, default=Path('/home/shields/r167-lanes/_rust35'))
    ap.add_argument('--min', type=int, default=33)
    ap.add_argument('--max', type=int, default=35)
    ap.add_argument('--threads', type=int, default=16)
    ap.add_argument('--deadline', required=True, help='fixed ISO-8601 UTC deadline, retained on resume')
    ap.add_argument('--plan-only', action='store_true')
    ap.add_argument('--step-timeout', type=int, default=172800, help='hard timeout in seconds for each census or roots step')
    args = ap.parse_args()
    assert 1 <= args.threads <= 16 and 27 <= args.min <= args.max <= 35
    temporary = args.scratch / 'tmp'
    temporary.mkdir(parents=True, exist_ok=True)
    os.environ['TMPDIR'] = str(temporary)
    assert os.getpriority(os.PRIO_PROCESS, 0) >= 10
    address_limit = resource.getrlimit(resource.RLIMIT_AS)[0]
    assert 0 < address_limit <= 24_000_000_000
    deadline = datetime.fromisoformat(args.deadline).timestamp()
    scale = {r['area']: r for r in json.loads((args.work / 'scale.json').read_bytes())}
    state_path = args.work / 'campaign-state.json'
    state = json.loads(state_path.read_bytes()) if state_path.exists() else {}
    if state:
        assert state['deadline_epoch'] == deadline, 'a resume must not reset the time budget'
    state['deadline_epoch'] = deadline
    state['deadline_utc'] = datetime.fromtimestamp(deadline, timezone.utc).isoformat()
    state['threads'] = args.threads

    def execute(command, name):
        log = args.work / 'logs' / (name + '.log')
        hot = args.scratch / 'logs' / (name + '.log')
        wrapped = [sys.executable, str(HERE / 'run_logged.py'), '--log', str(log),
                   '--hot-log', str(hot), '--', '/usr/bin/time', '-v'] + command
        # All children inherit the niceness, address-space limit, and thread caps.
        subprocess.run(['timeout', f'{args.step_timeout}s'] + wrapped, check=True)

    for area in range(args.min, args.max+1):
        path = args.work / f'area-{area:02}.json'
        already_started = state.get('area') == area and state.get('phase') in ('census', 'roots')
        if not path.exists():
            base = json.loads((args.work / f'area-{area-1:02}.json').read_bytes())
            previous_roots = json.loads((args.work / f'roots-keys-{area-1:02}.json').read_bytes())
            projection = (base['seconds'] * scale[area]['profiles'] / base['profiles']
                          * (area / (area-1)) ** 2 * base['threads'] / args.threads)
            root_allowance = max(300., 3 * previous_roots['seconds'])
            remaining = deadline - time.time()
            decision = dict(area=area, census_seconds=projection, root_allowance_seconds=root_allowance,
                            remaining_seconds=remaining, previously_started=already_started, planning_only=args.plan_only,
                            start=already_started or projection+root_allowance <= remaining)
            print('BUDGET', json.dumps(decision), flush=True)
            atomic_json(args.work / f'budget-{area:02}.json', decision)
            atomic_json(HERE / 'results' / f'budget-{area:02}.json', decision)
            if args.plan_only:
                return
            if not decision['start']:
                state.update(area=area, phase='stopped_budget', completed_through=area-1)
                atomic_json(state_path, state)
                print(f'STOP cleanly: area {area} does not fit the remaining budget', flush=True)
                return
            state.update(area=area, phase='census')
            atomic_json(state_path, state)
            execute([str(args.scratch / 'target/release/skew-census'), 'census',
                     '--min', str(area), '--max', str(area), '--threads', str(args.threads),
                     '--work', str(args.work), '--scratch', str(args.scratch / 'hot'),
                     '--summary', str(HERE / 'results')], f'census-{area}-{area}')
        if args.plan_only:
            print(f'Area {area} census is already complete', flush=True)
            return
        state.update(area=area, phase='roots')
        atomic_json(state_path, state)
        execute([sys.executable, str(HERE / 'roots_keys.py'), '--min', str(area), '--max', str(area),
                 '--jobs', str(args.threads), '--work', str(args.work), '--band-only'],
                f'roots-pinned-{area}')
        subprocess.run(['timeout', '120s', sys.executable, str(HERE / 'summarize.py'),
                        '--work', str(args.work)], check=True)
        subprocess.run(['timeout', '120s', sys.executable, str(HERE / 'summarize.py'),
                        '--work', str(args.work), '--check'], check=True)
        subprocess.run(['timeout', '120s', sys.executable, str(HERE / 'plan.py'),
                        '--work', str(args.work), '--base', str(area), '--through', str(args.max),
                        '--threads', str(args.threads)], check=True)
        census = json.loads(path.read_bytes())
        roots = json.loads((args.work / f'roots-keys-{area:02}.json').read_bytes())
        assert roots['rooted'] == census['nonrotation_members']
        assert roots['band_window_agreement_members'] == census['nonrotation_members']
        state.update(area=area, phase='complete', completed_through=area)
        atomic_json(state_path, state)
        atomic_json(args.work / f'complete-{area:02}.json',
                    dict(area=area, profiles=census['profiles'], classes=census['classes'],
                         nonrotation_classes=census['nonrotation_classes'], rooted_members=roots['rooted'],
                         census_seconds=census['seconds'], roots_seconds=roots['seconds'],
                         exact_false_merges_split=census['exact_false_merges_split'],
                         peak_rss_kib=census['peak_rss_kib']))
        print(f"AREA_READY {area}: {census['profiles']} profiles, {census['classes']} classes, "
              f"{roots['rooted']} rooted members, all keys/window comparisons PASS", flush=True)
    print('CAMPAIGN COMPLETE', flush=True)


if __name__ == '__main__':
    main()
