#!/usr/bin/env python3
"""Regenerate the README's completed-results table from final JSON files."""
import argparse
import json
from pathlib import Path
from cross_check import atomic_json
from run_logged import publish

HERE = Path(__file__).resolve().parent
BEGIN = '<!-- BEGIN MEASURED TABLE -->'
END = '<!-- END MEASURED TABLE -->'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work', default='/mnt/d/mvw-rust')
    ap.add_argument('--summary', default=str(HERE / 'results'))
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    directory = Path(args.summary)
    areas = [json.loads(p.read_bytes()) for p in sorted(directory.glob('area-??.json'))]
    assert [a['area'] for a in areas] == list(range(1, len(areas)+1))
    header = ['| N | Profiles | Rotation orbits | Classes | Nonrotation classes | Members | Seconds | Peak MiB |',
              '|---:|---:|---:|---:|---:|---:|---:|---:|']
    for a in areas:
        assert sum(int(k)*v for k, v in a['histogram'].items()) == a['profiles']
        assert sum(a['histogram'].values()) == a['classes']
        assert len(a['nonrotation']) == a['nonrotation_classes']
        assert sum(len(c) for c in a['nonrotation']) == a['nonrotation_members']
        header.append('| %d | %s | %s | %s | %s | %s | %.3f | %.1f |' % (
            a['area'], format(a['profiles'], ','), format(a['rotation_orbits'], ','),
            format(a['classes'], ','), format(a['nonrotation_classes'], ','),
            format(a['nonrotation_members'], ','), a['seconds'], a['peak_rss_kib']/1024))
    roots = [json.loads(p.read_bytes()) for p in sorted(directory.glob('roots-keys-??.json'))]
    if roots:
        header += ['', '| N | Rooted members | Classes with source-minimal key | Band/window agreement | Seconds |',
                   '|---:|---:|---:|:---:|---:|']
        for r in roots:
            assert r['rooted'] == r['members']
            assert r['source_minimal_key_classes'] == r['classes']
            assert r['band_window_agreement_members'] == r['members']
            header.append(f"| {r['area']} | {r['rooted']:,} | {r['classes']:,} | all members | {r['seconds']:.3f} |")
    block = BEGIN + '\n' + '\n'.join(header) + '\n' + END
    readme_path = HERE / 'README.md'
    text = readme_path.read_text()
    before, rest = text.split(BEGIN)
    _, after = rest.split(END)
    wanted = before + block + after
    if args.check:
        assert text == wanted, 'README measured table differs from final JSON results'
        print(f'PASS README table: {len(areas)} census rows and {len(roots)} roots/key rows')
    else:
        assert publish(readme_path, wanted.encode()), 'README atomic publication failed'
        small = [{k: v for k, v in a.items() if k != 'nonrotation'} for a in areas]
        atomic_json(directory / 'summary.json', small)
        atomic_json(Path(args.work) / 'summary.json', small)
        fields = ('profiles', 'rotation_orbits', 'classes', 'nonrotation_classes', 'nonrotation_members',
                  'exact_groups', 'exact_profiles', 'exact_false_merges_split',
                  'first_collision_groups', 'first_false_merges_split', 'second_evaluations', 'seconds')
        totals = {field: sum(a[field] for a in areas) for field in fields}
        totals['through'] = len(areas)
        totals['roots_areas'] = [r['area'] for r in roots]
        totals['rooted_members'] = sum(r['rooted'] for r in roots)
        totals['root_key_classes'] = sum(r['classes'] for r in roots)
        totals['peak_census_rss_kib'] = max(a['peak_rss_kib'] for a in areas)
        atomic_json(directory / 'totals.json', totals)
        atomic_json(Path(args.work) / 'totals.json', totals)
        print('\n'.join(header))


if __name__ == '__main__':
    main()
