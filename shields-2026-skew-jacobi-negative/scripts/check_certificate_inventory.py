#!/usr/bin/env python3
"""Check retained exact execution records and every staircase space verdict.

This is an evidence check, not a replacement for running the full matcher.
"""
from collections import Counter
from fractions import Fraction
import gzip
import json
from pathlib import Path
import staircase_matching as M
from staircase_exact import leaf_kind
from jacobi_trudi import require,rejects

HERE=Path(__file__).resolve().parent


def read(name):
    with gzip.open(HERE/'certificates'/name,'rt') as fh:
        return json.load(fh)


def record_check(records,expected):
    ids=[(r['stratum'],r['permutation']) for r in records]
    wanted={(r['stratum'],r['permutation']):r for r in expected}
    assert len(ids)==len(set(ids))==len(wanted)==308
    assert set(ids)==set(wanted)
    for row in records:
        goal=wanted[row['stratum'],row['permutation']]
        assert {k:row[k] for k in goal}==goal
        assert row['nodes']>0 and row['spaces']>=0
        assert sum(row['verdicts'].values())==row['spaces']
        assert set(row['verdicts'])<={'identity','reversal','family'}


def main():
    expected=json.loads((HERE/'certificates/staircase_counts.json').read_text())
    first=read('staircase_spaces.json.gz'); second=read('staircase_second.json.gz')
    assert first['backend']=='fm' and second['backend']=='z3'
    strata={s[0]:s for s in M.strata()}
    rows=tuple(M.var(i) for i in range(5)); gaps=tuple(M.var(i+5) for i in range(4))
    for result in (first,second):
        record_check(result['records'],expected['records'])
        spaces=result['spaces']
        assert len(spaces)==308
        ids=[(s['stratum'],s['permutation']) for s in spaces]
        assert len(set(ids))==308
        verdicts=Counter()
        for space in spaces:
            name,i=space['stratum'],space['permutation']
            rp,gp=strata[name][3][i]
            mate=tuple(rows[j] for j in rp),tuple(gaps[j] for j in gp)
            actual=Counter()
            bases=[]
            for eqs in space['equations']:
                basis=tuple(tuple(Fraction(x) for x in row) for row in eqs)
                assert basis==M.rref(basis)
                kind=leaf_kind(basis,(rows,gaps),mate)
                assert kind is not None
                actual[kind]+=1; bases.append(basis)
            assert len(bases)==len(set(bases))
            rec=next(r for r in result['records'] if (r['stratum'],r['permutation'])==(name,i))
            assert len(bases)==rec['spaces'] and actual==rec['verdicts']
            verdicts.update(actual)
        assert verdicts=={'identity':5038,'reversal':1119,'family':26}
    # Identical output spaces is stronger than identical aggregate counts.
    assert first['spaces']==second['spaces']
    query=Counter()
    for row in second['records']: query.update(row['exact_queries'])
    assert query==dict(sat=116921,unsat=159444)
    assert expected['exact_calls']=={'fourier_motzkin':174492}
    rejects(lambda: record_check(first['records'][:-1],expected['records']))
    rejects(lambda: record_check(first['records']+[first['records'][0]],expected['records']))
    altered=[dict(r) for r in first['records']]
    altered[0]=dict(altered[0],nodes=0)
    rejects(lambda: record_check(altered,expected['records']))
    totals=[]
    inventories=[]
    for filename,size in (('five_cross.json.gz',12),('five_within.json.gz',42)):
        data=read(filename)
        assert len(data)==size
        counts=Counter(node['type'] for cert in data for node in cert['nodes'])
        totals.append((size,sum(counts.values())))
        inventories.append(counts)
    assert totals==[(12,22217),(42,49230)]
    readme=(HERE/'README.md').read_text()
    cross,within=inventories
    phrases=[
        f"12 collision graphs, {sum(cross.values()):,} nodes = {cross['split']:,} split nodes + {cross['infeasible']:,} rational Farkas leaves + {cross['family']:,} family-implying leaves",
        f"42 collision graphs, {sum(within.values()):,} nodes = {within['split']:,} split nodes + {within['infeasible']:,} rational Farkas leaves + {within['identity']:,} identity leaves + {within['rotation']:,} rotation leaves",
        f"308 tasks, {sum(r['nodes'] for r in first['records']):,} nodes, and {sum(verdicts.values()):,} recorded spaces = {verdicts['identity']:,} identity + {verdicts['reversal']:,} reversal + {verdicts['family']:,} family",
        f"{expected['exact_calls']['fourier_motzkin']:,} Fourier–Motzkin calls; the second backend has {query['sat']:,} satisfiable and {query['unsat']:,} unsatisfiable queries",
    ]
    for phrase in phrases:
        assert phrase in readme,phrase
    assert sum(r['spaces']==0 for r in first['records'])==27
    assert 'Twenty-seven complete tasks have no equality spaces' in readme
    print('INVENTORY: both 308-task executions; every space checked; identical spaces; separate five-negative totals',totals)
    print('CONTROLS FIRED: missing task, duplicate task, zero-node incomplete record')
    print('ALL PASS')


if __name__=='__main__':
    main()
