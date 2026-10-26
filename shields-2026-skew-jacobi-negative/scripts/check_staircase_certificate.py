#!/usr/bin/env python3
"""Execute the complete 308-task staircase classification, with exact pruning.

The default backend is rational Fourier--Motzkin.  The optional --backend z3
uses exact linear-real arithmetic and checks each rational model.  Both use the
same occurrence matcher; neither is an independent implementation of it.
"""
import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import time
import staircase_matching as M
from staircase_exact import ExactDomain, leaf_kind
from jacobi_trudi import require, rejects

HERE = Path(__file__).resolve().parent


def controls():
    x = M.var(0)
    assert M.feasible_exact((), (x,))
    assert not M.feasible_exact((x,), (x,))
    rejects(lambda: require(M.feasible_exact((), (x, tuple(-v for v in x)))))
    rows = tuple(M.var(i) for i in range(5))
    gaps = tuple(M.var(i+5) for i in range(4))
    assert leaf_kind((), (rows,gaps), (rows,gaps)) == 'identity'
    rejects(lambda: require(leaf_kind((), (rows,gaps),
            ((rows[0],rows[2],rows[1],rows[3],rows[4]),gaps)) is not None))
    rejects(lambda: M.matchings([], [], (), [], set(), time.time()-1))
    print('CONTROLS FIRED: infeasibility, unclassified space, timeout')


def run_task(stratum, index, backend, seconds):
    name, extra_ineq, equations, permutations = stratum
    rp, gp = permutations[index]
    rows = tuple(M.var(i) for i in range(5))
    gaps = tuple(M.var(i+5) for i in range(4))
    mate = tuple(rows[i] for i in rp), tuple(gaps[i] for i in gp)
    inequalities = tuple(M.domain(rows,gaps)+M.domain(*mate)+extra_ineq)
    M._bij_cache.clear()
    M._exact_cache.clear()
    M.NODES[0] = 0
    M.DEPTH.clear()
    if backend == 'z3':
        solver = ExactDomain(inequalities)
        M.feasible = solver.feasible
    else:
        M.feasible = M.feasible_exact
    assert M.feasible(equations, inequalities)
    plus, minus = [], []
    for side, profile in (('F',(rows,gaps)),('H',mate)):
        for edges, sign, entries in M.sym_monomials(*profile):
            if edges in ((),(0,1,2,3)):
                continue
            sign *= 1 if side == 'F' else -1
            (plus if sign > 0 else minus).append((edges,side,entries))
    assert len(plus) == len(minus) == 14
    plus.sort(key=lambda item: -len(item[0]))
    families = M.family_forms_sym(rows,gaps)
    M.EARLY.update(classifier=lambda R: M.classify(R,rows,gaps,*mate,families), seen=set(),cut=0)
    spaces=set()
    M.matchings(plus,minus,inequalities,list(equations),spaces,time.time()+seconds)
    verdicts=Counter()
    for R in spaces:
        verdict = leaf_kind(R,(rows,gaps),mate)
        assert verdict is not None, (name,index,'unclassified space')
        verdicts[verdict] += 1
    result=dict(stratum=name,permutation=index,nodes=M.NODES[0],spaces=len(spaces),verdicts=dict(verdicts))
    if backend == 'z3':
        result['exact_queries']=dict(solver.answers)
    print('TASK',name,index,'nodes',M.NODES[0],'spaces',len(spaces),dict(verdicts),'DONE',flush=True)
    return result, sorted(spaces)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend',choices=('fm','z3'),default='fm')
    parser.add_argument('--case',nargs=2)
    parser.add_argument('--seconds',type=int,default=3600)
    parser.add_argument('--output',type=Path,help='optional complete equation-space certificate')
    args=parser.parse_args()
    controls()
    M.FM_CALLS[0]=0
    expected=json.loads((HERE/'certificates/staircase_counts.json').read_text())
    strata=M.strata()
    assert [len(s[3]) for s in strata]==[11,11,143,143]
    tasks=[(s,i) for s in strata for i in range(len(s[3]))]
    assert len(tasks)==308
    if args.case:
        tasks=[(s,i) for s,i in tasks if (s[0],i)==(args.case[0],int(args.case[1]))]
        assert len(tasks)==1
    rows=[]
    spaces=[]
    for s,i in tasks:
        result, leaves=run_task(s,i,args.backend,args.seconds)
        wanted=next(r for r in expected['records'] if (r['stratum'],r['permutation'])==(s[0],i))
        assert {k:result[k] for k in wanted}==wanted
        rows.append(result)
        spaces.append(dict(stratum=s[0],permutation=i,equations=[[[str(c) for c in row] for row in R] for R in leaves]))
    counts=Counter()
    queries=Counter()
    for r in rows:
        counts.update(r['verdicts']); queries.update(r.get('exact_queries',{}))
    if not args.case:
        assert counts==dict(identity=5038,reversal=1119,family=26)
        assert sum(r['nodes'] for r in rows)==183367
        assert sum(r['spaces'] for r in rows)==6183
        assert sum(r['spaces']==0 for r in rows)==27
        if args.backend=='fm':
            assert M.FM_CALLS[0]==174492
        else:
            assert queries==dict(sat=116921,unsat=159444)
        if args.output:
            with gzip.open(args.output,'wt') as fh:
                json.dump(dict(backend=args.backend,records=rows,spaces=spaces),fh,separators=(',',':'))
    print('TOTAL',len(rows),'tasks',sum(r['nodes'] for r in rows),'nodes',dict(counts),
          'FM calls',M.FM_CALLS[0],'exact queries',dict(queries))
    print('ALL PASS')


if __name__=='__main__':
    main()
