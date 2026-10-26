#!/usr/bin/env python3
"""Solver-free replay of within-class rigidity certificates.

The independent input uses row/overlap profiles and dense three-row border
expansions, not the producer's five-row permutation determinants.  SymPy
checks linear spaces; Fraction identities check every Farkas contradiction.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
import json
from math import lcm
from pathlib import Path
import gzip
from jacobi_trudi import determinant, permutation_determinant, validate, five_family, rotation, from_profile
import sys

import sympy as sp

HERE = Path(__file__).resolve().parent


def lin(*forms):
    return tuple(sum(xs) for xs in zip(*forms))


def difference(a, b):
    return tuple(x - y for x, y in zip(a, b))


def variable(i, n):
    return tuple(Fraction(i == j) for j in range(n))


def mono(*forms):
    return {tuple(sorted(forms)): 1}


def combine(*terms):
    out = Counter()
    for sign, poly in terms:
        for m, c in poly.items():
            out[m] += sign * c
    return {m: c for m, c in out.items() if c}


def htimes(form, poly):
    out = Counter()
    for m, c in poly.items():
        out[tuple(sorted((form,) + m))] += c
    return dict(out)


def phi(A, B, d, L, R):
    P = difference(lin(A, B), d)
    return combine((1, mono(lin(P, L, R), A, B)), (-1, mono(lin(P, L, R), P, d)),
                   (-1, mono(lin(P, R), lin(A, L), B)), (1, mono(lin(P, R), lin(P, L), d)),
                   (1, mono(lin(B, R), lin(A, L), P)), (-1, mono(lin(B, R), lin(P, L), A)))


def column(A, B, d, p, ell, a, v):
    return combine((1, htimes(lin(p, ell), phi(A, B, d, a, v))),
                   (-1, htimes(p, phi(A, B, d, lin(a, ell), v))))


def t1_poly(A, B, d, s, p, u, ell, a, v):
    return combine((1, htimes(lin(s, u), column(A, B, d, p, ell, a, v))),
                   (-1, htimes(s, column(A, B, d, p, lin(ell, u), a, v))))


def t2_poly(A, B, d, s, r, u, L, R, v):
    return combine((1, htimes(lin(s, u), htimes(lin(r, v), phi(A, B, d, L, R)))),
                   (-1, htimes(s, htimes(lin(r, v), phi(A, B, d, lin(L, u), R)))),
                   (-1, htimes(lin(s, u), htimes(r, phi(A, B, d, L, lin(R, v))))),
                   (1, htimes(s, htimes(r, phi(A, B, d, lin(L, u), lin(R, v))))))


def profile(rows, gaps):
    n = len(rows[0])
    Y = [(Fraction(0),) * n for _ in rows]
    for i in range(len(rows) - 2, -1, -1):
        Y[i] = difference(lin(Y[i + 1], rows[i + 1]), gaps[i])
    return tuple(lin(x, y) for x, y in zip(rows, Y)), tuple(Y)


def input_case(index):
    if index < 12:
        group, local, swaps, k = 't1_up', index, True, 3
    elif index < 24:
        group, local, swaps, k = 't1_down', index - 12, True, 3
    elif index < 26:
        group, local, swaps, k = 't1_tie', index - 24, False, 2
    elif index < 38:
        group, local, swaps, k = 't2_up', index - 26, True, 3
    else:
        assert index < 42
        group, local, swaps, k = 't2_tie', index - 38, True, 2
    permutations_ = tuple(permutations(range(k)))
    swap = local // len(permutations_) if swaps else 0
    order = permutations_[local % len(permutations_)]
    tied = group.endswith('tie')
    n = 8 if tied else 9
    xs = [variable(i, n) for i in range(n)]
    A, B, d = xs[:3]
    P = difference(lin(A, B), d)
    if group.startswith('t1'):
        names = ('A', 'B', 'd', 's', 'p', 'u', 'ell', 'a') + (() if tied else ('v',))
        s, p, u, ell, a = xs[3:8]
        v = u if tied else xs[8]
        source = profile((lin(s, u), lin(p, ell), lin(A, a), P, lin(B, v)), (s, p, A, B))
        first = t1_poly(A, B, d, s, p, u, ell, a, v)
        dom = [d, difference(A, d), difference(B, d), s, p, difference(ell, s), difference(a, p)]
        if group == 't1_up':
            dom += [u, difference(v, u)]
            Ap, Bp = (B, A) if swap else (A, B)
            rows = (lin(p, ell), lin(A, a), lin(B, v))
            picked = tuple(rows[i] for i in order)
            lp, ap, vp = difference(picked[0], p), difference(picked[1], Ap), difference(picked[2], Bp)
            target = profile((lin(s, u), lin(p, lp), lin(Ap, ap), P, lin(Bp, vp)), (s, p, Ap, Bp))
            second = t1_poly(Ap, Bp, d, s, p, u, lp, ap, vp)
            dom += [difference(lp, s), difference(ap, p), difference(vp, u)]
        elif group == 't1_down':
            dom += [v, difference(u, v)]
            sp_, pp = (p, s) if swap else (s, p)
            rows = (lin(s, u), lin(p, ell), lin(A, a))
            picked = tuple(rows[i] for i in order)
            up, lp, ap = difference(picked[0], sp_), difference(picked[1], pp), difference(picked[2], A)
            target = profile((lin(sp_, up), lin(pp, lp), lin(A, ap), P, lin(B, v)), (sp_, pp, A, B))
            second = t1_poly(A, B, d, sp_, pp, up, lp, ap, v)
            dom += [difference(up, v), difference(lp, sp_), difference(ap, pp)]
        else:
            dom += [u]
            rows = (lin(p, ell), lin(A, a))
            picked = tuple(rows[i] for i in order)
            lp, ap = difference(picked[0], p), difference(picked[1], A)
            target = profile((lin(s, u), lin(p, lp), lin(A, ap), P, lin(B, u)), (s, p, A, B))
            second = t1_poly(A, B, d, s, p, u, lp, ap, u)
            dom += [difference(lp, s), difference(ap, p)]
    else:
        names = ('A', 'B', 'd', 's', 'r', 'u', 'L', 'R') + (() if tied else ('v',))
        s, r, u, L, R = xs[3:8]
        v = u if tied else xs[8]
        source = profile((lin(s, u), lin(A, L), P, lin(B, R), lin(r, v)), (s, A, B, r))
        first = t2_poly(A, B, d, s, r, u, L, R, v)
        dom = [d, difference(A, d), difference(B, d), s, r, u, difference(L, s), difference(R, r)]
        Ap, Bp = (B, A) if swap else (A, B)
        if not tied:
            dom += [difference(v, u)]
            rows = (lin(A, L), lin(B, R), lin(r, v))
            picked = tuple(rows[i] for i in order)
            Lp, Rp, vp = difference(picked[0], Ap), difference(picked[1], Bp), difference(picked[2], r)
            dom += [difference(Lp, s), difference(Rp, r), difference(vp, u)]
        else:
            rows = (lin(A, L), lin(B, R))
            picked = tuple(rows[i] for i in order)
            Lp, Rp, vp = difference(picked[0], Ap), difference(picked[1], Bp), u
            dom += [difference(Lp, s), difference(Rp, r)]
        target = profile((lin(s, u), lin(Ap, Lp), P, lin(Bp, Rp), lin(r, vp)), (s, Ap, Bp, r))
        second = t2_poly(Ap, Bp, d, s, r, u, Lp, Rp, vp)
    return dict(group=group, swap=swap, order=order, names=names, source=source, mate=target,
                polynomial=combine((1, first), (-1, second)), domain=tuple(dom))


def matrix(rows):
    return tuple(tuple(Fraction(x) for x in row) for row in rows)


@lru_cache(maxsize=None)
def space(rows):
    if not rows:
        return ()
    n = len(rows[0])
    M = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row] for row in rows])
    R, pivots = M.rref()
    return tuple(tuple(Fraction(R[i, j]) for j in range(n)) for i in range(len(pivots)))


def reduce_form(form, equations):
    values = list(form)
    for row in equations:
        pivot = next(i for i, c in enumerate(row) if c)
        c = values[pivot]
        values = [x - c * y for x, y in zip(values, row)]
    return tuple(values)


def reduce_poly(poly, equations):
    out = Counter()
    for factors, c in poly.items():
        out[tuple(sorted(reduce_form(f, equations) for f in factors))] += c
    return {m: c for m, c in out.items() if c}


def successor_spaces(poly, pivot, equations):
    spaces = set()
    for mon, c in poly.items():
        if c >= 0:
            continue
        left, right = list(pivot), list(mon)
        for item in tuple(left):
            if item in right:
                left.remove(item)
                right.remove(item)
        for order in set(permutations(right)):
            extra = tuple(difference(x, y) for x, y in zip(left, order))
            child = space(equations + extra)
            assert len(child) > len(equations)
            spaces.add(child)
    assert spaces
    return spaces


def check_farkas(node, domain, equations):
    lam, mu = tuple(map(Fraction, node['lambda_'])), tuple(map(Fraction, node['mu']))
    assert len(lam) == len(domain) and len(mu) == len(equations)
    assert min(lam) >= 0 and sum(lam) == 1
    for j in range(len(domain[0])):
        assert sum(c * f[j] for c, f in zip(lam, domain)) + sum(c * f[j] for c, f in zip(mu, equations)) == 0


def check_goal(node, data, equations):
    source = data['source']
    if node['type'] == 'rotation':
        assert data['group'] == 't2_tie'
        X, Y = source
        source = (tuple(difference(X[0], y) for y in reversed(Y)), tuple(difference(X[0], x) for x in reversed(X)))
    else:
        assert node['type'] == 'identity'
    for aa, bb in zip(source, data['mate']):
        for a, b in zip(aa, bb):
            assert not any(reduce_form(difference(a, b), equations))


def eval_form(form, point):
    return sum(a * b for a, b in zip(form, point))


def evaluate(poly, point):
    out = Counter()
    for mon, coefficient in poly.items():
        values = tuple(eval_form(f, point) for f in mon)
        assert all(v.denominator == 1 and v > 0 for v in values)
        out[tuple(sorted(map(int, values), reverse=True))] += coefficient
    return tuple(sorted((m, c) for m, c in out.items() if c))


def native_controls(certificates):
    stats = Counter()
    for index, cert in enumerate(certificates):
        data = input_case(index)
        point = tuple(map(Fraction, cert['primal']))
        scale = lcm(*(x.denominator for x in point))
        point = tuple(x*scale for x in point)
        F,H=(tuple(tuple(int(eval_form(f,point)) for f in word) for word in obj)
             for obj in (data['source'],data['mate']))
        for obj in (F,H):
            validate(*obj)
            assert determinant(*obj)==permutation_determinant(*obj)
        native=Counter(determinant(*F)); native.subtract(determinant(*H))
        assert tuple(sorted((m,c) for m,c in native.items() if c))==evaluate(data['polynomial'],point)
        stats['unequal' if any(native.values()) else 'equal']+=1
    X,Y=from_profile((3,4,4,7,3),(1,2,3,1))
    point=tuple(map(Fraction,(X[2]-Y[1],X[3]-Y[2],X[3]-Y[1],X[1]-Y[0],
          X[4]-Y[3],X[0]-X[1],X[1]-X[2],Y[2]-Y[3])))
    data=input_case(41)
    assert all(eval_form(f,point)>=1 for f in data['domain'])
    H=tuple(tuple(int(eval_form(f,point)) for f in word) for word in data['mate'])
    assert H==rotation(X,Y) and H!=(X,Y)
    assert evaluate(data['polynomial'],point)==()
    assert determinant(X,Y)==determinant(*H)
    stats['nontrivial_rotation']+=1
    assert stats['equal']>0 and stats['unequal']>0
    return stats,point


def main():
    assert 'z3' not in sys.modules
    certs, data_cases = [], []
    totals, grouped = Counter(), {}
    corruption_farkas = None
    corruption_child = None
    with gzip.open(HERE / 'certificates/five_within.json.gz', 'rt') as fh:
        certificates = json.load(fh)
    assert len(certificates) == 42
    for index, cert in enumerate(certificates):
        data = input_case(index)
        assert cert['index'] == index and cert['group'] == data['group']
        assert cert['swap'] == data['swap'] and tuple(cert['order']) == data['order']
        assert tuple(cert['names']) == data['names'] and matrix(cert['domain']) == data['domain']
        poly = {matrix(term['factors']): term['coefficient'] for term in cert['polynomial']}
        assert poly == data['polynomial']
        primal = tuple(map(Fraction, cert['primal']))
        assert len(primal) == len(data['names'])
        assert all(eval_form(f, primal) >= 1 for f in data['domain'])
        nodes = cert['nodes']
        equations = [matrix(node['equations']) for node in nodes]
        assert equations[0] == () and len(set(equations)) == len(equations)
        done, todo, stats = set(), [0], Counter()
        while todo:
            ident = todo.pop()
            if ident in done:
                continue
            done.add(ident)
            node, eqs = nodes[ident], equations[ident]
            assert eqs == space(eqs)
            if node['type'] == 'infeasible':
                check_farkas(node, data['domain'], eqs)
                corruption_farkas = corruption_farkas or (node, data['domain'], eqs)
            elif node['type'] in ('identity', 'rotation'):
                check_goal(node, data, eqs)
            else:
                assert node['type'] == 'split'
                remaining = reduce_poly(poly, eqs)
                pivot = matrix(node['pivot'])
                assert remaining.get(pivot, 0) > 0
                required = successor_spaces(remaining, pivot, eqs)
                supplied = {equations[j] for j in node['children']}
                assert len(supplied) == len(node['children']) and supplied == required
                for child in node['children']:
                    assert len(equations[child]) > len(eqs)
                todo.extend(node['children'])
                corruption_child = corruption_child or (required, tuple(node['children']), equations)
            stats[node['type']] += 1
        assert len(done) == len(nodes)
        stats['nodes'] = len(nodes)
        totals.update(stats)
        grouped.setdefault(data['group'], Counter()).update(stats)
        certs.append(cert)
        data_cases.append(data)
        print('REPLAY', index, data['group'], dict(stats), flush=True)
    controls, point = native_controls(certs)
    node, domain, eqs = corruption_farkas
    wrong = dict(node, lambda_=['0'] * len(domain))
    try:
        check_farkas(wrong, domain, eqs)
    except AssertionError:
        controls['rejected_zero_multiplier'] += 1
    required, child_ids, equations = corruption_child
    assert required != {equations[i] for i in child_ids[1:]}
    controls['rejected_missing_child'] += 1
    fired = False
    for node in certs[41]['nodes']:
        eqs = matrix(node['equations'])
        if node['type'] != 'rotation' or any(eval_form(f, point) for f in eqs):
            continue
        try:
            check_goal(dict(node, type='identity'), data_cases[41], eqs)
        except AssertionError:
            fired = True
            break
    assert fired
    controls['rejected_rotation_as_identity'] += 1
    assert controls['rejected_zero_multiplier'] == controls['rejected_missing_child'] == controls['rejected_rotation_as_identity'] == 1
    assert totals['identity'] > 0 and totals['rotation'] > 0 and totals['split'] > 0 and totals['infeasible'] > 0
    assert 'z3' not in sys.modules
    assert totals == dict(nodes=49230, split=742, infeasible=44368, identity=3853, rotation=267)
    print('EXACT_TOTALS', dict(totals))
    print('BY_REGIME', {k: dict(v) for k, v in grouped.items()})
    print('NATIVE_AND_CORRUPTION_CONTROLS', dict(controls))
    print('ALL PASS')


if __name__ == '__main__':
    main()
