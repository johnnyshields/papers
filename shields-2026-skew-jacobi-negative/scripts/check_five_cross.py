#!/usr/bin/env python3
"""Replay cross-response exhaustion using exact arithmetic and independent input.

No Z3, certificate producer, or SMT model is imported.  The
polynomial is reconstructed from a six-term dense-border identity and two
column expansions.  Linear spaces are reduced by SymPy, and infeasible leaves
are checked by rational Farkas identities, not by another feasibility test.
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
NV = 9
ZERO = (Fraction(0),) * NV


def variable(i):
    return tuple(Fraction(i == j) for j in range(NV))


def linear(*terms):
    return tuple(sum(t[j] for t in terms) for j in range(NV))


def minus(a, b):
    return tuple(x - y for x, y in zip(a, b))


def multiple(n, a):
    return tuple(n * x for x in a)


def hproduct(*forms):
    return {tuple(sorted(forms)): 1}


def combine(*signed):
    out = Counter()
    for sign, poly in signed:
        for m, c in poly.items():
            out[m] += sign * c
    return {m: c for m, c in out.items() if c}


def times_h(form, poly):
    out = Counter()
    for m, c in poly.items():
        out[tuple(sorted(m + (form,)))] += c
    return {m: c for m, c in out.items() if c}


def phi(A, B, d, a, v):
    P = minus(linear(A, B), d)
    return combine(
        (1, hproduct(linear(P, a, v), A, B)),
        (-1, hproduct(linear(P, a, v), P, d)),
        (-1, hproduct(linear(P, v), linear(A, a), B)),
        (1, hproduct(linear(P, v), linear(P, a), d)),
        (1, hproduct(linear(B, v), linear(A, a), P)),
        (-1, hproduct(linear(B, v), linear(P, a), A)),
    )


def column(A, B, d, p, ell, a, v):
    return combine((1, times_h(linear(p, ell), phi(A, B, d, a, v))),
                   (-1, times_h(p, phi(A, B, d, linear(a, ell), v))))


def profile_betas(rows, gaps):
    Y = [ZERO] * len(rows)
    for i in range(len(rows) - 2, -1, -1):
        Y[i] = minus(linear(Y[i + 1], rows[i + 1]), gaps[i])
    return tuple(linear(y, r) for y, r in zip(Y, rows)), tuple(Y)


def branch_input(index):
    A, B, d, s, p, q, ell, a, v = [variable(i) for i in range(NV)]
    swapped = index >= 6
    order = tuple(permutations(range(3)))[index % 6]
    Ap, Bp = (B, A) if swapped else (A, B)
    P = minus(linear(A, B), d)
    rows = (linear(p, ell), linear(A, a), linear(B, v))
    selected = tuple(rows[i] for i in order)
    u, ap, r = minus(selected[0], p), minus(selected[1], Ap), minus(selected[2], Bp)
    source_rows = (linear(s, q), linear(p, ell), linear(A, a), P, linear(B, v))
    mate_rows = (linear(p, u), linear(Ap, ap), P, linear(Bp, r), linear(s, q))
    source = profile_betas(source_rows, (s, p, A, B))
    mate = profile_betas(mate_rows, (p, Ap, Bp, s))
    U = column(A, B, d, p, ell, a, v)
    Ut = column(A, B, d, p, linear(ell, q), a, v)
    V = column(Ap, Bp, d, p, u, ap, r)
    Vb = column(Ap, Bp, d, p, u, ap, linear(r, q))
    poly = combine((1, times_h(linear(s, q), U)), (-1, times_h(s, Ut)),
                   (-1, times_h(linear(s, q), V)), (1, times_h(s, Vb)))
    domain = (d, minus(A, d), minus(B, d), s, p, q, minus(ell, s), minus(a, p), minus(v, q),
              minus(u, q), minus(ap, p), minus(r, s))
    return poly, domain, source, mate


def matrix(data):
    return tuple(tuple(Fraction(x) for x in row) for row in data)


@lru_cache(maxsize=None)
def canonical_space(rows):
    if not rows:
        return ()
    M = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row] for row in rows])
    R, pivots = M.rref()
    return tuple(tuple(Fraction(R[i, j]) for j in range(NV)) for i in range(len(pivots)))


def reduce_form(form, equations):
    values = list(form)
    for row in equations:
        pivot = next(i for i, c in enumerate(row) if c)
        c = values[pivot]
        values = [x - c * y for x, y in zip(values, row)]
    return tuple(values)


def restricted_polynomial(poly, equations):
    out = Counter()
    for factors, c in poly.items():
        factors = tuple(sorted(reduce_form(f, equations) for f in factors))
        out[factors] += c
    return {m: c for m, c in out.items() if c}


def all_successor_spaces(poly, pivot, equations):
    spaces = set()
    for target, coefficient in poly.items():
        if coefficient >= 0:
            continue
        # Cancel literal common factors by list deletion, independently of the
        # producer's Counter-based construction.  Polynomial monomials form a
        # cancellative free commutative monoid.
        left, right = list(pivot), list(target)
        for item in tuple(left):
            if item in right:
                left.remove(item)
                right.remove(item)
        for perm in set(permutations(right)):
            new = tuple(minus(x, y) for x, y in zip(left, perm))
            space = canonical_space(tuple(equations) + new)
            assert len(space) > len(equations)
            spaces.add(space)
    assert spaces
    return spaces


def check_farkas(rec, domain, equations):
    lam = tuple(Fraction(x) for x in rec['lambda_'])
    mu = tuple(Fraction(x) for x in rec['mu'])
    assert len(lam) == len(domain) and len(mu) == len(equations)
    assert all(x >= 0 for x in lam) and sum(lam) == 1
    for j in range(NV):
        assert sum(c * row[j] for c, row in zip(lam, domain)) + sum(c * row[j] for c, row in zip(mu, equations)) == 0


def family_betas(family):
    # Recover family parameters from the literal two-row component, then
    # compare full beta lists instead of a preselected equation predicate.
    A, B, d, _, p, _, _, a, _ = [variable(i) for i in range(NV)]
    b, g, q = A, minus(B, d), minus(A, d)
    X = tuple(linear(b, multiple(k, g)) for k in range(4, -1, -1))
    if family == 'I':
        YF = (multiple(3, g), linear(g, q), g, q, ZERO)
        YH = (linear(multiple(2, g), q), multiple(2, g), g, q, ZERO)
    else:
        assert family == 'II'
        YF = (linear(multiple(3, g), q), linear(g, q), g, q, ZERO)
        YH = (linear(multiple(2, g), q), multiple(2, g), linear(g, q), q, ZERO)
    source = (tuple(minus(X[0], y) for y in reversed(YH)),
              tuple(minus(X[0], x) for x in reversed(X)))
    mate = (X, YF)
    clearance_difference = minus(minus(g, b), minus(a, p))
    return source, mate, clearance_difference


def check_family(rec, source, mate, equations):
    expected_source, expected_mate, clearance = family_betas(rec['family'])
    for actual, expected in ((source, expected_source), (mate, expected_mate)):
        for row_a, row_b in zip(actual, expected):
            for a, b in zip(row_a, row_b):
                assert not any(reduce_form(minus(a, b), equations))
    assert not any(reduce_form(clearance, equations))


def evaluate(form, values):
    return sum(a * b for a, b in zip(form, values))



def specialize(poly, values):
    out = Counter()
    for factors, coefficient in poly.items():
        labels = [evaluate(f, values) for f in factors]
        assert all(x.denominator == 1 and x > 0 for x in labels)
        out[tuple(sorted((int(x) for x in labels), reverse=True))] += coefficient
    return tuple(sorted((m, c) for m, c in out.items() if c))


def native_checks(all_data):
    stats = Counter()
    for index, data in enumerate(all_data):
        poly, domain, source, mate = branch_input(index)
        point = tuple(Fraction(x) for x in data['primal'])
        scale = lcm(*(x.denominator for x in point))
        point = tuple(x * scale for x in point)
        F, H = (tuple(tuple(int(evaluate(f, point)) for f in word) for word in obj)
                for obj in (source, mate))
        for obj in (F, H):
            validate(*obj)
            assert determinant(*obj) == permutation_determinant(*obj)
        native = Counter(determinant(*F)); native.subtract(determinant(*H))
        assert tuple(sorted((m,c) for m,c in native.items() if c)) == specialize(poly, point)
        stats['unequal' if any(native.values()) else 'equal'] += 1
    controls = []
    A, B, d = 3, 7, 1
    for family in (1, 2):
        p = A if family == 1 else d
        ell = B-A if family == 1 else B-d
        a = B-d if family == 1 else B-A
        values = tuple(map(Fraction,(A,B,d,d,p,A-d,ell,a,B-d)))
        hits=[]
        for index in range(12):
            poly,domain,source,mate=branch_input(index)
            if all(evaluate(f,values)>=1 for f in domain) and specialize(poly,values)==():
                hits.append(index)
        assert hits
        controls.append((values,hits))
        F,H=five_family(family,A,B-d,A-d)
        assert determinant(*F)==determinant(*H)
        assert F!=H and rotation(*F)!=H
    assert stats['unequal'] > 0
    return stats, controls


def main():
    assert 'z3' not in sys.modules
    all_data = []
    totals = Counter()
    missing_child_control = None
    bad_multiplier_control = None
    with gzip.open(HERE / 'certificates/five_cross.json.gz', 'rt') as fh:
        certificates = json.load(fh)
    assert len(certificates) == 12
    for index, data in enumerate(certificates):
        assert data['branch'] == index
        assert tuple(data['order']) == tuple(permutations(range(3)))[index % 6]
        assert data['swap'] == (index >= 6)
        poly, domain, source, mate = branch_input(index)
        assert domain == matrix(data['domain'])
        recorded_poly = {matrix(t['factors']): t['coefficient'] for t in data['root_polynomial']}
        assert poly == recorded_poly
        primal = tuple(Fraction(x) for x in data['primal'])
        assert len(primal) == NV and all(evaluate(f, primal) >= 1 for f in domain)
        nodes = data['nodes']
        bases = [matrix(rec['equations']) for rec in nodes]
        assert bases[0] == () and len(set(bases)) == len(bases)
        reached = set()
        pending = [0]
        local = Counter()
        while pending:
            ident = pending.pop()
            if ident in reached:
                continue
            reached.add(ident)
            rec, equations = nodes[ident], bases[ident]
            assert equations == canonical_space(equations)
            if rec['type'] == 'infeasible':
                check_farkas(rec, domain, equations)
                local['farkas_leaves'] += 1
                bad_multiplier_control = bad_multiplier_control or (rec, domain, equations)
            elif rec['type'] == 'family':
                check_family(rec, source, mate, equations)
                local['family_' + rec['family']] += 1
            else:
                assert rec['type'] == 'split'
                remaining = restricted_polynomial(poly, equations)
                pivot = matrix(rec['pivot'])
                assert remaining.get(pivot, 0) > 0
                required = all_successor_spaces(remaining, pivot, equations)
                given = {bases[j] for j in rec['children']}
                assert len(given) == len(rec['children']) and required == given
                for child in rec['children']:
                    assert len(bases[child]) > len(equations)
                pending.extend(rec['children'])
                local['split_nodes'] += 1
                missing_child_control = missing_child_control or (required, tuple(rec['children']), bases)
        assert len(reached) == len(nodes)
        local['nodes'] = len(nodes)
        totals.update(local)
        all_data.append(data)
        print('REPLAY', index, dict(local), flush=True)
    stats, controls = native_checks(all_data)
    # Mutations must fail the arithmetic, coverage, and family checks.
    rec, domain, equations = bad_multiplier_control
    wrong = dict(rec, lambda_=['0'] * len(domain))
    try:
        check_farkas(wrong, domain, equations)
    except AssertionError:
        totals['rejected_zero_multiplier'] += 1
    required, children, bases = missing_child_control
    assert required != {bases[j] for j in children[1:]}
    totals['rejected_missing_child'] += 1
    wrong_family_fired = False
    for values, hits in controls:
        for index in hits:
            _, _, source, mate = branch_input(index)
            for rec in all_data[index]['nodes']:
                eqs = matrix(rec['equations'])
                if rec['type'] != 'family' or any(evaluate(row, values) for row in eqs):
                    continue
                wrong = dict(rec, family='II' if rec['family'] == 'I' else 'I')
                try:
                    check_family(wrong, source, mate, eqs)
                except AssertionError:
                    wrong_family_fired = True
                    break
            if wrong_family_fired:
                break
        if wrong_family_fired:
            break
    assert wrong_family_fired
    totals['rejected_wrong_family'] += 1
    assert totals['rejected_zero_multiplier'] == totals['rejected_missing_child'] == totals['rejected_wrong_family'] == 1
    assert totals['farkas_leaves'] > 0 and totals['family_I'] > 0 and totals['family_II'] > 0
    assert 'z3' not in sys.modules
    assert {k: totals[k] for k in ('nodes','split_nodes','farkas_leaves','family_I','family_II')} == dict(nodes=22217, split_nodes=439, farkas_leaves=21751, family_I=16, family_II=11)
    print('EXACT_CERTIFICATE_TOTALS', dict(totals))
    print('INDEPENDENT_NATIVE_CONTROLS', dict(stats), 'family branches', [h for p, h in controls])
    print('ALL PASS')


if __name__ == '__main__':
    main()
