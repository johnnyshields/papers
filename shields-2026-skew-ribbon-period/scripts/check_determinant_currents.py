r"""Paper section `sec:whole-sign` (Whole-determinant noncancellation).

Also checks `app:cell-cut` (Integral cuts with a cell-only proper interior).
Exact SymPy checks derive determinants from beta lists, then compare full
row/column differentiation, physical-cut jumps, and retained-slot unit
contractions.  These bounded checks do not prove the general recognition
or period theorem.
"""
from itertools import combinations
import sympy as sp


def sign(exponent):
    return sp.Integer(1 if exponent % 2 == 0 else -1)


def alphabet(prefix, largest):
    return {0: sp.Integer(1), **{j: sp.Symbol(f"{prefix}{j}") for j in range(1, largest + 1)}}


def entry(index, symbols):
    return symbols.get(index, sp.Integer(0))


def matrix(rows, columns, symbols):
    return sp.Matrix([[entry(x-y, symbols) for y in columns] for x in rows])


def determinant(rows, columns, symbols):
    return sp.expand(matrix(rows, columns, symbols).det())


def equal(left, right):
    assert sp.expand(left-right) == 0


def derivative(poly, q, symbols, weighted=False):
    return sp.expand(sum(sp.diff(poly, symbol) * entry(j-q, symbols) *
                         (j-q if weighted else 1)
                         for j, symbol in symbols.items() if j >= q and j > 0))


def replacements(rows, columns, q, symbols):
    row_terms = {x: determinant([v-q if i == k else v for i, v in enumerate(rows)],
                               columns, symbols) for k, x in enumerate(rows)}
    column_terms = {y: determinant(rows, [v+q if j == k else v for j, v in enumerate(columns)],
                                  symbols) for k, y in enumerate(columns)}
    return row_terms, column_terms


def check_currents_and_cuts():
    cases = [([], []), ([4, 3, 2, 1], [3, 2, 1, 0]), ([3, 2], [1, 0]),
             ([6, 4, 2], [3, 1, 0]), ([4, 1], [2, 0]),
             ([3, 2, 1], [3, 2, 1])]
    for rows, columns in cases:
        largest = max(rows, default=0)
        symbols = alphabet("h", largest)
        raw = determinant(rows, columns, symbols)
        canonical_phase = sign(len(rows)-1)
        original = matrix(rows, columns, symbols)
        for q in range(1, largest+2):
            row_terms, column_terms = replacements(rows, columns, q, symbols)
            hall = derivative(raw, q, symbols)
            weighted = derivative(raw, q, symbols, weighted=True)
            equal(hall, sum(row_terms.values()))
            equal(hall, sum(column_terms.values()))
            equal(weighted, sum((x-q)*value for x, value in row_terms.items()) -
                  sum(y*value for y, value in column_terms.items()))
            r_star, tau = q+2, 1
            equal(weighted-(r_star-tau)*hall,
                  sum((x-q-r_star)*value for x, value in row_terms.items()) +
                  sum((tau-y)*value for y, value in column_terms.items()))
            # The actual indicator definition retains the full original cofactors.
            cuts = {t: sp.expand(canonical_phase * sum(
                original.cofactor(i, j) * entry(x-y-q, symbols)
                for i, x in enumerate(rows) for j, y in enumerate(columns)
                if y < t <= x-q)) for t in range(largest+2)}
            equal(sum(cuts.values()), canonical_phase*weighted)
            for e in range(largest+1):
                equal(cuts[e+1]-cuts[e], canonical_phase *
                      (column_terms.get(e, 0)-row_terms.get(q+e, 0)))
    # An actual disconnected determinant lies outside the connected-source domain.
    symbols = alphabet("h", 4)
    disconnected = determinant([4, 1], [2, 0], symbols)
    equal(disconnected, symbols[2]*symbols[1])
    equal(derivative(disconnected, 2, symbols), symbols[1])
    equal(derivative(disconnected, 2, symbols, weighted=True), 0)
    print("PASS: full Hall/weighted identities and physical-cut jumps on fixed beta-list cases")


def check_retained_slots():
    rows, columns = [4, 3, 2, 1], [3, 2, 1, 0]
    h, H = alphabet("h", 4), alphabet("H", 4)
    canonical = -determinant(rows, columns, h)
    remainder = h[2]-h[1]**2
    equal(derivative(canonical, 2, h, weighted=True), 2*remainder)
    equal(derivative(canonical, 2, h), -remainder)
    equal(determinant(rows[1:], columns[:-1], h), 1)
    equal(sp.diff(remainder, h[2]), 1)
    assert sp.Poly(remainder, h[1]).TC() != 0
    z = sp.Symbol("z")
    unit_positions = [(i,j) for i,x in enumerate(rows)
                      for j,y in enumerate(columns) if x == y]
    substituted = sp.expand(canonical.subs(
        {h[j]: z*H[j-1] for j in range(1,5)}, simultaneous=True))
    for degree in range(1, len(rows)+1):
        slot_sum = 0
        for selected in combinations(unit_positions, len(rows)-degree):
            remaining_rows = [x-1 for i,x in enumerate(rows) if all(i != a for a,b in selected)]
            remaining_columns = [y for j,y in enumerate(columns) if all(j != b for a,b in selected)]
            parity = sign(sum(i-j+1 for i,j in selected))
            slot_sum += parity*sign(degree-1)*determinant(remaining_rows, remaining_columns, H)
        equal(slot_sum, substituted.coeff(z, degree))
    # This wrong convention changes a genuine gated example, not just notation.
    occupied_sum = 0
    for selected in combinations(unit_positions, 2):
        rr = [x-1 for i,x in enumerate(rows) if all(i != a for a,b in selected)]
        cc = [y for j,y in enumerate(columns) if all(j != b for a,b in selected)]
        occupied = sum(x > y for x,y in zip(rr, cc))
        occupied_sum += sign(sum(i-j+1 for i,j in selected))*sign(occupied-1)*determinant(rr, cc, H)
    correct = substituted.coeff(z, 2)
    assert sp.expand(occupied_sum-correct) != 0
    equal(correct, -H[1]**2-2*H[2])
    print("PASS: every original unit layer retains matrix-slot phase; occupied-row mutation rejected")


if __name__ == "__main__":
    check_currents_and_cuts()
    check_retained_slots()
    print("ALL PASS")
