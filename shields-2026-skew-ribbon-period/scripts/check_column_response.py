r"""Paper section `sec:response` (The complete scalar and its second channel).

First response of a column-kind cap template (shields-2026-skew-ribbon-period.tex, sec:response,
lem:boolean, prop:clocks; sec:poles, lem:first-response).

Formalized in `SkewRibbonPeriod/Main/FilterColumn/ColumnReduction.lean`.  Template model of
`check_boolean_limit.py`: relative labels h_k (h_0 = nu, h_k = 0 for k < 0, generic rational h_k,
k > 0).  A column-kind template has cap rows I0 + Zref, cap columns (C0 + Zref) - {sigma}, with
sigma in C0 + Zref, top row c in I0.  The cap vector l (l_c = 1) annihilates the cap columns; the
return setup has rows I0 + ZR, columns C0 + ZR, and its numerator coefficient [z^0] T_R is y_c, with
y B_R = (residual of l on the return columns).

Asserts, over random column-kind templates with positive cap heights, nonsingular cap and return
systems and every return unit outside the cap columns not a cap row:
  1. sigma not in C0 (the case left by the Boolean state): T_R(0) is O(1/nu), and nu * T_R(0) is
     the same at nu = 1e9 and nu = 1e12 to relative 1e-6 (the first response of lem:first-response);
  2. sigma in C0 (the second reference-core case): T_R(0) tends to 1, so e_R = 1, which the
     Boolean state (e_R = 0, eq:clock-infinity) excludes for an ordinary high zero.
Run: nice taskset -c 1 timeout 600 python3 check_column_response.py
"""
import random
from sympy import Matrix, Rational

random.seed(11)


def labels(c):
    return {k: Rational(random.randint(1, 9), random.randint(1, 6)) for k in range(1, c + 2)}


def make_h(nu, base):
    def h(k):
        return Rational(0) if k < 0 else (nu if k == 0 else base[k])
    return h


def upper_height(rows, cols, u):
    return len([x for x in rows if x > u]) - len([x for x in cols if x > u])


def response(c, I0, C0, Zref, ZR, sigma, base, nu):
    h = make_h(nu, base)
    cap_rows = sorted(I0 | Zref)
    cap_cols = sorted((C0 | Zref) - {sigma})
    free = [i for i in cap_rows if i != c]
    if len(free) != len(cap_cols):
        return None
    sol = []
    if cap_cols:
        M = Matrix(len(cap_cols), len(free), lambda a, b: h(free[b] - cap_cols[a]))
        if M.det() == 0:
            return None
        sol = M.LUsolve(Matrix([-h(c - j) for j in cap_cols]))
    ell = {c: Rational(1)}
    for b, i in enumerate(free):
        ell[i] = sol[b]

    def resid(j):
        return sum(ell[i] * h(i - j) for i in cap_rows)

    rows = sorted(I0 | ZR)
    cols = sorted(C0 | ZR)
    BR = Matrix(len(rows), len(cols), lambda a, b: h(rows[a] - cols[b]))
    if BR.det() == 0:
        return None
    y = BR.T.LUsolve(Matrix([resid(j) for j in cols]))
    return y[rows.index(c)]


def samples(want_core_sigma, target):
    out = []
    tries = 0
    while len(out) < target and tries < 200000:
        tries += 1
        c = random.randint(2, 4)
        K = list(range(c + 1))
        k = random.randint(1, 2)
        I0 = set(random.sample(K, k))
        if c not in I0:
            continue
        rest = [x for x in K if x not in I0]
        if len(rest) < k:
            continue
        C0 = set(random.sample(rest, k))
        vac = [x for x in rest if x not in C0]
        Zref = {x for x in vac if random.random() < 0.5}
        ZR = {x for x in vac if random.random() < 0.5}
        pool = sorted(C0 | Zref)
        if not pool:
            continue
        sigma = random.choice(pool)
        if (sigma in C0) != want_core_sigma:
            continue
        cap_rows = I0 | Zref
        cap_cols = (C0 | Zref) - {sigma}
        if any(upper_height(cap_rows, cap_cols, u) < 1 for u in range(0, c)):
            continue
        if any(not (z in cap_cols or z not in cap_rows) for z in ZR):
            continue
        base = labels(c)
        a = response(c, I0, C0, Zref, ZR, sigma, base, Rational(10) ** 9)
        b = response(c, I0, C0, Zref, ZR, sigma, base, Rational(10) ** 12)
        if a is None or b is None:
            continue
        out.append((c, I0, C0, Zref, ZR, sigma, a, b))
    return out


no_anchor = samples(False, 60)
assert len(no_anchor) >= 40, len(no_anchor)
for (c, I0, C0, Zref, ZR, sigma, a, b) in no_anchor:
    assert abs(a) < Rational(1, 1000), (c, I0, C0, Zref, ZR, sigma, a)
    na, nb = a * 10 ** 9, b * 10 ** 12
    assert abs(na - nb) <= Rational(1, 10 ** 6) * max(1, abs(nb)), (c, I0, C0, Zref, ZR, sigma, na, nb)

anchor = samples(True, 30)
assert len(anchor) >= 15, len(anchor)
for (c, I0, C0, Zref, ZR, sigma, a, b) in anchor:
    assert abs(a - 1) < Rational(1, 1000) and abs(b - 1) < Rational(1, 10 ** 6), (
        c, I0, C0, Zref, ZR, sigma, a, b)
print("column-kind templates: sigma not in C0:", len(no_anchor), "(nu*T_R(0) stable);",
      "sigma in C0:", len(anchor), "(T_R(0) -> 1)", "PASS")
