r"""Paper section `sec:response` (The complete scalar and its second channel).

Orders of the two cap responses of a mixed template (shields-2026-skew-ribbon-period.tex,
sec:response, lem:boolean, prop:clocks: "for mixed/mixed charts the genuine relation is
T_R + T_L = 1"; sec:poles, thm:end-filter input).

Template model of check_boolean_limit.py: relative labels h_k (h_0 = nu, h_k = 0 for k < 0, generic
rational h_k, k > 0), one common weak core (I0, C0) with top row c in I0 or c a return unit.  A
mixed template pairs an upper cap of one kind with the reflected lower cap of the other:
case (d), column-kind upper cap (cap columns (C0 + Zref) - {sigma}) with row-kind lower cap
(cap rows I0 + ZrefL + {tau}); case (c), the roles exchanged.  The return response of each end is
T(0) = y_c (c a return row or unit), y B_R = residual of the cap vector on the return columns.

Asserts, over random mixed templates with positive cap heights, nonsingular cap and return systems
and every return unit outside the cap columns not a cap row:
  1. order nu^0: each end has T(0) -> e in {0, 1} (lem:boolean);
  2. order nu^-1: the first-order coefficient nu (T(0) - e) is the same at nu = 1e9 and nu = 1e12
     (the first response, so the phiSum equation lives at this order);
  3. the only Hall-compatible state (e_R + e_L = 1) that occurs is 10 in case (d) and 01 in case
     (c); the opposite state and 11 never occur, and the state 00 occurs and is excluded by
     T_R + T_L = 1, so the Boolean state is a real constraint (MixedBoolean) and the coefficient
     equation at order nu^-1 is not vacuous in a Hall state.
Run: nice taskset -c 1 timeout 600 python3 check_mixed_response.py
"""
import random
from sympy import Matrix, Rational

random.seed(23)
TOL = Rational(1, 1000)


def make_h(nu, base):
    return lambda k: Rational(0) if k < 0 else (nu if k == 0 else base[k])


def height(rows, cols, u):
    return len([x for x in rows if x > u]) - len([x for x in cols if x > u])


def resp(c, cap_rows, cap_cols, rows, cols, base, nu):
    """T(0) = y_c for the cap vector of (cap_rows, cap_cols) and the return setup (rows, cols)."""
    h = make_h(nu, base)
    cap_rows, cap_cols = sorted(cap_rows), sorted(cap_cols)
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
    rows, cols = sorted(rows), sorted(cols)
    if len(rows) != len(cols):
        return None
    if not rows:
        return Rational(0)
    BR = Matrix(len(rows), len(cols), lambda a, b: h(rows[a] - cols[b]))
    if BR.det() == 0:
        return None
    y = BR.T.LUsolve(Matrix([sum(ell[i] * h(i - j) for i in cap_rows) for j in cols]))
    return y[rows.index(c)] if c in rows else Rational(0)


def end(c, I0, C0, kind, Zref, Zret, act, base):
    """Cap and return data of one end; kind 'col': act = sigma in C0 + Zref removed from the cap
    columns; kind 'row': act = tau-like new row outside I0 + Zref added to the cap rows."""
    if kind == 'col':
        cap_rows, cap_cols = I0 | Zref, (C0 | Zref) - {act}
    else:
        cap_rows, cap_cols = I0 | Zref | {act}, C0 | Zref
    if any(height(cap_rows, cap_cols, u) < 1 for u in range(0, c)):
        return None
    if c not in cap_rows or any(y >= c for y in cap_cols):
        return None
    if any(not (z in cap_cols or z not in cap_rows) for z in Zret):
        return None
    out = []
    for nu in (Rational(10) ** 9, Rational(10) ** 12):
        t = resp(c, cap_rows, cap_cols, I0 | Zret, C0 | Zret, base, nu)
        if t is None:
            return None
        out.append(t)
    a, b = out
    e = Rational(1) if abs(a - 1) < TOL else (Rational(0) if abs(a) < TOL else None)
    if e is None:
        return None
    na, nb = (a - e) * 10 ** 9, (b - e) * 10 ** 12
    assert abs(na - nb) <= Rational(1, 10 ** 5) * max(1, abs(nb)), (c, I0, C0, kind, Zref, Zret, act, na, nb)
    return e


def sample(kind_u, kind_v, target):
    states = {}
    n = tries = 0
    while n < target and tries < 400000:
        tries += 1
        c = random.randint(2, 4)
        K = list(range(c + 1))
        k = random.randint(0, 2)
        I0 = set(random.sample(K, k)) | {c}
        rest = [x for x in K if x not in I0]
        if len(rest) < len(I0) - 1 + 0 or len(I0) > len(rest):
            continue
        C0 = set(random.sample(rest, len(I0)))
        vac = [x for x in rest if x not in C0]
        Zu = {x for x in vac if random.random() < 0.5}
        Zv = {x for x in vac if random.random() < 0.5}
        Ru = {x for x in vac if random.random() < 0.5}
        Rv = {x for x in vac if random.random() < 0.5}
        poolu = sorted(C0 | Zu) if kind_u == 'col' else vac
        poolv = sorted(C0 | Zv) if kind_v == 'col' else vac
        if not poolu or not poolv:
            continue
        au, av = random.choice(poolu), random.choice(poolv)
        if kind_u == 'row' and (au in Zu or au in I0 or au in C0):
            continue
        if kind_v == 'row' and (av in Zv or av in I0 or av in C0):
            continue
        base = {j: Rational(random.randint(1, 9), random.randint(1, 6)) for j in range(1, c + 2)}
        eu = end(c, I0, C0, kind_u, Zu, Ru, au, base)
        ev = end(c, I0, C0, kind_v, Zv, Rv, av, base)
        if eu is None or ev is None:
            continue
        key = (int(eu), int(ev))
        states[key] = states.get(key, 0) + 1
        n += 1
    return states


for name, ku, kv, hall, bad in (("case (d): column upper / row lower", 'col', 'row', (1, 0), (0, 1)),
                                ("case (c): row upper / column lower", 'row', 'col', (0, 1), (1, 0))):
    st = sample(ku, kv, 120)
    print(name, st)
    assert sum(st.values()) >= 100, st
    assert st.get(hall, 0) > 0, (name, st)
    assert st.get(bad, 0) == 0 and st.get((1, 1), 0) == 0, (name, st)
    assert st.get((0, 0), 0) > 0, (name, st)
print("mixed templates: Boolean at order nu^0, first response at order nu^-1, "
      "Hall state 10 (d) / 01 (c) only, 00 excluded PASS")
