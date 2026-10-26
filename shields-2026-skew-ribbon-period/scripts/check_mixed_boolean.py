r"""Paper section `sec:response` (The complete scalar and its second channel).

Whether the Boolean state of a mixed pair is fixed by the case (`lem:boolean`, `prop:clocks`:
`e_R + e_L = 1`; Lean `MixedBoolean`).  `check_mixed_response.py` forbids the lower active index
from being a return unit (`z in cap_cols or z not in cap_rows`), which assumes `e_L = 0` in case (d),
so its "only 10 occurs" is the constraint, not a finding.  The real constraint on a return unit of a
mixed template is only that a return unit in the cap rows is a cap column, and a return unit equal to
the added active row is exempt: it is the lower vacancy with `e_L = 1` (return pair `(1,1)`).  With
that exemption the template model of `check_mixed_response.py` (relative labels, weak core, vacancy
sets, positive cap heights, nonsingular systems) produces the state `01` in the case-(d) shape, and
the state `10` in the case-(c) shape, with the Hall-compatible sums `e_R + e_L = 1`.  Asserted:
  1. in the case-(d) shape both Hall-compatible states `10` and `01` occur;
  2. in the case-(c) shape both occur;
  The states `11` and `00` also occur in the model; they are excluded by the Hall zero, not by the template.
Hence `MixedBoolean` is not a consequence of the template, heights and cap-profile data alone.
Run: nice taskset -c 3 timeout 600 python3 check_mixed_boolean.py
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
    if any(not (z in cap_cols or z not in cap_rows or z == act) for z in Zret):
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



for name, ku, kv in (("case (d): column upper / row lower", 'col', 'row'),
                     ("case (c): row upper / column lower", 'row', 'col')):
    st = sample(ku, kv, 150)
    print(name, st)
    assert sum(st.values()) >= 120, st
    assert st.get((1, 0), 0) > 0 and st.get((0, 1), 0) > 0, (name, st)
print("mixed templates: both Hall states occur in each case shape PASS")
