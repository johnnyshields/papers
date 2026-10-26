r"""Paper section `sec:poles` (Endpoint poles and outward boundary defects).

First response of the present end (shields-2026-skew-ribbon-period.tex, sec:poles,
lem:first-response with e_R = 1, lem:boolean, thm:end-filter input).

Template model of check_mixed_response.py: relative labels h_k (h_0 = nu), one weak core (I0, C0)
with c in I0, a column-kind upper cap with sigma a CORE column (sigma in C0, so the cap columns are
(C0 + Zref) - {sigma}), cap units Zref, return units Zret, all vacancies outside I0 and C0.  The
end is present: T(0) -> 1.  Let M = Zref - Zret (cap units absent from the return, the "missing"
units) and A = Zret - Zref (return units outside the cap, the "added" units).  With the limiting
cap vector l_inf (core rows), the forcing G_u = h_{c-u} + sum_i l_inf_i h_{i-u}, and the limiting
core inverse, the formulas

    phiA = - sum_{u in A} G_u (Y A^-1)_{u,c}          (capCut-phiSum of the return setup)
    phiM = - sum_{u in M} G_u rho_u(c),  rho_u = projection of the row h_{u-.} on the return core

are computed from the limit data alone.  Asserts, over random present templates:
  1. nu^0: T(0) -> 1;
  2. nu^-1: nu (T(0) - 1) is stable between nu = 1e12 and 1e14;
  3. the exact first coefficient is nu (T(0) - 1) = phiM: the added units A contribute nothing
     (the cap vector is its own projection on every return row it occupies);
  4. the capCut-phiSum of the return units, phiA, is NOT the first response of a present end:
     it differs from nu (T(0) - 1) whenever A is nonempty with phiA != 0 (in particular T = 1
     exactly when M is empty, however large A is).
Run: nice taskset -c 1 timeout 600 python3 check_present_response.py
"""
import random
from sympy import Matrix, Rational

random.seed(41)


def make_h(nu, base):
    return lambda k: Rational(0) if k < 0 else (nu if k == 0 else base[k])


def cap_vector(c, cap_rows, cap_cols, h):
    free = [i for i in sorted(cap_rows) if i != c]
    cols = sorted(cap_cols)
    if len(free) != len(cols):
        return None
    ell = {c: Rational(1)}
    if cols:
        M = Matrix(len(cols), len(free), lambda a, b: h(free[b] - cols[a]))
        if M.det() == 0:
            return None
        sol = M.LUsolve(Matrix([-h(c - j) for j in cols]))
        for b, i in enumerate(free):
            ell[i] = sol[b]
    return ell


def return_projection(rows, cols, rhs, h):
    rows, cols = sorted(rows), sorted(cols)
    BR = Matrix(len(rows), len(cols), lambda a, b: h(rows[a] - cols[b]))
    if BR.det() == 0:
        return None
    y = BR.T.LUsolve(Matrix([rhs(j) for j in cols]))
    return {rows[a]: y[a] for a in range(len(rows))}


def truth(c, I0, C0, sigma, Zref, Zret, base, nu):
    h = make_h(nu, base)
    cap_rows, cap_cols = I0 | Zref, (C0 | Zref) - {sigma}
    ell = cap_vector(c, cap_rows, cap_cols, h)
    if ell is None:
        return None
    y = return_projection(I0 | Zret, C0 | Zret,
                          lambda j: sum(ell[i] * h(i - j) for i in cap_rows), h)
    return None if y is None else (y[c], ell)


def limit_pieces(c, I0, C0, sigma, Zref, Zret, base):
    """Limit data from the exact solutions at a very large nu."""
    nu = Rational(10) ** 14
    h = make_h(nu, base)
    cap_rows, cap_cols = I0 | Zref, (C0 | Zref) - {sigma}
    ell = cap_vector(c, cap_rows, cap_cols, h)
    core_rows = sorted(I0 - {c}) if False else sorted(I0)
    ell_inf = {i: ell[i] for i in I0}
    ell_inf[c] = Rational(1)

    def G(u):
        return base_h(c - u, base) + sum(ell_inf[i] * base_h(i - u, base) for i in I0 if i != c)

    # core inverse on (I0, C0) matched in sorted order
    Ir, Cc = sorted(I0), sorted(C0)
    A = Matrix(len(Ir), len(Ir), lambda a, b: base_h(Ir[a] - Cc[b], base))
    Ainv = A.inv()

    def rho(u):
        v = Matrix([[base_h(u - j, base) for j in Cc]])
        w = v * Ainv
        return w[0, Ir.index(c)]

    def YAinv(z):
        Yz = Matrix([[base_h(z - j, base) for j in Cc]])
        w = Yz * Ainv
        return w[0, Ir.index(c)]

    added = Zret - Zref
    missing = Zref - Zret
    phiA = -sum(G(u) * YAinv(u) for u in added) if added else Rational(0)
    phiM = -sum(G(u) * rho(u) for u in missing) if missing else Rational(0)
    return phiA, phiM, ell_inf


def base_h(k, base):
    return Rational(0) if k < 0 else (Rational(0) if k == 0 else base[k])


def sample(target):
    n = tries = 0
    stats = {"M_empty": 0, "M_nonempty": 0, "A_differs": 0}
    while n < target and tries < 100000:
        tries += 1
        c = random.randint(3, 5)
        K = list(range(c + 1))
        k = random.randint(1, 2)
        I0 = set(random.sample(K[:c], k)) | {c}
        rest = [x for x in K if x not in I0]
        if len(I0) > len(rest):
            continue
        C0 = set(random.sample(rest, len(I0)))
        if max(C0) >= c:
            continue
        vac = [x for x in rest if x not in C0]
        sigma = random.choice(sorted(C0))
        Zref = {x for x in vac if random.random() < 0.5}
        Zret = {x for x in vac if random.random() < 0.5}
        cap_rows, cap_cols = I0 | Zref, (C0 | Zref) - {sigma}
        if len(cap_rows) != len(cap_cols) + 1:
            continue
        if any(len([x for x in cap_rows if x > u]) - len([x for x in cap_cols if x > u]) < 1
               for u in range(0, c)):
            continue
        base = {j: Rational(random.randint(1, 9), random.randint(1, 6)) for j in range(1, c + 2)}
        res = []
        for nu in (Rational(10) ** 12, Rational(10) ** 14):
            t = truth(c, I0, C0, sigma, Zref, Zret, base, nu)
            if t is None:
                break
            res.append(t[0])
        if len(res) < 2:
            continue
        a, b = res
        assert abs(a - 1) < Rational(1, 10 ** 6), (c, I0, C0, sigma, Zref, Zret, a)
        na, nb = (a - 1) * 10 ** 12, (b - 1) * 10 ** 14
        assert abs(na - nb) <= Rational(1, 10 ** 4) * max(1, abs(nb)), (na, nb)
        phiA, phiM, _ = limit_pieces(c, I0, C0, sigma, Zref, Zret, base)
        tol = Rational(1, 10 ** 4) * max(1, abs(nb))
        assert abs(nb - phiM) <= tol, (c, I0, C0, sigma, Zref, Zret, nb, phiA, phiM)
        if Zref <= Zret:
            stats["M_empty"] += 1
            assert abs(nb) <= tol
        else:
            stats["M_nonempty"] += 1
        if Zret - Zref and abs(phiA) > Rational(1, 100):
            stats["A_differs"] += 1
            assert abs(nb - phiA) > tol, (nb, phiA, phiM)
        n += 1
    return n, stats


n, stats = sample(80)
print(n, stats)
assert n >= 60 and stats["M_empty"] > 0 and stats["M_nonempty"] > 0 and stats["A_differs"] > 0
print("present end: T -> 1, nu^-1 coefficient = phiM (missing cap units only); added units contribute 0 PASS")
