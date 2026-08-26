#!/usr/bin/env python3
r"""Paper section `subsec:microcanonical` (Microcanonical Bessel fibers and canonical averaging),
subsec:microcanonical: thm:ensemble-hierarchy.

Under the symmetric finite law
    pi_{m,a}(i) = 1/(S_m * i!(m-i)! Gamma(a+i) Gamma(a+m-i)),   0 <= i <= m,
with D = m-2I, X = psi(a+m-I)-psi(a+I), sigma = psi_1(a+I)+psi_1(a+m-I) (the paper's
sigma), this verifies the displays of thm:ensemble-hierarchy:

  * E D = E X = 0 (symmetry);
  * the finite-law coefficient identities
        alpha_m = (1/2) E(sigma - X^2),
        beta_m  = 1 - (1/2) E(D Xi),
        c_m^(kappa) = kappa m/2 - (1/2) E D^2   (kappa=1 gives c_m);
  * the second-logarithmic-derivative identity F_m''(0)/F_m(0) = E(X^2 - sigma) =
    -2 psi_1(a+m) (thm:ensemble-hierarchy; cf. F_m''(0) = -2 S_m psi_1(a+m), eq. (F-second-delta));
  * the normalized coefficient matrix N_m = diag(1,g^{-1/2}) M_m diag(1,g^{-1/2})
    -- defined in subsec:gram, with M_m from eq. (matrix-series) of sec:coefficients -- in its
    finite-law form, with the conjugation carried out rather than assumed.

All checks are exact symbolic evaluations of finite sums, for m = 0..5 and symbolic
(a, kappa); thm:ensemble-hierarchy states them for every m >= 0.
"""
from __future__ import annotations
import sympy as sp

a, kap = sp.symbols('a kappa', positive=True)
delta = sp.symbols('delta', real=True)
M_MAX = 5

def S(m):
    return sp.rf(2*a+m-1, m)/(sp.factorial(m)*sp.gamma(a+m)**2)

def alpha_m(m):
    return sp.polygamma(1, a+m)

def beta_m(m):
    return sp.Integer(1) if m == 0 else (2*a+m-2)/(2*(a+m-1))

def c_sharp(m):
    return sp.Integer(0) if m in (0, 1) else m*(m-1)/(2*(2*a+2*m-3))

def c_kappa(m):
    if m == 0:
        return sp.Integer(0)
    if m == 1:
        return (kap-1)/2
    return kap*m/2 - m*(2*a+m-2)/(2*(2*a+2*m-3))

g = sp.polygamma(1, a)

# ---------------------------------------------------------------------------
# Finite-law moments and the coefficient identities (thm:ensemble-hierarchy)
# ---------------------------------------------------------------------------
for m in range(M_MAX + 1):
    w = [1/(sp.factorial(i)*sp.factorial(m-i)*sp.gamma(a+i)*sp.gamma(a+m-i))
         for i in range(m+1)]
    Sm = sum(w)
    assert sp.simplify(sp.expand_func(Sm - S(m))) == 0, ('norm', m)   # sum = S_m

    prob = [wi/Sm for wi in w]
    D  = [sp.Integer(m-2*i) for i in range(m+1)]
    X  = [sp.digamma(a+m-i) - sp.digamma(a+i) for i in range(m+1)]
    sigma = [sp.polygamma(1, a+i) + sp.polygamma(1, a+m-i) for i in range(m+1)]

    E   = lambda arr: sum(prob[i]*arr[i] for i in range(m+1))
    ED  = sp.simplify(sp.expand_func(E(D)))
    EX  = sp.simplify(sp.expand_func(E(X)))
    assert ED == 0 and EX == 0, ('symmetry', m)

    EsigmamX2 = sp.expand_func(E([sigma[i] - X[i]**2 for i in range(m+1)]))
    EDX   = sp.expand_func(E([D[i]*X[i] for i in range(m+1)]))
    ED2   = sp.expand_func(E([D[i]**2 for i in range(m+1)]))

    assert sp.simplify(sp.expand_func(sp.Rational(1, 2)*EsigmamX2 - alpha_m(m))) == 0, ('alpha', m)
    assert sp.simplify(sp.expand_func((1 - sp.Rational(1, 2)*EDX) - beta_m(m))) == 0, ('beta', m)
    assert sp.simplify(sp.expand_func((sp.Rational(m, 2) - sp.Rational(1, 2)*ED2) - c_sharp(m))) == 0, ('c', m)
    # eq. (c-cond-derivation): kappa E J - E J^2 + E(I J) = kappa m/2 - (1/2) E D^2
    assert sp.simplify(sp.expand_func((kap*sp.Rational(m, 2) - sp.Rational(1, 2)*ED2) - c_kappa(m))) == 0, ('c_kappa', m)

    # The finite-law form of the coefficient matrix.  M_m is eq. (matrix-series) of
    # sec:coefficients; N_m = diag(1,g^{-1/2}) M_m diag(1,g^{-1/2}) is defined in subsec:gram,
    # just before thm:gram.  Build M_m literally from eq. (matrix-series) and conjugate, so
    # the normalization is tested rather than assumed.
    rg = 1/sp.sqrt(g)
    Mm = sp.Matrix([[alpha_m(m), sp.sqrt(g)*beta_m(m)],
                    [sp.sqrt(g)*beta_m(m), 1 + g*c_sharp(m)]])          # eq. (matrix-series)
    Nm_conj = sp.diag(1, rg) * Mm * sp.diag(1, rg)                       # subsec:gram
    Nm_law = sp.Matrix([[sp.Rational(1, 2)*EsigmamX2, 1 - sp.Rational(1, 2)*EDX],
                        [1 - sp.Rational(1, 2)*EDX,
                         1/g + sp.Rational(m, 2) - sp.Rational(1, 2)*ED2]])
    assert sp.simplify(sp.expand_func(Nm_conj - Nm_law)) == sp.zeros(2), ('N_m', m)
    # and the conjugation really does undo the sqrt(g) placement of eq. (matrix-series):
    assert sp.simplify(sp.expand_func(
        Nm_conj - sp.Matrix([[alpha_m(m), beta_m(m)],
                             [beta_m(m), 1/g + c_sharp(m)]]))) == sp.zeros(2), ('N_m conj', m)
print('PASS: E D = E X = 0, the finite-law coefficient identities, and'
      ' N_m = diag(1,g^-1/2) M_m diag(1,g^-1/2) in finite-law form')

# ---------------------------------------------------------------------------
# Second logarithmic derivative of the asymmetric convolution F_m(delta), eq. (F-second-delta)
# / thm:ensemble-hierarchy: F_m''(0)/F_m(0) = E(X^2 - sigma) = -2 psi_1(a+m).  Independent of the
# loop above.
# ---------------------------------------------------------------------------
for m in range(M_MAX + 1):
    Fm = sum(1/(sp.factorial(i)*sp.factorial(m-i)
                *sp.gamma(a+delta+i)*sp.gamma(a-delta+m-i))
             for i in range(m+1))
    # eq. (Fdelta): the closed form of the same sum, lem:convolution at
    # (alpha, beta) = (a+delta, a-delta).
    Fm_closed = sp.rf(2*a + m - 1, m)/(sp.factorial(m)
                                       *sp.gamma(a + m + delta)*sp.gamma(a + m - delta))
    assert sp.simplify(sp.expand_func(sp.simplify(Fm/Fm_closed))) == 1, ('Fdelta', m)
    ratio = sp.expand_func((sp.diff(Fm, delta, 2)/Fm).subs(delta, 0))
    assert sp.simplify(sp.expand_func(ratio + 2*sp.polygamma(1, a+m))) == 0, ('Fm2', m)
print('PASS: eq. (Fdelta) F_m(delta) = (2a+m-1)_m/(m! Gamma(a+m+delta) Gamma(a+m-delta)),')
print('      and F_m\'\'(0)/F_m(0) = E(X^2 - sigma) = -2 psi_1(a+m)')

print('ALL PASS: verify_finite_law')
