# Computational supplement

Verification scripts for *Sharp coefficientwise positivity for a matrix Turán
determinant of ${}_0F_1$*.  Every script re-derives the closed forms it checks
from the series definition of

    Z(a, λ) = Σ_{k≥0} λ^k / (k! Γ(a+k)),

so the symbolic identities are pinned to the objects that define them rather than
transcribed.  All checks are at the sharp endpoint κ = 1 unless a script explicitly
carries the parameter κ.  Symbolic work uses SymPy; numerical work uses mpmath at
arbitrary precision (no floating-point arithmetic in the verification loops).

Reference environment: Python 3.12, SymPy 1.14.0, mpmath 1.3.0.

```bash
python -m pip install -r requirements.txt
./run_all.sh
```

## Scripts by section

| Script | Paper section | Content |
| --- | --- | --- |
| `verify_convolution_coefficients.py` | §3 | Asymmetric reciprocal-gamma convolution; `S_m`; the coefficient formulas `α_m, β_m, γ_m^(κ), c_m^(κ)` and the sharp `c_m`; convolution moments `E_δ D, E(DX), E D²`, cross-checked against direct Maclaurin coefficients of `A, B, C_κ`. |
| `verify_conditional_hessian.py` | §3 (Rem. 3.3) | The finite law `π_{m,a}`; the coefficient identities `α_m = ½E(R−X²)`, `β_m = 1−½E(DX)`, `c_m^(κ) = κm/2 − ½E D²`; the identity `F_m″(0)/F_m(0) = E(X²−R) = −2ψ₁(a+m)`; the finite-law form of `N_m`. |
| `verify_gram.py` | §4 | Trigamma integrand and inequality bounds; the `ℓ²` norms `‖u‖² = ψ₁(x)`, `⟨u,v⟩ = q/(x−1)`, `‖v‖² = q²ψ₁(x−1)`; the sharp Gram-slack `(m−1)/(2(2a+2m−3))`; `N_m = Gram(ξ_m, η_m)`; `M_0` rank one. |
| `verify_determinant.py` | §4, §5 | `MD` as the polarization of `det`; `Δ_n = ½ Σ S_k S_{n−k} MD(M_k, M_{n−k})` vs direct series; `Δ_1`; `det M_1` and the sharp anomaly threshold `a_* = 0.3690738484…`; `MD(M_1, M_m) > 0` for `0<a<1/2`; the exceptional `Δ_2 = Q_*/(2a⁶(a+1)³Γ⁴)` via `S_0 S_2 MD(M_0,M_2)+S_1² det M_1` and its positive sum-of-squares form; the κ-monotonicity identity. |
| `verify_bessel_reduction.py` | §6, §7 | `I_{a−1}(2√λ) = λ^{(a−1)/2} Z`; the bridge identities, the matrix congruence with `diag(1,2/√g)`, and the reduction `D_{a−1}(2√λ) = 4Δ/(gZ⁴)`; the boundary-correction optimality `D_{ν,R} = D_ν + G_ν(R−4/g)`; boundary limits and the rank-one `z=0` matrix; the small-`z` law (slope-2 fit); negative-order failure `Δ_2<0` on `−2<a<−1`. |
| `verify_context.py` | §8 | The infinitesimal Turánian `Z(a+δ)Z(a−δ)−Z² = −Aδ²+O(δ⁴)`, and the gauge variance: rescaling `I_s(e^y)` by `e^{cy}` fixes `G,p` but shifts the Schur determinant by `+2cG`. |
| `check_coefficients_stdlib.py` | §5 | Dependency-free positivity audit of the exported `Q_*` coefficient blocks in `exported_coefficients.json`. |

Each script prints `PASS` lines and ends with `ALL PASS`; any broken identity raises
`AssertionError` and stops the script with a nonzero exit code.
