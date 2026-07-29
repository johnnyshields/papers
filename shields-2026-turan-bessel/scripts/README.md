# Computational supplement

Verification scripts for *Sharp coefficientwise positivity for a matrix Turán
determinant of \({}_0F_1\)*.  Every script re-derives the closed forms it checks
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
| `verify_convolution_coefficients.py` | §3 | Asymmetric reciprocal-gamma convolution; `S_m`; the coefficient formulas `α_m, β_m, γ_m^(κ), c_m^(κ)` and the sharp `c_m`; the eq. (3.8) assembly `S_m M_m` with `√g` off-diagonal; convolution moments `E_δ D, E(DX), E D²`, cross-checked against direct Maclaurin coefficients of `A, B, C_κ`; and that `|δ| < a` is exactly where the convolution weights stay positive, while eq. (3.12) holds as an identity past it. |
| `verify_finite_law.py` | §3 (Rem. 3.4) | The finite law `π_{m,a}`; the coefficient identities `α_m = ½E(σ−X²)`, `β_m = 1−½E(DX)`, `c_m^(κ) = κm/2 − ½E D²`; the identity `F_m″(0)/F_m(0) = E(X²−σ) = −2ψ₁(a+m)`; and the finite-law form of `N_m`, with the conjugation `diag(1,g^{−1/2}) M_m diag(1,g^{−1/2})` of §4 carried out from eq. (3.8) rather than assumed. |
| `verify_gram.py` | §4 | The trigamma integral representation (4.1) and the integrand and inequality bounds of Lem. 4.1; the `ℓ²` norms `‖u‖² = ψ₁(x)`, `⟨u,v⟩ = q/(x−1)`, `‖v‖² = q²ψ₁(x−1)`; the sharp Gram-slack `(m−1)/(2(2a+2m−3))`; both Gram identities `N_m = Gram(ξ_m, η_m)` (4.9) and `M_m = Gram(ξ_m, √g η_m)` (4.10), with positive definiteness; that Thm. 4.2's `m=1` hypothesis `a ≥ 1/2` is load-bearing (`ρ_1 < 0` for small `a`); `M_0` rank one. |
| `verify_determinant.py` | §4, §5 | `MD` as the polarization of `det`; `Δ_n = ½ Σ S_k S_{n−k} MD(M_k, M_{n−k})` vs direct series; `Δ_1`; `det M_1` and the sharp anomaly threshold `a_* = 0.3690738484…`; `MD(M_1, M_m) > 0` for `0<a<1/2`; the exceptional `Δ_2 = Q_*/(2a⁶(a+1)³Γ⁴)` via `S_0 S_2 MD(M_0,M_2)+S_1² det M_1` and its positive sum-of-squares form; the κ-monotonicity identity. |
| `make_figure_det_m1.py` | §4 (Fig. 1, Lem. 4.3) | Every claim the figure and its caption make about `f` and `det M_1`: `det M_1` by the Gram route, the closed form and the 2x2 determinant; the exact window endpoints `f(1/4) = -4`, `f(1/2) = pi^2/2 - 4`; `f' > 0` on `(0,1/2)` from the series against a numerical derivative, and `f'(0.7) < 0` showing that interval is load-bearing; `a^2 f(a) -> -1`, so `f -> -infty`; `a_*` pinned to the ten digits the paper prints, and the figure's own `0.36907385` literals; the inertia trichotomy from the eigenvalues of `M_1`; and that no plotted sample is clipped.  With `--emit` it also prints the `pgfplots` coordinate block the figure inlines. |
| `verify_degree_one_threshold.py` | §2 (Rem. 2.3), §5 | The degree-one coefficient as the uniform threshold detector, exhibiting `{κ : Δ_1^(κ)(a) > 0 for every a > 0} = [1, ∞)` on an `a`-ladder — the claim Rem. 2.3 makes for the first nonzero determinant coefficient.  Eq. (5.7) is rebuilt from the §3 entries of `M_0, M_1^(κ)` and `Δ_1^(κ) = S_0 S_1 MD(M_0, M_1^(κ))`, so the sign test rests on the paper rather than on itself. |
| `verify_cauchy_mu_center.py` | §7 (Lem. 7.1, Rem. 7.3), §5 | The remainder `R(μ,w) = log E_μ(w) + (4μ²−1)/(8w)` and its order derivatives `∂_μ^j R(ν,w) = O(w^{−2})`, `j ≤ 2`, at the centre `μ = ν` of `K` — the only order the proof evaluates them at — by two independent routes (Cauchy contour integral over a fixed circle vs direct numerical differentiation); the downstream limits `z·G_ν → 1`, `1+P_ν → 1`, `H^(κ) − ((2κ−1)z − κ(1+2ν)) → 0`, `D_ν^(κ) → 2(κ−1)`; the §5 closing lower bound `Δ_1(a) > 1/(a⁴Γ(a)⁴)`; and the fixed-`a` form of Rem. 7.3 — with `c_n = [λⁿ] gAZZ_Θ > 0`, the admissible window `min_{n≤N} Δ_n^(1)/c_n` in `1−κ` is positive for every `N` and decreasing in `N`. |
| `verify_first_negative_degree.py` | §7 (Rem. 7.3) | `Δ_n^(κ)` by three independent routes agreeing to 45 digits: the Thm. 3.2 coefficient sum, the same sum in `MD` form, and a Cauchy convolution of the termwise Maclaurin coefficients of `Z` and its derivatives that uses no Chu–Vandermonde identity. On that footing, the least degree `n_min(a,κ)` with `Δ_n^(κ) < 0` is nondecreasing in `κ` and passes the `n ≤ 60` cap, which is Rem. 7.3's fixed-`a` claim; `κ < 1/2` makes `Δ_1^(κ) < 0` at every `a` on the grid (discriminant `2κ−1 ≤ 0`), and for `1/2 < κ < 1` the set `{a : Δ_1^(κ) > 0}` is a bounded interval, so degree one also detects failure at large `a`. |
| `verify_continuation.py` | §8 (Lem. 8.1) | The first assertion of Lem. 8.1, which §2 leans on twice: `Z` and its fixed-order parameter and Euler derivatives are entire in `(a,λ)`, the series converging locally uniformly. `Z` is finite at `a = 0,−1,−2,−3` where the quotient `0F1(;a;λ)/Γ(a)` is not, and agrees with it off the pole set; `∮Z da` and `∮Z dλ` vanish by Cauchy's theorem, with the same contour on `0F1` itself nonzero as a positive control that the test detects a pole when there is one; termwise differentiation is legitimate, `∂_a^j Θ_λ^l Z` agreeing across the Cauchy-integral and numerical routes; and the tail past `N` is uniformly small on `|a| ≤ 3, |λ| ≤ 2`. |
| `verify_bessel_reduction.py` | §6, §7, §8 | `I_{a−1}(2√λ) = λ^{(a−1)/2} Z`; the bridge identities, the matrix congruence with `diag(1,2/√g)`, and the reduction `D_{a−1}(2√λ) = 4Δ/(gZ⁴)`; the boundary-correction optimality `D_{ν,R} = D_ν + G_ν(R−4/g)`; boundary limits and the rank-one `z=0` matrix; the small-`z` law (slope-2 fit) and its negative-order leg; negative-order failure `Δ_2<0` on `−2<a<−1` with the polynomial certificate.  Also what licenses differentiating the large-argument expansion in the Lem. 7.1 proof: `|E_μ−1| < 1/2` uniformly on `K × Σ_δ` past a threshold `W` (with the failure in-sector below `W`, so `W` is load-bearing), eq. (7.2) at rate `w^{−2}`, the Cauchy disc `|w−z| ≤ εz ⊂ Σ_δ`, and the exponent ledger `∂_μ^j ∂_w^ℓ R = O(w^{−2−ℓ})`, `Θ_w^k R = O(w^{−2})`. |
| `verify_context.py` | §9 | The infinitesimal Turánian `Z(a+δ)Z(a−δ)−Z² = −Aδ²+O(δ⁴)`, with the evenness in `δ` that rules out a `δ³` term; that the `F(ν,y)` forms agree with eqs. (2.7)–(2.9) under `z = e^y`; and the rescaling variance: `e^{cy}` fixes `G_ν,P_ν` but shifts `D_ν` by `+2cG_ν`, so any `c < −D_ν/(2G_ν)` makes it negative and the sign is not rescaling-invariant. |
| `check_coefficients_stdlib.py` | §5 (Lem. 5.3) | Dependency-free audit of `exported_coefficients.json`: expands the three blocks of eq. (5.5) in exact integer arithmetic and checks the stored powers and coefficients against them, plus integrality and strict positivity.  With eqs. (5.4)–(5.5) that gives `Δ_2 > 0`; the identities themselves are `verify_determinant.py`'s. |
| `verify_dlmf_locators.py` | citations | Every DLMF locator the paper cites (5.15.1, 10.17.1, 10.25.2, 10.40.1, 10.40(iii), 10.38), checked for mathematical content against the local section copies in `../refs/`, plus coverage that no cited locator lacks a page. |

Each script prints `PASS` lines and ends with `ALL PASS`; any broken identity raises
`AssertionError` and stops the script with a nonzero exit code.

Script headers cite each paper result by number *and* by its LaTeX label
(`Lemma 5.3 = lem:Delta2-positive`), since the numbers move when the paper is
renumbered but the labels do not.
