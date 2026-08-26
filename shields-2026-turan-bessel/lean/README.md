# Lean 4 formalization — Canonical–microcanonical positivity and phase geometry for a Bessel–₀F₁ matrix Turán determinant

Formalizes the core of `shields-2026-turan-bessel.tex` against Mathlib
(`leanprover/lean4:v4.30.0-rc2`, namespace `TuranBessel`).  **The development is
unconditional: no `sorry`, no project axiom anywhere in the tree.**  Every result
below reports `[propext, Classical.choice, Quot.sound]` under `#print axioms`.

Every theorem of the paper carrying algebraic content is proved: the endpoint
classification, `lem:boundary-positivity` in full, `thm:two-parameter-coeff` as
an iff in `τ` on every `κ ≥ 1` slice, `prop:scalar-H` with both directions of
`eq:H-kappa-global`, the sharp quadrant of `prop:bessel-sharpness`,
`prop:c-monotone` entire, and the ensemble hierarchy of
`thm:ensemble-hierarchy` and `prop:four-copy` at general `(κ,τ)`.

Two absences in the pinned Mathlib bound the remainder, and L6 below separates
them.  Bessel large-argument asymptotics gate `lem:large-argument-limit`, and
through it the `κ < 1` exclusion at fixed `a` in `thm:two-parameter-coeff` and
`thm:coefficientwise`, together with the least-constant half of
`prop:bessel-sharpness`.  Hoeffding's sampling-without-replacement inequality
gates the tail estimate of `lem:central-moments` and the critical-scaling
asymptotics downstream of it; the two exact inputs to that lemma —
`eq:Sm-asymptotic` and the base-law moments of `eq:hypergeom-moments` — are
proved.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

## Result coverage

The **central theorem of the paper** and its sharpness.  Every Lean name below is
pinned to the standard footprint by a `#guard_msgs` in
`TuranBessel/AxiomCheck.lean`, so a `sorry` or a stray axiom entering any
dependency fails the build rather than silently weakening a row here.

| Result | Paper | Lean |
|---|---|---|
| Sharp coefficientwise positivity, `Δ_n(a)>0`, `κ=1` | `thm:coefficientwise` | `Main.coefficientwise_positivity` |
| Degree-one threshold sharp, uniformly in `a`: `κ<1` fails / `κ≥1` holds | `rem:uniform-degree-one`, `eq:MD01-kappa` | `Threshold.MDkappa_uniform_iff`, `MDkappa_neg_exists`, `MDkappa_ge_pos` |
| Gram positive-definiteness of the coefficient fiber, at a free shift | `thm:gram`, `eq:Nm-gram`, `eq:Mm-gram` | `GramRep.NmatS_eq_gram`, `Mmat_eq_gram_smul`, `NmatS_pd`; `Gram.Nmat_pd_two`, `Nmat_pd_one` at `s = 1/g` |
| Degree-one inertia trichotomy and the threshold `a✱` | `lem:M1-indefinite` | `Anomaly.M1_inertia_trichotomy`, `Nmat_one_not_psd`, `Nmat_one_pd_of_fM1_pos` |
| Degree-two `Q_*` decomposition, `Δ_2>0` | `lem:Delta2-positive`, `eq:Qstar-decomp` | `Degree.Dcoeff_two_pos` |
| Negative-order failure `Δ_2(a)<0` on `-2<a<-1` | `prop:negative-coeff-failure` | `NegativeOrder.Dcoeff_two_neg` |
| Two-parameter affine identity, in `MD` and coefficientwise | `eq:affine-two-param` | `Phase.MD_NmatKT`, `Phase.DcoeffKT_affine` |
| `τ_cw` is the exact degree-one root, and `τ_cw < 1` | `eq:tau-cw`, `thm:two-parameter-coeff` | `Phase.DcoeffKT_degree_one_boundary`, `Phase.tauCw_lt_one`, `Phase.tauCw_antitone` |
| Boundary pieces: `det N̂_1 ≥ 0`, `s_*+c_2>0`, `P_2>0` | `lem:boundary-positivity` | `Phase.det_N1_boundary_eq`, `det_N1_boundary_nonneg`, `sStar_add_c_two_pos`, `P2boundary_pos` |
| Cubic trigamma bound; `1 < a²ψ₁(a)`; `c(a) > 3/2` | `eq:trig-upper-cubic`, `eq:tau-cw`, `lem:large-argument-limit` | `Phase.trigamma_lt_cubic`, `Phase.sq_mul_trigamma_gt_one`, `Phase.cCrit_gt` |
| Asymmetric reciprocal-gamma convolution | `lem:convolution`, `eq:asymmetric-convolution` | `Convolution.gamma_convolution`, `Convolution.poch_vandermonde` |
| `Z` entire in `λ`, positive, and `[λᵐ]Z² = S_m` | `eq:Zdef`, `sec:coefficients` | `Zseries.summable_zterm`, `Zseries.Zfun_pos`, `Zseries.Zfun_sq` |
| `sred a m = S_m Γ(a)²` | `sec:coefficients` | `Zseries.sred_eq_sweight_mul` |
| Scalar forms of `H_ν^{(κ)}`: Amos root, Turánian, and `κ ≥ 1` in both directions | `prop:scalar-H`, `eq:H-Amos-general`, `eq:Amos-bound-exact`, `eq:H-turan-exact`, `eq:H-kappa-global` | `ScalarH.Hratio_pos_iff_ratio`, `ScalarH.Hratio_one_pos_iff_amos`, `ScalarH.Hratio_eq_turan`, `ScalarH.Hratio_pos_of_one_le`; `Sharpness.besselHkappa_pos_iff` |
| Rank-one boundary determinant `4(τ-1)` | `rem:schur-correction` | `ScalarH.schur_boundary_det` |
| Wedge/MD positivity | `lem:MD-positive` | `MatrixMD.SymMat.MD_nonneg`, `SymMat.MD_pos_of_psd_pd` |
| Trigamma bounds (both sharp, trapezoidal) | `lem:trigamma-bounds`, `eq:trig-lower`, `eq:trig-upper-half` | `Trigamma.trigamma_gt_inv_sharp`, `trigamma_lt_upper` |
| ℓ² Cauchy–Schwarz | (Gram argument) | `Trigamma.tsum_mul_sq_le` |
| Sharp pointwise Bessel–Schur inequality, and the PD matrix | `thm:bessel`, `cor:bessel-matrix` | `Bridge.bessel_schur_ineq`, `bessel_schur_matrix_pd` |
| `Δ = det 𝒯` is its own Maclaurin sum, every real `λ` | `eq:Delta-n-MD` | `TuranDet.hasSum_turanDet`, `Bridge.hasSum_turanDetCoeff` |
| The Bessel dictionary `G_ν, P_ν, H_ν^{(κ)}, det 𝒮_ν` | `eq:Gnu`–`eq:Hnu-kappa`, `eq:D-Delta` | `BesselDict`, `BesselDictPH`, `BesselLaw.besselHkappa_eq` |
| The discrete Bessel law and the covariance deficit | `cor:bessel-law`, `eq:covariance-ineq` | `BesselLaw.normalizedTuran_eq`, `covariance_ineq` |
| `lem:boundary-positivity`, all four steps and the chain | `lem:boundary-positivity` | `Boundary.boundary_positivity` |
| Two-parameter coefficientwise positivity, `κ ≥ 1` | `thm:two-parameter-coeff` | `WallOrder.DcoeffKT_pos_of_gt`, `DcoeffKT_nonneg_of_ge`, `two_parameter_boundary` |
| `S_m` as a pair of gamma ratios (Legendre duplication) | `eq:Sm-gamma-ratio` | `Scaling.sweight_eq_gamma_ratio` |
| `3/2 < c(a) < 7/2` | `eq:c-range` | `Scaling.cCrit_mem` |
| `c(a)` strictly decreasing, with range exactly `(3/2,7/2)` | `prop:c-monotone` | `CriticalConstant.cCrit_strictAnti_and_range`; `Tetragamma.trigamma_sq_add_tetragamma_pos`, `hasDerivAt_trigamma` |
| Two-term expansion of `S_m`, remainder two-sided with its constant written out | `eq:Sm-asymptotic` | `GammaRatio.abs_sweight_div_sub_le` |
| Exact variance of the symmetric hypergeometric base law | `eq:hypergeom-moments` | `GammaRatio.hyperWeight_variance`, `hyperWeight_second_moment_scaled` |
| The microcanonical fiber law, its three moments, and its differential form | `thm:ensemble-hierarchy` | `Microcanonical.hasSum_pairPMF`, `sum_condPMF`, `NmatKT_eq_condExp`, `NmatKT_eq_baseline_sub_cov`, `NmatKT_eq_ellUV`, `normalizedTuran_eq_pairExp` |
| Four-copy sectors, and the defect as a canonical sector average | `prop:four-copy` | `FourCopy.hasSum_fourPMF`, `DcoeffKT_eq_kExp`, `besselDefect_eq_sectorAverage`; `SectorAverage.besselDefectKT_eq_sectorAverage` at general `(κ,τ)` |
| The determinant series at general `(κ,τ)`, and its degree-zero coefficient | `eq:Tkt`, `eq:Delta0-tau` | `TuranDetKT.hasSum_turanDetKT`, `DcoeffKT_zero`, `turanDetKT_pos` |
| `τ` converse of the coefficientwise phase diagram | `thm:two-parameter-coeff` | `Sharpness.DcoeffKT_pos_iff_of_one_le`, `DcoeffKT_nonneg_iff_of_one_le` |
| Bessel–Schur positivity on the sharp quadrant `κ,τ ≥ 1`, and `τ ≥ 1` forced | `prop:bessel-sharpness`, `eq:Dkappa-tau-Delta` | `Sharpness.besselDefectKT_eq`, `bessel_sharpness_pos`, `bessel_schur_matrix_KT_pd`, `exists_bessel_defect_neg_of_lt_one` |
| The Schur matrix at `z = 0`, rank one exactly at `τ = 1` | `cor:bessel-matrix`, `rem:schur-correction` | `Sharpness.schurMatKT_arg_zero`, `schurMatKT_arg_zero_det`, `schurMat_arg_zero_rank_one` |

In this table `Δ_n` is the coefficient in its proven mixed-determinant form
(`Dcoeff`, `eq:Delta-n-MD`); its identification with the genuine Maclaurin
coefficient `[λⁿ] det 𝒯` is `Bridge.hasSum_turanDetCoeff`, and
`turanDetCoeff_pos` is an ordinary theorem.

Trigamma `ψ₁` is **built from scratch** (`∑(y+n)⁻²`) because Mathlib has no
polygamma. The algebraic identities are cross-checked in `../scripts` (sympy).

## Structural coverage

Every result of `../shields-2026-turan-bessel.tex` carrying algebraic content, with
its Lean status.  `proven` means sorry-free and axiom-clean.  Rows are keyed by
`\label`, not by number.

| Paper | Lean | Status |
|---|---|---|
| `lem:trigamma-bounds` | `trigamma_gt_inv_sharp`, `trigamma_lt_upper`, `Gram.inv_trigamma_gt` | proven |
| `eq:trig-upper-cubic` | `Phase.trigamma_lt_cubic` | proven |
| `thm:gram`, `eq:Nm-gram`, `eq:Mm-gram`, `eq:rho-m` | `GramRep.NmatS_eq_gram`, `Mmat_eq_gram_smul`, `NmatS_det_pos`, `NmatS_pd`, `inner_xi_xi`, `inner_xi_eta`, `inner_eta_eta`; `Gram.slack_identity`, `rho_pos_of_two`, `rho_pos_one`, `cross_sum`, `Nmat_det_pos`, `Nmat_pd_two`, `Nmat_pd_one` | proven — at the free shift `s` the theorem is stated at; the `Gram` names are the case `s = 1/g` |
| `lem:M1-indefinite` | `Anomaly.M1_inertia_trichotomy`, `Nmat_one_not_psd`, `Nmat_one_pd_of_fM1_pos` | proven (the decimal `a✱` is a locator, not formalized) |
| `lem:MD-positive` | `SymMat.MD_nonneg`, `SymMat.MD_pos_of_psd_pd` | proven |
| `lem:Delta-n-noneq2` | `MD_Nmat_nonneg`, `MD_N0_Nn_pos`, `MD_N0_N1_pos`, `Dcoeff_one_pos`, `MD_N1_Nm_pos` | proven |
| `lem:Delta2-positive` | `Dcoeff_two_eq`, `Rval_pos_of_pos`, `Qstar2_pos_of_pos`, `Dcoeff_two_pos` | proven |
| `thm:coefficientwise`, `κ=1` | `coefficientwise_positivity` | proven, on `Dcoeff` |
| `rem:uniform-degree-one`, `eq:MD01-kappa` — degree-one sharpness uniform in `a` | `MDkappa_eq`, `MDkappa_ge_pos`, `MDkappa_neg_exists`, `MDkappa_uniform_iff` | proven |
| `thm:gram`, degree 0 (`N_0` rank one) | `Nmat_zero_psd`, `Nmat_zero_ne` | proven |
| `thm:two-parameter-coeff`, the boundary | `Phase.DcoeffKT_degree_one_boundary`, `Phase.tauCw_lt_one`, `Phase.tauCw_antitone`, `Phase.DcoeffKT_affine`, `Phase.pRed_pos`, `Phase.qRed_pos` | proven — the boundary equation, `τ_cw<1`, and the affine structure; positivity of every degree `n ≥ 2` on it is `WallOrder.two_parameter_boundary` |
| `lem:boundary-positivity`, its algebraic steps | `Phase.det_N1_boundary_eq`, `det_N1_boundary_nonneg`, `det_N1_boundary_factor_pos`, `sStar_add_c_two_pos`, `P2boundary_pos` | proven |
| `lem:large-argument-limit`, the bound `c(a) > 3/2` | `Phase.cCrit_gt` | proven (the expansion itself is L6) |
| `prop:negative-coeff-failure` | `NegativeOrder.Dcoeff_two_neg` | proven |
| `lem:convolution`, `eq:asymmetric-convolution` | `Convolution.gamma_convolution`, `Convolution.poch_vandermonde`, `Convolution.Gamma_add_natCast` | proven |
| `eq:Zdef`; `[λᵐ]Z² = S_m` | `Zseries.summable_zterm`, `Zseries.Zfun_pos`, `Zseries.Zfun_sq`, `Zseries.sred_eq_sweight_mul` | proven |
| `eq:Zdef` — `Z` **is** Mathlib's regularized `₀F₁` | `Hypergeometric.ofReal_Zfun` | proven (no hypothesis; both sides are `tsum`s) |
| `eq:I-Z`, the `J`-side: `J_{a-1}(x) = (x/2)^{a-1} Z(a,-(x/2)²)` | `Hypergeometric.besselJ_eq_Zfun` | proven |
| **`eq:I-Z`**: `I_{a-1}(2√λ) = λ^{(a-1)/2} Z(a,λ)` | `BesselI.besselIReal_eq_rpow_mul_Zfun`, `BesselI.ofReal_besselI_eq_Zfun` | proven, over `BesselI.besselI` defined there |
| `I_ν` analytic; `I_ν>0` for `ν>-1, x>0`; `log I_ν` splits off `log Z` | `BesselI.analyticAt_besselI`, `besselIReal_pos`, `log_besselIReal` | proven |
| `ψ' = ψ₁`, tying `Trigamma.trigamma` to `Real.Gamma` and to Mathlib's `digamma` | `ParameterCalculus.deriv_realDigamma_eq_trigamma`, `deriv_digamma_ofReal` | proven |
| `∂_a Z`, `∂_a² Z` termwise (differentiation under the sum) | `ParameterCalculus.hasDerivAt_Zfun_param`, `hasDerivAt_deriv_Zfun` | proven |
| `eq:F-second-delta`, `F_m''(0) = -2S_mψ₁(a+m)` | `ParameterCalculus.deriv_deriv_Fdelta` | proven |
| `eq:alpha`, `[λᵐ]A = S_mψ₁(a+m)` | `AlphaCoeff.hasSum_Afun` | proven |
| `eq:beta`, `[λᵐ]B = S_mβ_m` | `BetaGammaCoeff.tsum_beta_eq_B` | proven |
| `[λᵐ]C_{κ,τ} = S_m(τ+gc_m^{(κ)})` | `BetaGammaCoeff.tsum_gamma_eq_C` | proven, at general `(κ,τ)` |
| **`eq:Delta-n-MD`** — `Δ = det 𝒯` is the sum of `∑ₙ Δ_n λⁿ`, `Δ_n = ψ₁(a)Γ(a)⁻⁴/2·Dcoeff`, and `Δ_n` as an expectation over `eq:Tn-Kn-law` | `TuranDet.hasSum_turanDet`, `Bridge.hasSum_turanDetCoeff`; `FourCopy.DcoeffKT_eq_kExp`, `Dcoeff_eq_kExp`, `turanDetCoeff_eq_kExp` | proven — both equalities, the probabilistic one at general `(κ,τ)` |
| `thm:coefficientwise` → the true Maclaurin coefficient | `turanDetCoeff_pos` | proven |
| `prop:scalar-H` — `eq:H-Amos-general`, `eq:Amos-bound-exact`, `eq:H-turan-exact` | `ScalarH.Hratio_pos_iff`, `Hratio_pos_iff_ratio`, `Hratio_one_pos_iff_amos`, `Hratio_eq_turan`, `Hratio_shift`, `Hratio_pos_of_one_le`, `amosRoot_eq_div`, `amosRoot_antitone` | proven **in the ratio variable** — every claim about the quadratic `r²+2(ν+κ)r-z²` and about the ratio recurrence.  Identifying `H_ν^{(κ)}` with that quadratic (`eq:H-r-forms`) is `BesselLaw.besselHkappa_eq`, at general `κ` |
| `eq:H-kappa-global`, both directions | `Sharpness.besselHkappa_pos_iff`, `besselHkappa_pos_of_one_le`, `exists_besselHkappa_neg_of_lt_one`, `besselHfun_pos`, `besselHkappa_eq_zform`, `strictConcaveOn_log_Zfun`, `Zfun_turan`, `ZEulerSeries_eq_shift`, `ZEuler2Series_eq_shift` | proven — `H_ν^{(κ)}>0` on `z>0` iff `κ ≥ 1`.  The `κ ≥ 1` half is internal rather than cited: `Z_1² > ZZ_2` is the midpoint case of strict concavity of `a ↦ log Z(a,λ)`, which is `A/Z² > 0`.  The `κ<1` half is the `λ ↓ 0` value `(κ-1)/a` of the same bracket |
| `cor:bessel-law`'s underdispersion reading, unconditionally | `Sharpness.besselLaw_underdispersed` | proven — `Var Y < E Y` for every `ν>-1`, `z>0` |
| `rem:schur-correction`, the `z ↓ 0` matrix and its determinant `4(τ-1)` | `ScalarH.schur_boundary_det`; `Sharpness.schurMatKT_arg_zero`, `schurMatKT_arg_zero_det`, `continuousAt_besselG_arg`, `continuousAt_besselP_arg`, `continuousAt_besselHkappa_arg` | proven |
| `thm:coefficients` | `Nmat`, `ccoef`, `sred` are definitions; their coefficient identities are proven (`AlphaCoeff`, `BetaGammaCoeff`) | proven |
| `eq:Gnu`–`eq:Hnu-kappa`, `eq:D-Delta` | `Bridge.besselG_eq`, `besselP_eq`, `besselH_eq`, `besselDefect_eq`; `BesselLaw.besselHkappa_eq` at general `κ` | proven |
| `thm:bessel` | `Bridge.bessel_schur_ineq` | proven |
| `cor:bessel-matrix` | `Bridge.bessel_schur_matrix_pd`; `Sharpness.schurMatKT_arg_zero`, `schurMat_arg_zero_rank_one`, `continuousAt_besselG_arg`, `continuousAt_besselP_arg`, `continuousAt_besselHkappa_arg` | proven, including the limit clause — the extension to the rank-one matrix `((g,2),(2,4/g))` is a two-sided `ContinuousAt` at `z = 0`, stronger than the paper's `z ↓ 0` |
| `lem:boundary-positivity` | `Boundary.boundary_positivity`, `NmatHat_pd`, `MD_NmatHat_zero_pos`, `MD_NmatHat_one_pos`, `DcoeffKT_boundary_two_pos` | proven |
| `cor:bessel-law`, `eq:bessel-law-meanvar`, `eq:bessel-law-param`, `eq:covariance-deficit-matrix`, `eq:covariance-loewner`, `eq:H-dispersion`, `eq:covariance-ineq` | `BesselLaw` (`hasSum_besselPMF`, `Afun_div_sq_eq`, `Bseries_div_sq_eq`, `Cseries_div_eq`, `normalizedTuran_eq`, `besselHkappa_eq_dispersion`, `covariance_ineq`, `besselDefect_eq_covariance`) | proven |
| `thm:ensemble-hierarchy`, `eq:pair-total-law` | `Microcanonical.pairPMF_eq_conv`, `hasSum_pairPMF`, `besselPMF_div_pairPMF`, `sum_condPMF`, `condPMF_reflect` | proven — both identities, and the conditional law carries no `λ` |
| `eq:finite-law-entries` | `Microcanonical.alpha_eq_condExp`, `beta_eq_condExp`, `ckappa_eq_condExp`, `condExp_dfin`, `condExp_xiScore` | proven — all three entries, with the two vanishing means `E Ξ_m = E D_m = 0` |
| `eq:microcanonical-covariance-deficit` | `Microcanonical.NmatKT_eq_condExp`, `NmatKT_eq_baseline_sub_cov` | proven, at general `(κ,τ)` |
| `eq:microcanonical-schur` | `Microcanonical.NmatKT_eq_ellUV`, `deriv_deriv_log_eq` | proven — a genuine second logarithmic derivative of the two-parameter fiber weight `Fuv` at the origin, in both variables and mixed |
| `eq:canonical-fiber-average` | `Microcanonical.normalizedTuran_eq_pairExp`, `pairExp_alpha`, `pairExp_beta`, `pairExp_gamma` | proven, at general `(κ,τ)` |
| `prop:four-copy`, `eq:four-total-law`, `eq:Tn-Kn-law` | `FourCopy.Zfun_pow_four`, `hasSum_fourPMF`, `sum_kPMF`, `pairPMF_div_fourPMF` | proven |
| `eq:sector-density`, `eq:D-canonical-average` | `FourCopy.hasSum_sectorDensity`, `besselDefect_eq_sectorAverage`; `SectorAverage.hasSum_sectorDensityKT`, `besselDefectKT_eq_sectorAverage` | proven, at general `(κ,τ)` |
| `rem:ensemble-positivity`, the vacuum sector `d_0^{(κ,τ)} = 4(τ-1)` | `FourCopy.sectorDensityKT_zero` | proven |
| `eq:Tkt`, `eq:Delta0-tau` — the determinant series at general `(κ,τ)` | `TuranDetKT.turanDetKT`, `turanDetKT_endpoint`, `cauchy_eq_factor_mul_DcoeffKT`, `hasSum_turanDetKT`, `DcoeffKT_zero`, `turanDetKT_lam_zero`, `turanDetKT_pos` | proven — positivity holds on the quadrant `κ ≥ 1`, `τ ≥ 1`, and no further: the degree-zero coefficient is `2(τ-1)`, so `Δ^{(κ,τ)}` is negative near `λ = 0` throughout `τ_cw < τ < 1` |
| `prop:bessel-sharpness`, sufficiency, and `τ ≥ 1` forced; `eq:Dkappa-tau-Delta` at general `(κ,τ)` | `Sharpness.besselDefectKT_eq`, `bessel_sharpness_pos`, `bessel_schur_matrix_KT_pd`, `exists_bessel_defect_neg_of_lt_one` | proven — the correction term is `4τ/g`, as `eq:Dnu-kt-def` writes it |
| `eq:qn-pn-ratio`, `eq:q1-p1`, `eq:q-ratio-gap` | `WallOrder.n_pRed_lt_two_qRed`, `pRed_one`, `qRed_one`, `qRed_pRed_cross` | proven |
| `thm:two-parameter-coeff`, every `κ ≥ 1` slice as an iff in `τ` | `WallOrder.DcoeffKT_pos_of_gt`, `DcoeffKT_nonneg_of_ge`, `two_parameter_boundary`; `Sharpness.DcoeffKT_degree_one_neg_of_lt`, `DcoeffKT_pos_iff_of_one_le`, `DcoeffKT_nonneg_iff_of_one_le` | proven in both directions — strict positivity of every positive degree holds iff `τ_cw < τ`, nonnegativity iff `τ_cw ≤ τ` |
| `eq:Sm-gamma-ratio` | `Scaling.sweight_eq_gamma_ratio` | proven (Legendre duplication) |
| `eq:c-range` | `Scaling.cCrit_mem` | proven, both ends |
| `eq:alpha-asymptotic` | `Scaling.abs_alpha_sub_three_term_le` | proven, all three terms |
| `eq:beta-asymptotic`, `eq:c-asymptotic` | `Scaling.betacoef_three_term`, `ccoef_three_term`, and their bounds | proven, exactly — both are rational in `m` |
| DLMF §5.11(i), the digamma expansion | `Digamma.digamma_sandwich` | proven with an explicit `x⁻³` remainder |
| `prop:c-monotone` | `CriticalConstant.cCrit_strictAnti_and_range`, `strictAntiOn_cCrit`, `hasDerivAt_cCrit`, `deriv_cCrit_neg`, `tendsto_cCrit_atTop`, `tendsto_cCrit_zero`, `exists_cCrit_eq`; `Tetragamma.trigamma_sq_add_tetragamma_pos`, `hasDerivAt_trigamma` | proven entire — strict antitonicity on `(0,∞)`, both endpoint limits, and surjectivity onto `(3/2,7/2)` |
| `eq:Sm-asymptotic` | `GammaRatio.abs_sweight_div_sub_le`, `abs_gammaRatioFactor_div_rpow_sub_le`, `stirling_diff_sandwich`, `stirlingLam_add`, `abs_shiftRem_sub_le`, `abs_four_shift_sub_le` | proven — a two-sided bound with the threshold and the remainder constant written out, not an `IsBigO` |
| `thm:two-parameter-coeff`, the `κ<1` exclusion at fixed `a` | — | missing (L6) — the paper routes it through `lem:large-argument-limit`.  The `τ` half of the converse is proven above, and the coefficient-level `κ<1` failure at `τ=1`, uniform in `a`, is `Threshold.MDkappa_neg_exists` |
| `thm:coefficientwise`, the fixed-`a` "only if" half | — | missing (L6) — the paper defers it to the necessity part of `thm:two-parameter-coeff`, above, so it rests on the same absence.  Degree one cannot reach it: what `Threshold` proves is the uniform-in-`a` converse (`MDkappa_uniform_iff`), which is strictly weaker |
| `prop:bessel-sharpness`, the single zero on `(0,∞)` for `τ_cw ≤ τ < 1` | `ZeroCount.exists_unique_zero_besselDefectKT`, `exists_unique_zero_turanDetKT`, `strictMonoOn_turanDetKT`, `tendsto_turanDetKT_atTop`, `continuous_turanDetKT_lam`, `two_term_le_turanDetKT`, `DcoeffKT_pos_of_ge_two` | proven — from the coefficient signs alone: a strictly negative constant term, nonnegative coefficients above it, and degree two strictly positive give strict monotonicity and divergence, so the crossing is unique.  Needs no large-argument input |
| `prop:bessel-sharpness`, the least-constant half | — | missing (L6) — needs `lem:large-argument-limit` |
| `lem:large-argument-limit`, the expansion | — | missing (L6) |
| `eq:hypergeom-moments`, the base-law moments `lem:central-moments` consumes | `GammaRatio.hyperWeight_sum`, `hyperWeight_first_moment`, `hyperWeight_second_moment`, `hyperWeight_variance`, `hyperWeight_second_moment_scaled` | proven — the exact variance `n²/(4(2n-1))`, from Chu–Vandermonde.  The fourth and sixth moments are not; they are not needed for the variance and they sit behind the tail bound below |
| `lem:central-moments`, `eq:X2-asymptotic`, `eq:X4-asymptotic`, `eq:tilt-comparison`, `eq:tilted-tail`, and everything downstream: `eq:MD-central-expansion`, `eq:den-central-expansion`, `eq:MD-expectation-two-term`, `eq:den-expectation`, `thm:critical-scaling`, `thm:wall-fan`, `thm:cubic-multicritical`, `cor:wall-orientation`, `cor:eventual-negative-tail`, `rem:jet-transfer-factor` | — | missing (L6) — needs Hoeffding's sampling-without-replacement inequality |
| `lem:continuation` | `trigamma_summable_shift`, `trigamma_succ_of_summable`, `trigamma_recurrences_neg`, `trigamma_pos_neg` | **partial** — the trigamma series continues to negative non-integer `a`; `lem:coefficient-continuation`, which carries each coefficient identity across by the one-variable identity theorem, is not formalized and is in no L-bucket |
| `sec:context`, the closing `Γ`-bound of `subsec:endpoint-sufficiency` | — | out of scope (L4) |

**L1, L2, L3, L5 and L7 are all closed**, and L6 has narrowed from an area to
two missing primitives.  `thm:bessel` and `cor:bessel-matrix` are proved
outright, the corollary's limit clause included; `lem:boundary-positivity` is
proved in full and transported to every `κ ≥ 1`; `cor:bessel-law` is proved with
the Bessel law itself and with the microcanonical fibers and four-copy sectors
underneath it; and `thm:two-parameter-coeff` is an iff in `τ` on every `κ ≥ 1`
slice.  Inside `sec:scaling` the division is sharp: `eq:Sm-gamma-ratio`,
`eq:Sm-asymptotic` with its constants written out, `eq:c-range`, all three
expansions of `subsec:asymptotics-degree-thresholds`, the three-term digamma
sandwich, `prop:c-monotone` entire, and the exact base-law moments of
`eq:hypergeom-moments` are all proved.  What is left is Hoeffding's
sampling-without-replacement inequality and Bessel large-argument asymptotics.
None of the paper's headline results depends on either.  `K_ν` and the
order-derivative asymptotics are also still absent from Mathlib, and nothing in
this paper consumes them: the dictionary went through `I_ν` alone.


## Dependencies

This development depends on modules in the repository-wide `_lean_shared/` tree,
outside the paper's `lean/` directory.

| Component | Used by | Description |
|---|---|---|
| `Vendor.MathlibPR.PR42760.Bessel` | `Hypergeometric`, for `Complex.besselJ` in `besselJ_eq_Zfun` | `J_ν` as `(x/2)^ν · ₀F̃₁(;ν+1;-(x/2)²)`, with its analyticity in the argument.  Vendored from Mathlib pull request #42760, *feat(Analysis/SpecialFunction): bessel function of the first kind*, by Weiyi Wang (GitHub `wwylele`).  Retires when that PR merges and the Mathlib pin is bumped past it |
| `Vendor.MathlibPR.PR42760.RegularizedHypergeometric` | reached transitively, through `Bessel`; `Hypergeometric` names `Complex.regularizedHGFun`, `regularizedHGFunSeries` and `regularizedHGFunCoeff` from it in `ofReal_Zfun` | The generalized hypergeometric function and its regularization, by which `Zfun a` **is** `regularizedHGFun 0 {a}` rather than a private construction.  Upstream file by Moritz Doll.  It is already on Mathlib master but postdates our pin, so it retires on the same pin bump |

## License

Code is made available under the MIT license (see `LICENSE.txt`), or as
otherwise noted in the comments of the file.  The vendored modules under
`_lean_shared/Vendor` are the latter: each keeps its upstream header.

## References

1. D. Karp and Y. Zhang, *Log-concavity and log-convexity of series containing
   multiple Pochhammer symbols*, Fractional Calculus and Applied Analysis **27**
   (2024), 458–486. [doi:10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0)

Refer to the paper for references.
