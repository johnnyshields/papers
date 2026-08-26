# Lean 4 formalization — The cubic threshold for coefficientwise log-concavity of multiple-Pochhammer series

Formalizes the core of `shields-2026-cubic-pochhammer.tex` against Mathlib
(`leanprover/lean4:v4.30.0-rc2`, namespace `CubicPochhammer`).  `lake build` is
green with **no `sorry`** and **no project axiom**: every result below rests on
Lean's own `[propext, Classical.choice, Quot.sound]` and nothing else.

The paper proves a statement stronger than Karp–Zhang Conjecture 1 [1]: for a nonnegative log-concave sequence `(f_n)` and
`F_f(μ;x) = Σ_{n≥1} f_n (μ)_{3n} x^n/(3n-1)!`, every coefficient of
`F_f(s/2+d;x)F_f(s/2-d;x)` is nonincreasing in the imbalance `d` over
`0 ≤ d ≤ s/2`, at each fixed parameter sum `s > 0`.  The conjecture —
coefficientwise log-concavity — is the comparison of the imbalances `|α-β|/2`
and `(α+β)/2`.

The proofs in the paper are noncomputational and do not depend on the code here.

## Build

```
lake exe cache get   # fetch the pinned Mathlib build cache (once)
lake build
```

The project is self-contained: its own `lakefile.lean`, `lean-toolchain`, and
pinned `lake-manifest.json`.  (`.lake/` is a gitignored build directory.)

## Result coverage

The table below indicates coverage of the paper's theorems, propositions and
corollaries -- the statements the paper is for, and what the formalization is
measured against.  Every entry marked full is proven unconditionally.

**Work in progress.**  All proofs in the paper are unconditional and
noncomputational.  A row marked below anything but ✅ reflects the state of the
Lean formalization, not of the paper.

**Status.**  ✅ Full · ⚠️ Partial, some clauses carried · ❌ Missing · — not
applicable.

| § | Paper item | Kind | Coverage | Lean (file:line) | Notes |
|---|---|---|---|---|---|
| §1.1 Thm 1.1 | `thm:main` | theorem | ✅ Full | `Main.turan_coeff_nonneg`, `Main.schur_coeff_nonneg` | Proved for an arbitrary symmetric weight family increasing toward the center, which is more general than the paper's `w_k = f_k f_{m-k}`. |
| §2 Prop 2.4 | `prop:kernel-exact` | proposition | ✅ Full | `Bridge.kernel_exact_iff`, `Bridge.cmw_strictAntiOn_imbalance` | Both directions (`kernel_exact_iff`) and the strict clause.  The converse needed no concentration argument: `G_{m,w}` is a polynomial, so the `s → ∞` limit is algebraic. |
| §3 Thm 3.1 | `thm:kernel` | theorem | ✅ Full | `Kernel.gmw_monotoneOn`, `Kernel.gmw_strictMonoOn` | Both clauses, the strict one included. |
| §4 Cor 4.1 | `cor:C-schur` | corollary | ✅ Full | `Bridge.cmw_schur_of_kernel`, `Bridge.cmw_schur_of_kernel_closed` | — |
| §4 Cor 4.2 | `cor:strict` | corollary | ✅ Full | `Bridge.cmf_delta_pos_iff`, `Main.cmf_delta_pos_iff_of_logConcave` | Both halves, plus the Turánian restatement.  `cmf_delta_pos_iff_of_logConcave` gives it at `thm:main`'s own sequence hypothesis rather than the wider degree-local chain. |
| §5 Prop 5.1 | `prop:multiplicity-threshold` | proposition | ✅ Full | `Multiplicity.GeneralOrder.twoTerm_degreeThree`, `Multiplicity.GeneralOrder.twoTerm_degreeThree_neg_iff` | The closed form, the threshold `μ > 4r/(r−3)` for `r ≥ 4`, and both minimality clauses (`degreeTwo_nonneg`, `onePoint_nonneg`). |
| §5 Cor 5.2 | `cor:multiplicity` | corollary | ✅ Full | `Multiplicity.Classification.multiplicity_classification` | `multiplicity_classification`, unconditional.  The `r = 2` case, which the paper cites, is **proven here** as `universalLogConcave_two`, so nothing in the module rests on a cited result. |
| §6.2 Cor 6.1 | `cor:ordinary` | corollary | ✅ Full | `Consequences.cor_ordinary` | All five clauses.  Convergence is taken as a hypothesis rather than the radius formalized; the Γ-ratio needs only a polynomial majorant, not the paper's asymptotic. |
| §6.3 Cor 6.2 | `cor:differential` | corollary | ⚠️ Partial | `Differential.dcoeff_tsum_eq`, `Differential.dcoeff_nonneg`, `Differential.dcoeff_two_pos_iff` | `dcoeff_tsum_eq` identifies `dcoeff` with the `x^m` coefficient of the analytic differential Turánian, by termwise `μ`-differentiation of `eq:F-def`; `dcoeff_nonneg` gives the corollary's nonnegativity clause at every `μ ≥ 0`; `dcoeff_two_pos_iff` closes both directions at `m = 2`, and the vanishing off `I+I` and the `μ = 0` case hold at every `m`.  Missing: strict positivity for `μ > 0` at `m ≥ 3`, reduced in `Differential.lean`'s gap note to the single sequence `f ≡ 1` — it does **not** follow from `thm:main`, which gives only `Φ_m''(0) ≤ 0`, a bound a quartically flat maximum also satisfies.  No Mathlib primitive is missing.  Checked in `../scripts/check_structural.py` and `../scripts/check_differential_coefficients.py`, which show the reduced inequality is true, is not pairwise, and is tight to relative margin `2/(3m)`. |

## Structural coverage

The table below indicates coverage of the paper's lemmas, equations, remarks,
figures and unnumbered prose claims -- the machinery the results above run
through, plus the two subsections that state a claim without a numbered
environment.  Several items are formalized by a **different route** than the
paper's own, and those are marked as such in the notes: the route taken here is
stated and proven, and it reaches the paper's statement, but a reader following
the paper's argument will not find the same intermediate steps.

| § | Paper item | Kind | Coverage | Lean (file:line) | Notes |
|---|---|---|---|---|---|
| §1.1 eq. (1.1) | `eq:general-r` | equation | - | — | Definition fixing notation; its claims are `prop:multiplicity-threshold` and `cor:multiplicity`. |
| §1.1 eq. (1.2) | `eq:F-def` | equation | ✅ Full | `Consequences.aser`, `Consequences.fser` | `aser` is the coefficient `f_n (μ)_{3n}/(3n-1)!` and `fser` the series. |
| §1.1 eq. (1.3) | `eq:schur-def` | equation | ✅ Full | `Consequences.sum_range_aser`, `Main.schur_coeff_nonneg` | Carried coefficientwise, which is the only way the paper asserts anything about it: `sum_range_aser` is the degree-`m` coefficient of the product, unconditionally, and `schur_coeff_nonneg` compares it at the two imbalances.  No formal power series object is formed. |
| §1.1 eq. (1.4) | `eq:Turan-def` | equation | ✅ Full | `Consequences.sum_range_aser`, `Main.turan_coeff_nonneg` | As `eq:schur-def`, in the shift parametrization. |
| §2 Lem 2.1 | `lem:central-products` | lemma | ✅ Full | `CentralProducts.centralProducts_iff` | Both directions. |
| §2 eq. (2.1) | `eq:central-products` | equation | ✅ Full | `CentralProducts.centralProducts_chain` | — |
| §2 Rmk 2.2 | `rem:internal-zeros` | remark | ❌ Missing | — | A concrete witness; nothing blocks it. |
| §2 eq. (2.2) | `eq:C-def` | equation | ✅ Full | `Bridge.cmw` | — |
| §2 eq. (2.3) | `eq:C-beta-binomial` | equation | ❌ Missing | — | Checked in `../scripts/verify_beta_binomial.py`.  The discrete law is bypassed: `aint_eq` goes from `eq:C-def` straight to the beta integral. |
| §2 eq. (2.4) | `eq:C-beta` | equation | ✅ Full | `Bridge.aint_eq` | **Different route.**  Carried with the normalizations cleared rather than as an expectation, so no probability measure appears in the tree. |
| §2 eq. (2.5) | `eq:G-weighted` | equation | ✅ Full | `Kernel.gmw_symm` | — |
| §2 eq. (2.6) | `eq:fixed-sum` | equation | ❌ Missing | — | `kappa_{m,s}` is never formed; the constants cancel inside `aint_eq`.  Checked in `../scripts/check_fixed_sum_schur.py`. |
| §2 Lem 2.3 | `lem:beta-order` | lemma | ✅ Full | `BetaOrder.beta_order`, `BetaOrder.beta_order_strict` | Both clauses.  The strict one, `beta_order_strict`, is at the paper's hypothesis -- `H` strictly increasing on the open `(0,1/2)` and `d₁ < d₂`. |
| §2 eq. (2.7) | `eq:beta-order` | equation | ✅ Full | `BetaOrder.beta_order` | — |
| §2 Rmk 2.5 | `rem:fixed-total` | remark | ⚠️ Partial | `Consequences.sum_range_aser`, `Bridge.cmf_eq_zero_of_not_memSumset`, `Bridge.cmw_pos` | Three of the four claims are carried: `C_{m,w}(u,v) = [x^m]F_f(u;x)F_f(v;x)` (`sum_range_aser`), vanishing off `I+I` (`cmf_eq_zero_of_not_memSumset`), and positivity on `I+I` (`cmw_pos`).  Missing: the conditional law `ℙ_x(N_u=k ∣ N_u+N_v=m)`, which needs a probability measure the tree never names. |
| §3 eq. (3.1) | `eq:w-monotone` | equation | ✅ Full | `Kernel.jmw_nonneg` | Carried as the hypothesis of `jmw_nonneg`. |
| §3.1 eq. (3.2) | `eq:G-J` | equation | ✅ Full | `Kernel.hasDerivAt_gmw_proj` | **Different route.**  Not stated separately; it is `hasDerivAt_gmw_proj` at `w = 1`. |
| §3.1 eq. (3.3) | `eq:J-k` | equation | ✅ Full | `Bernstein.three_jm_monomial` | — |
| §3.1 Lem 3.2 | `lem:bernstein` | lemma | ✅ Full | `Bernstein.jm_pos`, `Snj.snj_nonneg` | — |
| §3.1 eq. (3.4) | `eq:P-def` | equation | ✅ Full | `BernsteinBasis.bernstein_reconstruction` | — |
| §3.1 eq. (3.5) | `eq:P-sum` | equation | ✅ Full | `Bernstein.three_jm_monomial` | — |
| §3.1 eq. (3.6) | `eq:P-coeff` | equation | ✅ Full | `Bernstein.pcoef_transform` | — |
| §3.1 eq. (3.7) | `eq:S-def` | equation | ✅ Full | `Snj.snj` | — |
| §3.1 eq. (3.8) | `eq:S-table` | equation | ✅ Full | `ResidueSums.three_residueSum_closed`, `Snj.three_snj_dform`, `Snj.three_snj_table_zero`–`three_snj_table_five` | **Different route.**  Proven as a period-6 closed form by Pascal induction; no complex root of unity appears anywhere in the tree.  The `three_snj_table_*` family states the display's six printed lines, one per residue class of `j` mod 6. |
| §3.1 eq. (3.9) | `eq:S-R` | equation | ✅ Full | `ResidueSums.moment1_c2` | — |
| §3.1 eq. (3.10) | `eq:exp-bound-1` | equation | ✅ Full | `Snj.expb_quad0` | — |
| §3.1 eq. (3.11) | `eq:exp-bound-0` | equation | ✅ Full | `Snj.expb_quad0` | — |
| §3.2 Lem 3.3 | `lem:weighting` | lemma | ✅ Full | `Weighting.sum_weighted_nonneg`, `Weighting.sum_weighted_pos` | All three parts, both branches of the strict clause. |
| §3.2 eq. (3.12) | `eq:abel-weight` | equation | ✅ Full | `Weighting.sum_weighted_abel` | — |
| §3.2 eq. (3.13) | `eq:J-weighted` | equation | ✅ Full | `Kernel.hasDerivAt_gmw_proj` | — |
| §3.2 eq. (3.14) | `eq:Jw-def` | equation | ✅ Full | `Kernel.jmw_nonneg` | — |
| §3.2 eq. (3.15) | `eq:B-def` | equation | ✅ Full | `Blocks.bblock` | — |
| §3.2 eq. (3.16) | `eq:B-center` | equation | ✅ Full | `Blocks.bblock_center_pos` | — |
| §3.2 Lem 3.4 | `lem:block-sign` | lemma | ✅ Full | `Blocks.block_sign_change` | — |
| §3.2 eq. (3.17) | `eq:H-hyperbolic` | equation | ✅ Full | `Blocks.hgap`, `Blocks.bblock_eq_hgap` | **Different route.**  The sign change is proven rationally rather than hyperbolically; `Real.tanh` never appears. |
| §4 eq. (4.1) | `eq:w-from-f` | equation | ✅ Full | `Bridge.cmf` | — |
| §4 eq. (4.2) | `eq:delta-C` | equation | ✅ Full | `Consequences.sum_range_aser`, `Consequences.fser_mul` | `sum_range_aser` is the coefficient identity, with no convergence hypothesis; `fser_mul` identifies the series product with `∑_m C_{m,f}(u,v)x^m` inside the disc. |
| §4 Rmk 4.3 | `rem:local-weight` | remark | ✅ Full | `Main.turan_coeff_nonneg`, `CentralProducts.centralProducts_iff`, `Bridge.memSumset_iff_of_Icc_support` | All three claims.  `turan_coeff_nonneg`'s hypothesis `hwmono` **is** the remark's degree-local chain, so the degree-`m` conclusion is stated at exactly that condition; `centralProducts_iff` is the global equivalence; `memSumset_iff_of_Icc_support` is `I+I` an interval. |
| §5 eq. (5.1) | `eq:r-central-slope` | equation | ✅ Full | `Multiplicity.CentralSlope.ghat_central_slope_three` | The sign pattern driving the threshold: `+1/2` at `r = 2`, exactly `0` at `r = 3`, negative for every `r ≥ 4`. |
| §5 eq. (5.2) | `eq:r-degree-three` | equation | ✅ Full | `Multiplicity.GeneralOrder.twoTerm_degreeThree` | Closed form for the two-term sequence, via the Pochhammer identity `pochDegreeThree_identity`. |
| §5 Fig 1 | `fig:multiplicity-threshold` | figure | ❌ Missing | — | The curves need nothing, but the caption asserts three numbers: the central value `binom(3r-2,r-1)2^{1-3r}`, the normalized endpoint slope `2r(3-r)`, and the interior maxima at `+6.59%` and `+21.12%` for `r = 4, 5`.  The first two are one step from `dickE_center` and `ghat_central_slope`; the maxima are numerical, and are checked in `../scripts/make_figure_multiplicity.py`. |
| §5.1 | `subsec:first-supercritical-case` | prose | ❌ Missing | — | Two claims: the closed forms of `a_7`, `a_8` in `(1+ξ)^{4m-1}J^{(4)}_m(ξ/(1+ξ))`, and the factorization `J^{(4)}_4(t) = 52t^7(1-t)(7z^4+42z^3+42(z-1)^2+6) > 0` at `z = (1-t)^2/t`.  The tree carries no `r = 4` numerator; both are checked in `../scripts/check_r4_obstruction.py`. |
| §6.1 | `subsec:hypergeometric-specialization` | prose | ❌ Missing | — | The triplication identity `F_f(μ;x) = 3x\,d/dx\,{}_3F_2(μ/3,(μ+1)/3,(μ+2)/3;1/3,2/3;x)` at `f_n ≡ 1`.  Mathlib carries no generalized hypergeometric function; the identity is checked in `../scripts/verify_theorem.py`. |

## Dependencies

None.

## License

Code is made available under the MIT license (see `LICENSE.txt`), or as
otherwise noted in the comments of the file.

## References

1. D. Karp and Y. Zhang, *Log-concavity and log-convexity of series containing
   multiple Pochhammer symbols*, Fractional Calculus and Applied Analysis **27**
   (2024), no. 1, 458–486. [doi:10.1007/s13540-023-00238-0](https://doi.org/10.1007/s13540-023-00238-0)

Refer to the paper for references.
