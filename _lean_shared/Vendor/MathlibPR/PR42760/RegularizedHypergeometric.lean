/-
Vendored from Mathlib pull request #42760, `feat(Analysis/SpecialFunction): bessel function of
the first kind`, by Weiyi Wang (GitHub `wwylele`).  The hypergeometric file it builds on is by
Moritz Doll; both upstream copyright lines are reproduced verbatim below.

  https://github.com/leanprover-community/mathlib4/pull/42760

Licence: Apache 2.0, as granted by Mathlib.  Retirement: the PR is OPEN as of 2026-08-24; when it
merges and the Mathlib pin is bumped past it, delete this directory and drop the `Vendor` lib's
import.  `Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean` is ALREADY on Mathlib
master (from an earlier PR) but postdates our pin; `Bessel.lean` is what #42760 itself adds.

WHY IT IS HERE.  `Complex.regularizedHGFun`, notated `F₀₁(a)`, is the paper's `Z`:
`Z(a,λ) = ₀F₁(;a;λ)/Γ(a)` is by definition the regularized `₀F₁`, and the coefficient identity
`regularizedHGFunCoeff 0 {a} n = 1/(n! * Γ(a+n))` closes by `simp`, matching `Zseries.zterm`
term for term.  Mind the index: upstream's local notation is `F₀₁(a) := regularizedHGFun 0 {a+1}`,
so `besselJ ν x = (x/2)^ν * regularizedHGFun 0 {ν+1} (-(x/2)^2)` and it is `J_{a-1}`, not `J_a`,
whose hypergeometric factor is `Z(a,·)`:  `J_{a-1}(x) = (x/2)^{a-1} Z(a, -(x/2)^2)`, which at
`x = 2√λ` is `eq:I-Z` with the sign of the argument flipped.  Both identifications are proved in
`TuranBessel.Hypergeometric` (`ofReal_Zfun`, `besselJ_eq_Zfun`).  Note what this does NOT give:
analyticity here is in the ARGUMENT only, so the parameter calculus that `turanDetCoeff_eq`
needs -- differentiating `1/Γ(a+k)` in `a` under the sum -- is still absent, as is every
polygamma beyond `digamma`.  See `../../../../_papers_done/turan-bessel/lean/README.md` § L2, L3.

SCALE.  2 files, 628 lines, 56 declarations (44 + 12).

SORRY / AXIOM / BUNDLE SCAN.  No `sorry`, no `axiom`, no `native_decide`, and no hypothesis-bundle
`structure` or `class`: every binder is an ordinary hypothesis or a standard Mathlib typeclass.
Transitive footprint of the headline declarations, checked with `#print axioms`, is
`[propext, Classical.choice, Quot.sound]` for `regularizedHGFun`, `analyticAt_regularizedHGFun_zero`,
`besselJ`, `analyticAt_besselJ`, `ordinaryHypergeometric_div_Gamma_eq`, and for both backported
declarations below.

BUILDS CLEAN at our pin (`leanprover/lean4:v4.30.0-rc2`, Mathlib `07de3072`) after the adaptations
listed below -- `lake build Vendor.MathlibPR.PR42760.Bessel`, no errors and no warnings.

NAMESPACE HYGIENE.  Upstream namespaces kept (`Complex`, `FormalMultilinearSeries`), so consuming
code is written exactly as it will be against a merged Mathlib.  Clash probe against the 2131
declaration names in `TuranBessel` and `_lean_shared/Shields`: no collisions among the 56 names
here.  Nothing else in `Vendor` defines these.

OVERLAP.  None with what we already carry.  `TuranBessel.Trigamma` builds `ψ₁` from scratch and is
untouched by this: Mathlib carries `digamma` only, and this PR adds no polygamma.

ADAPTATIONS TO THE PIN.  Every one is marked `ADAPTED TO PIN` at its site.  All are proof-local;
no statement was weakened or changed, and nothing upstream proves was dropped except where noted.

  1. `Gamma_add_nat_div_Gamma_eq` and `FormalMultilinearSeries.const_smul_sum_apply` are consumed
     by the file but postdate our pin, so they are BACKPORTED into the section below, from Mathlib
     master `cf65d43b4f` (2026-08-24) -- `Gamma/Beta.lean` and `Analytic/ConvergenceRadius.lean`
     respectively, upstream names and namespaces kept so they vanish on a pin bump.  Neither name
     exists at our pin, so neither shadows anything.  `Gamma_add_nat_div_Gamma_eq` is reproved:
     upstream closes both induction branches with `grind`, which does not carry them here, so it
     runs through `Gamma_add_one` and `ascPochhammer_succ_right` instead.
  2. `convert!` does not exist before `v4.33.0-rc1`; `analyticOnNhd_regularizedHGFun_of_card_le`
     uses `simpa ... using` instead.
  3. `fun_prop` does not recognize `AnalyticOnNhd` at this revision, so the four `@[fun_prop]`
     attributes on `AnalyticOnNhd` results are dropped and the proofs that relied on them --
     `analyticAt_besselJ`, `analyticAt_besselJ_int` -- write their compositions out.  PR #42570's
     tag file, already vendored here, would supply the missing tags but does not itself compile at
     this pin (it was vendored against the siblings' `v4.33.0-rc1`).
  4. Four `grind` calls exceed `grind` at this revision and are reproved: two needed
     `Gamma_ne_zero` in usable form (`regularizedHGFunCoeff_eq_zero_iff` rewrites `Gamma z = 0`
     to `∃ m : ℕ, z = -m` first; `Gamma_inv_mul_ordinaryHypergeometricSeries_eq` is handed
     `Gamma c ≠ 0`), one is `Gamma_add_one` at `j + n`, and the `zpow` bookkeeping in
     `multiset_prod_div_multiset_prod_mul` is done by hand.
  5. `multiset_prod_eq_pow_mul_multiset_prod` and `multiset_prod_div_multiset_prod_mul` are
     reproved: upstream relies on `field_simp` discharging `(↑n : ℂ) ≠ 0` from `hn : n ≠ 0`, which
     it does not do here, so the cast-nonvanishing is supplied explicitly.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-! # Generalized hypergeometric function

In this file we define the generalized hypergeometric function as well as the Gaussian
hypergeometric function.

The hypergeometric function is a function with parameters `a : Fin p → ℂ` and `b : Fin q → ℂ`.

Note that in this file, we use the *regularized* version of the hypergeometric function, that is
the coefficients are divides by `∏ i, Gamma (b i)`, giving in the case of the Gaussian
hypergeometric function the series representation
$$\sum_j \frac{(a)^n (b)^n}{\Gamma(c + n) n!} z^ n,$$
where `(a)^n` denotes the rising Pochhammer symbol.

This definition is valid for all values of `c`, whereas the usual hypergeometric function has a
pole for `c = -k` and `k : ℕ`. To our knowledge the regularized hypergeometric function only appears
in the literature only for the Gaussian case, it is implicit in the definition of the Bessel
function (`p = 0` and `q = 1`).
To recover the usual hypergeometric function, simply multiply by `∏ i, Gamma (b i)`.

## Definitions
For the general case we have
* `Complex.regularizedHGFunCoeff`: the coefficients
* `Complex.regularizedHGFunSeries`: the formal multilinear series
* `Complex.regularizedHGFun`: the function

For the Gaussian case (`p = 2` and `q = 1`), we define
* `Complex.regularizedGaussHGFunSeries`: the formal multilinear series
* `Complex.regularizedGaussHGFun`: the function

## Results

Convergence:
* `radius_regularizedHGFunSeries_eq_top_of_finite`: in the case that the series reduces to a
  polynomial, the radius of convergence is infinite.
* `radius_regularizedHGFunSeries_eq_top`: if `p < q + 1`, then the series has infinite convergence
  radius.
* `radius_regularizedHGFunSeries_eq_one`: if `p = q + 1`, then the series has convergence radius
  `1`.
* `Complex.radius_regularizedGaussHGFunSeries_eq_one`: the Gaussian hypergeometric series has
  convergence radius `1`.

-/

@[expose] public noncomputable section

/-! ### Backported from Mathlib master

Two declarations the PR consumes that postdate the pinned revision, copied from
Mathlib master `cf65d43b4f` (2026-08-24) with their upstream names and namespaces
so they vanish cleanly when the pin is bumped:

* `FormalMultilinearSeries.const_smul_sum_apply` --- `Mathlib/Analysis/Analytic/ConvergenceRadius.lean`
* `Complex.Gamma_add_nat_div_Gamma_eq` --- `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`
-/

namespace FormalMultilinearSeries

variable {ku : Type*} [NontriviallyNormedField ku]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ku E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ku F]
  {ku' : Type*} [DivisionSemiring ku'] [Module ku' F] [ContinuousConstSMul ku' F]
  [SMulCommClass ku ku' F]

theorem const_smul_sum_apply [T2Space F] (c : ku') (f : FormalMultilinearSeries ku E F) (z : E) :
    c • f.sum z = (c • f).sum z := by
  unfold FormalMultilinearSeries.sum
  simp [tsum_const_smul'']

end FormalMultilinearSeries

namespace Complex

/-- The ascending Pochhammer symbol is given by the ratio of `Γ` functions. -/
theorem Gamma_add_nat_div_Gamma_eq {n : ℕ} (z : ℂ) (hz : ∀ k : ℕ, z ≠ -k) :
    Gamma (z + n) / Gamma z = (ascPochhammer ℂ n).eval z := by
  -- ADAPTED TO PIN: upstream discharges both branches with `grind`; reproved here
  -- from `Gamma_add_one` and `ascPochhammer_succ_right`.  Statement is upstream's.
  induction n generalizing z with
  | zero => simp [div_self (Gamma_ne_zero hz)]
  | succ n ih =>
    have hzn : z + (n : ℂ) ≠ 0 := fun h => hz n (by linear_combination h)
    have hstep : Gamma (z + ((n : ℕ) + 1 : ℕ)) = (z + n) * Gamma (z + n) := by
      push_cast
      rw [← add_assoc, Gamma_add_one _ hzn]
    rw [hstep, ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast, ← ih z hz]
    ring

end Complex

namespace Complex

open scoped Nat Real
open Topology Filter

variable {p q : ℕ}

variable {a : Multiset ℂ} {b : Multiset ℂ} {n m : ℕ} {j k : ℂ}

/-- The coefficients of the regularized hypergeometric series. -/
def regularizedHGFunCoeff (a : Multiset ℂ) (b : Multiset ℂ) (n : ℕ) : ℂ :=
  (a.map (ascPochhammer ℂ n).eval).prod / (n ! * (b.map (Gamma <| · + n)).prod)

attribute [grind .] Nat.factorial_ne_zero

@[grind =]
theorem regularizedHGFunCoeff_eq_zero_iff :
    regularizedHGFunCoeff a b n = 0 ↔
    (∃ j ∈ a, ∃ k < n, j = -k) ∨ ∃ j ∈ b, ∃ (m : ℕ), j + n = -m := by
  -- ADAPTED TO PIN: `grind` cannot move between `Gamma z = 0` and `∃ m : ℕ, z = -m`
  -- at this revision, so that equivalence is proved first and rewritten in, leaving
  -- `grind` a purely arithmetic goal.
  have gamma_zero_iff : ∀ z : ℂ, Gamma z = 0 ↔ ∃ m : ℕ, z = -m := by
    intro z
    constructor
    · intro hz
      by_contra hcon
      simp only [not_exists] at hcon
      exact Gamma_ne_zero hcon hz
    · rintro ⟨m, rfl⟩
      exact Gamma_neg_nat_eq_zero m
  unfold regularizedHGFunCoeff
  simp [gamma_zero_iff]
  grind

variable (a b n m) in
theorem regularizedHGFunCoeff_eq_zero_right (hb : -(n : ℂ) - m ∈ b := by grind) :
    regularizedHGFunCoeff a b n = 0 := by grind

variable (a b n m) in
theorem regularizedHGFunCoeff_eq_zero_left (ha : -(m : ℂ) ∈ a := by grind)
    (hm : m < n := by grind) :
  regularizedHGFunCoeff a b n = 0 := by grind

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one (hb : ∀ k ∈ b, k ≠ -n) :
    regularizedHGFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n *
      ((a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod  * (n + 1))) := calc
  _ = (a.map fun i ↦ ((ascPochhammer ℂ n).eval i) * (i + n)).prod /
      (n ! * (n + 1) * (b.map fun j ↦ Gamma (j + n) * (j + n)).prod) := by
    unfold regularizedHGFunCoeff
    congrm ((a.map ?_).prod / (?_ * Multiset.prod ?_))
    · ext j
      simp [ascPochhammer_succ_right]
    · rw [Nat.factorial_succ]
      grind
    · refine Multiset.map_congr rfl (fun j hj ↦ ?_)
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
      -- ADAPTED TO PIN: upstream closes this with `grind`; it is `Gamma_add_one`
      -- at `j + n`, whose nonvanishing is exactly the hypothesis `hb`.
      rw [Gamma_add_one _ (fun hz => hb j hj (by linear_combination hz)), mul_comm]
  _ = _ := by
    unfold regularizedHGFunCoeff
    simp_rw [div_mul_div_comm, Multiset.prod_map_mul]
    ring

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one_div_self (h : regularizedHGFunCoeff a b n ≠ 0) :
    regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n =
      (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) := by
  by_cases! hb : ∀ k ∈ b, k ≠ -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (b.map (· + (n : ℂ))).prod = 0 := by
      grind [Multiset.prod_eq_zero, Multiset.mem_map]
    simp [regularizedHGFunCoeff_eq_zero_right a b n 0, h₁]

@[simp]
theorem regularizedHGFunCoeff_zero_neg_nat_add_one (n i : ℕ) :
    regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) = regularizedHGFunCoeff 0 {(n : ℂ) + 1} i := by
  simp [regularizedHGFunCoeff, ← Gamma_nat_eq_factorial]
  ring_nf

-- ADAPTED TO PIN: both helpers reproved.  Upstream leans on `field_simp` discharging
-- `(↑n : ℂ) ≠ 0` from `hn : n ≠ 0` and on `grind` for the zpow bookkeeping; neither
-- happens at this revision, so the cast-nonzeroness is supplied explicitly and the
-- `zpow` split is done by hand.  Both statements are upstream's, unchanged.
private theorem multiset_prod_eq_pow_mul_multiset_prod (a : Multiset ℂ) (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod = n ^ a.card * (a.map (· / (n : ℂ) + 1)).prod := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc (a.map (· + (n : ℂ))).prod
      = (a.map (fun j ↦ (n : ℂ) * (j / (n : ℂ) + 1))).prod := by
        refine congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => ?_)
        field_simp
    _ = _ := by simp [Multiset.prod_map_mul]

private
theorem multiset_prod_div_multiset_prod_mul (a : Multiset ℂ) (b : Multiset ℂ) (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) =
      n ^ (a.card - (b.card : ℤ) - 1) * (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [multiset_prod_eq_pow_mul_multiset_prod a hn, multiset_prod_eq_pow_mul_multiset_prod b hn]
  have hz : ((n : ℂ)) ^ (a.card - (b.card : ℤ) - 1)
      = (n : ℂ) ^ (a.card : ℕ) / ((n : ℂ) ^ (b.card : ℕ) * (n : ℂ)) := by
    rw [zpow_sub₀ hn', zpow_sub₀ hn', zpow_one, zpow_natCast, zpow_natCast]
    ring
  have e1 : ((n : ℂ) + 1) = (n : ℂ) * (1 + (n : ℂ)⁻¹) := by field_simp
  have hb : ((n : ℂ) ^ (b.card : ℕ)) ≠ 0 := pow_ne_zero _ hn'
  rw [hz, e1]
  field_simp

variable (a b) in
/-- The regularized hypergeometric series. -/
def regularizedHGFunSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (regularizedHGFunCoeff a b)

@[simp]
theorem regularizedHGFunSeries_coeff :
    (regularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b := by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]
theorem regularizedHGFunSeries_eq_zero :
    regularizedHGFunSeries a b n = 0 ↔ regularizedHGFunCoeff a b n = 0 := by
  apply FormalMultilinearSeries.ofScalars_eq_zero

variable (a b) in
/-- The regularized hypergeometric function. -/
def regularizedHGFun (z : ℂ) : ℂ := (regularizedHGFunSeries a b).sum z

@[simp]
theorem regularizedHGFun_zero : regularizedHGFun a b 0 = regularizedHGFunCoeff a b 0 := by
  rw [regularizedHGFun, regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalarsSum]
  simp

/-- If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric series is finite
and has convergence radius `∞`. -/
theorem radius_regularizedHGFunSeries_eq_top_of_finite (ha : j ∈ a) (hj : j = -n) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use n + 1
  grind

variable (b) in
/-- If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeometric series
are eventually non-vanishing. -/
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero (h : ∀ j ∈ a, ∀ (k : ℕ), j ≠ -↑k) :
    ∀ᶠ (n : ℕ) in atTop, regularizedHGFunCoeff a b n ≠ 0 := by
  rw [Filter.eventually_atTop]
  use b.toFinset.sup (⌈-re ·⌉₊) + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, hj, m, h'⟩)
  · grind
  · suffices (m : ℝ) < 0 by grind
    suffices -j.re < n by
      have h : j = -m - n := by grind
      simpa [h] using this
    calc
      -j.re ≤ ⌈-j.re⌉₊ := Nat.le_ceil (-j.re)
      _ ≤ b.toFinset.sup (⌈-re ·⌉₊) := mod_cast Finset.le_sup (by grind) (f := (⌈-re ·⌉₊))
      _ < n := by norm_cast

variable (a) in
private theorem tendsto_multiset_prod_div_add_one :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod) atTop (𝓝 1) := by
  suffices ∀ i ∈ a, Tendsto (fun n : ℕ ↦ (i / n + 1)) atTop (𝓝 <| (fun _ : _ ↦ 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

variable (a b) in
private theorem tendsto_multiset_prod_div_multiset_prod_mul :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_multiset_prod_div_add_one a).div
    ((tendsto_multiset_prod_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- If `a.card ≤ b.card`, then the hypergeometric series has infinite convergence radius. -/
@[grind =]
theorem radius_regularizedHGFunSeries_eq_top (h : a.card ≤ b.card) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  by_cases! ha : ∃ j ∈ a, ∃ k : ℕ, j = -k
  · obtain ⟨j, hj, k, ha⟩ := ha
    apply radius_regularizedHGFunSeries_eq_top_of_finite hj ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  · simp only [Nat.succ_eq_add_one]
    have h₁ : Tendsto (fun (n : ℕ) ↦ (n : ℂ) ^ (a.card - (b.card : ℤ) - 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ)).pow (b.card + 1 - a.card)
      rw [zero_pow (by grind)] at this
      apply this.congr
      intro n
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg, Int.ofNat_sub (by grind),
        Int.natCast_add_one]
      ring_nf
    have := (h₁.mul (tendsto_multiset_prod_div_multiset_prod_mul a b)).norm
    simp only [mul_one, norm_zero] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    rw [← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b hn₂, mul_div]

@[simp]
theorem radius_regularizedHGFunSeries_zero_eq_top : (regularizedHGFunSeries 0 b).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top (by simp)

theorem analyticOnNhd_regularizedHGFun_of_card_le (h : a.card ≤ b.card) :
    AnalyticOnNhd ℂ (regularizedHGFun a b) .univ := by
  -- ADAPTED TO PIN: upstream uses `convert!`, which arrives after this revision.
  have hr := (regularizedHGFunSeries a b).analyticOnNhd
  simpa [radius_regularizedHGFunSeries_eq_top h] using hr

theorem analyticAt_regularizedHGFun_of_card_le (h : a.card ≤ b.card) (z : ℂ) :
    AnalyticAt ℂ (regularizedHGFun a b) z :=
  analyticOnNhd_regularizedHGFun_of_card_le h z (by simp)

-- ADAPTED TO PIN: `@[fun_prop]` dropped; `fun_prop` does not recognize `AnalyticOnNhd`
-- at this revision, and PR #42570's tag file (vendored here for the siblings' newer
-- pin) does not compile at this one either.  The theorem itself is unchanged.
theorem analyticOnNhd_regularizedHGFun_zero : AnalyticOnNhd ℂ (regularizedHGFun 0 b) .univ :=
  analyticOnNhd_regularizedHGFun_of_card_le (by simp)

-- ADAPTED TO PIN: `@[fun_prop]` dropped, as above.
theorem analyticAt_regularizedHGFun_zero (z : ℂ) : AnalyticAt ℂ (regularizedHGFun 0 b) z :=
  analyticAt_regularizedHGFun_of_card_le (by simp) z

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius `1`, unless it
is a polynomial. -/
@[grind =]
theorem radius_regularizedHGFunSeries_eq_one (h : a.card = b.card + 1)
    (h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k) :
    (regularizedHGFunSeries a b).radius = 1 := by
  have : Tendsto (fun n ↦ ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (tendsto_multiset_prod_div_multiset_prod_mul a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b h'
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    simp [Nat.succ_eq_add_one, ← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b hn₂, h]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) ℂ _ (by simp) this
  simpa

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius greater or equal
to `1`. -/
theorem radius_regularizedHGFunSeries_ge_one (h : a.card = b.card + 1) :
    1 ≤ (regularizedHGFunSeries a b).radius := by
  by_cases! h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k
  · grind
  · obtain ⟨j, hj, k, h'⟩ := h'
    rw [radius_regularizedHGFunSeries_eq_top_of_finite hj h']
    simp

theorem analyticOnNhd_regularizedHGFun_of_card_eq_add_one (h : a.card = b.card + 1) :
    AnalyticOnNhd ℂ (regularizedHGFun a b) (Metric.eball 0 1) := by
  apply (regularizedHGFunSeries a b).analyticOnNhd.mono
  exact Metric.eball_subset_eball (radius_regularizedHGFunSeries_ge_one h)

theorem analyticAt_regularizedHGFun_of_card_eq_add_one (h : a.card = b.card + 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (regularizedHGFun a b) z := by
  apply (analyticOnNhd_regularizedHGFun_of_card_eq_add_one h)
  rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]

theorem regularizedHGFun_zero_singleton_neg_nat_add_one (n : ℕ) (z : ℂ) :
    regularizedHGFun 0 {-(n : ℂ) + 1} z = z ^ n * regularizedHGFun 0 {(n : ℂ) + 1} z := by
  unfold regularizedHGFun FormalMultilinearSeries.sum
  conv_lhs =>
    rw [← ((regularizedHGFunSeries 0 {-(n : ℂ) + 1}).summable (by simp)).sum_add_tsum_nat_add n]
  suffices ∑ i ∈ Finset.range n, z ^ i * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} i +
      ∑' i, z ^ (i + n) * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) =
      z ^ n * ∑' i, z ^ i * regularizedHGFunCoeff 0 {(n : ℂ) + 1} i by simpa
  calc
    _ = 0 + ∑' i, z ^ (i + n) * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) := by
      congrm $(Finset.sum_eq_zero fun i hi ↦ mul_eq_zero_of_right _ ?_) + _
      refine regularizedHGFunCoeff_eq_zero_right _ _ _ (n - i - 1) ?_
      rw [Multiset.mem_singleton]
      norm_cast
      grind
    _ = z ^ n * ∑' i, z ^ i * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) := by
      simp_rw [zero_add, ← tsum_mul_left]
      congr with i
      ring
    _ = _ := by simp

section ZeroZero

/-- The regularized hypergeometric series with `a = b = 0` is exponential series. -/
@[simp, grind =]
theorem regularizedHGFunSeries_zero_zero :
    regularizedHGFunSeries 0 0 = NormedSpace.expSeries ℂ ℂ := by
  ext n
  simp [regularizedHGFunCoeff, NormedSpace.expSeries]

/-- The regularized hypergeometric function `₀F₀` is the complex exponential. -/
@[simp, grind =]
theorem regularizedHGFun_zero_zero : regularizedHGFun 0 0 = exp := by
  rw [exp_eq_exp_ℂ, NormedSpace.exp_eq_expSeries_sum (𝕂 := ℂ)]
  unfold regularizedHGFun
  simp

end ZeroZero

section Gaussian

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFunSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  regularizedHGFunSeries {a, b} {c}

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFun (a b c z : ℂ) : ℂ :=
  (regularizedGaussHGFunSeries a b c).sum z

variable {a b c z : ℂ}

variable (a b c) in
theorem regularizedGaussHGFunSeries_symm :
    regularizedGaussHGFunSeries a b c = regularizedGaussHGFunSeries b a c := by
  unfold regularizedGaussHGFunSeries
  rw [Multiset.pair_comm]

variable (a b c) in
theorem regularizedGaussHGFun_symm :
    regularizedGaussHGFun a b c = regularizedGaussHGFun b a c := by
  unfold regularizedGaussHGFun
  rw [regularizedGaussHGFunSeries_symm]

theorem coeff_regularizedGaussHGFunSeries :
    (a.regularizedGaussHGFunSeries b c).coeff n =
    ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) / (n ! * Gamma (c + n)) := by
  simp [regularizedGaussHGFunSeries, regularizedHGFunCoeff]

theorem Gamma_inv_mul_ordinaryHypergeometricSeries_eq (hc : ∀ k : ℕ, c ≠ -k) {n : ℕ} :
    (Gamma c)⁻¹ * (ordinaryHypergeometricSeries ℂ a b c).coeff n =
      (a.regularizedGaussHGFunSeries b c).coeff n := by
  rw [coeff_regularizedGaussHGFunSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.coeff_ofScalars, ordinaryHypergeometricCoefficient,
    ← Gamma_add_nat_div_Gamma_eq c hc]
  -- ADAPTED TO PIN: `Gamma c ≠ 0` has to be handed to `grind` explicitly here.
  have hc0 : Gamma c ≠ 0 := Gamma_ne_zero hc
  grind

theorem ordinaryHypergeometric_div_Gamma_eq (hc : ∀ k : ℕ, c ≠ -k) :
    ordinaryHypergeometric a b c z / Gamma c = regularizedGaussHGFun a b c z := by
  rw [regularizedGaussHGFun, ordinaryHypergeometric, div_eq_inv_mul, ← smul_eq_mul,
    FormalMultilinearSeries.const_smul_sum_apply]
  congr
  ext n
  simp [Gamma_inv_mul_ordinaryHypergeometricSeries_eq hc]

variable (b c) in
@[simp]
theorem radius_regularizedGaussHGFunSeries_eq_top_of_left (k : ℕ) :
    (regularizedGaussHGFunSeries (-k) b c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (a c) in
@[simp]
theorem radius_regularizedGaussHGFunSeries_eq_top_of_right (k : ℕ) :
    (regularizedGaussHGFunSeries a (-k) c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (c) in
@[grind =]
theorem radius_regularizedGaussHGFunSeries_eq_one (h : ∀ k : ℕ, a ≠ -k ∧ b ≠ -k) :
    (regularizedGaussHGFunSeries a b c).radius = 1 :=
  radius_regularizedHGFunSeries_eq_one rfl (by simp; grind)

variable (a b c) in
theorem radius_regularizedGaussHGFunSeries_ge_one :
    1 ≤ (regularizedGaussHGFunSeries a b c).radius :=
  radius_regularizedHGFunSeries_ge_one rfl

end Gaussian

end Complex
