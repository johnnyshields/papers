/-
Vendored from Mathlib pull request #42760, `feat(Analysis/SpecialFunction): bessel function of
the first kind`, by Weiyi Wang (GitHub `wwylele`).  The hypergeometric file it extends is by
Moritz Doll; both upstream copyright lines are reproduced verbatim below.

  https://github.com/leanprover-community/mathlib4/pull/42760

Licence: Apache 2.0, as granted by Mathlib.  Retirement: the PR merged upstream as `db00fb3901`
(2026-09-15), after the `v4.34.x` branch point, so it is absent from our pin
(`leanprover/lean4:v4.34.1`, Mathlib `v4.34.1` = `d13f23b7`).  When the pin moves past
`db00fb3901`, delete this directory and import `Mathlib.Analysis.SpecialFunctions.Bessel`.

WHAT IS HERE.  `Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean` is at our pin;
this file carries only the ten declarations #42760 adds to it, verbatim and in upstream order:
`regularizedHGFunCoeff_zero_neg_nat_add_one`, `regularizedHGFun_zero`,
`radius_regularizedHGFunSeries_zero_eq_top`, the `analyticOnNhd`/`analyticAt` pairs for
`card_le`, `zero` and `card_eq_add_one`, and `regularizedHGFun_zero_singleton_neg_nat_add_one`.
`Bessel.lean` in this directory is the PR's new module.

WHY IT IS HERE.  `Complex.regularizedHGFun`, notated `F₀₁(a)`, is the paper's `Z`:
`Z(a,λ) = ₀F₁(;a;λ)/Γ(a)` is by definition the regularized `₀F₁`, and the coefficient identity
`regularizedHGFunCoeff 0 {a} n = 1/(n! * Γ(a+n))` closes by `simp`, matching `Zseries.zterm`
term for term.  Mind the index: upstream's local notation is `F₀₁(a) := regularizedHGFun 0 {a}`,
and `besselJ ν x = (x/2)^ν * F₀₁(ν+1) (-(x/2)^2)`, so it is `J_{a-1}`, not `J_a`,
whose hypergeometric factor is `Z(a,·)`:  `J_{a-1}(x) = (x/2)^{a-1} Z(a, -(x/2)^2)`, which at
`x = 2√λ` is `eq:I-Z` with the sign of the argument flipped.  Both identifications are proved in
`TuranBessel.Hypergeometric` (`ofReal_Zfun`, `besselJ_eq_Zfun`).  Note what this does NOT give:
analyticity here is in the ARGUMENT only, so the parameter calculus that `turanDetCoeff_eq`
needs -- differentiating `1/Γ(a+k)` in `a` under the sum -- is still absent, as is every
polygamma beyond `digamma`.  See `../../../../_papers_done/turan-bessel/lean/README.md` § L2, L3.

SORRY / AXIOM / BUNDLE SCAN.  No `sorry`, no `axiom`, no `native_decide`, and no hypothesis-bundle
`structure` or `class`.

NAMESPACE HYGIENE.  Upstream namespace `Complex` and upstream names kept, so consuming code is
written exactly as it will be against a merged Mathlib.

ADAPTATIONS TO THE PIN.  None: the hunks compile at the pin as written.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-! # Generalized hypergeometric function: additions from #42760 -/

@[expose] public noncomputable section

namespace Complex

open Filter

open scoped Nat Real Topology

variable {p q : ℕ}

variable {a : Multiset ℂ} {b : Multiset ℂ} {n m : ℕ} {j k : ℂ}

@[simp]
theorem regularizedHGFunCoeff_zero_neg_nat_add_one (n i : ℕ) :
    regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) = regularizedHGFunCoeff 0 {(n : ℂ) + 1} i := by
  simp [regularizedHGFunCoeff, ← Gamma_nat_eq_factorial]
  grind

@[simp]
theorem regularizedHGFun_zero : regularizedHGFun a b 0 = regularizedHGFunCoeff a b 0 := by
  rw [regularizedHGFun, regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalarsSum]
  simp

@[simp]
theorem radius_regularizedHGFunSeries_zero_eq_top : (regularizedHGFunSeries 0 b).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top (by simp)

theorem analyticOnNhd_regularizedHGFun_of_card_le (h : a.card ≤ b.card) :
    AnalyticOnNhd ℂ (regularizedHGFun a b) .univ := by
  convert! (regularizedHGFunSeries a b).analyticOnNhd
  simp [radius_regularizedHGFunSeries_eq_top h]

theorem analyticAt_regularizedHGFun_of_card_le (h : a.card ≤ b.card) (z : ℂ) :
    AnalyticAt ℂ (regularizedHGFun a b) z :=
  analyticOnNhd_regularizedHGFun_of_card_le h z (by simp)

@[fun_prop]
theorem analyticOnNhd_regularizedHGFun_zero : AnalyticOnNhd ℂ (regularizedHGFun 0 b) .univ :=
  analyticOnNhd_regularizedHGFun_of_card_le (by simp)

@[fun_prop]
theorem analyticAt_regularizedHGFun_zero (z : ℂ) : AnalyticAt ℂ (regularizedHGFun 0 b) z :=
  analyticAt_regularizedHGFun_of_card_le (by simp) z

theorem analyticOnNhd_regularizedHGFun_of_card_eq_add_one (h : a.card = b.card + 1) :
    AnalyticOnNhd ℂ (regularizedHGFun a b) (Metric.eball 0 1) := by
  apply (regularizedHGFunSeries a b).analyticOnNhd.mono
  exact Metric.eball_subset_eball (radius_regularizedHGFunSeries_ge_one h)

theorem analyticAt_regularizedHGFun_of_card_eq_add_one (h : a.card = b.card + 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (regularizedHGFun a b) z := by
  apply analyticOnNhd_regularizedHGFun_of_card_eq_add_one h
  rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]

theorem regularizedHGFun_zero_singleton_neg_nat_add_one (n : ℕ) (z : ℂ) :
    regularizedHGFun 0 {-(n : ℂ) + 1} z = z ^ n * regularizedHGFun 0 {(n : ℂ) + 1} z :=
  calc
    _ = ∑ i ∈ Finset.range n, z ^ i * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} i +
        ∑' i, z ^ (i + n) * regularizedHGFunCoeff 0 {-(n : ℂ) + 1} (i + n) := by
      rw [regularizedHGFun, FormalMultilinearSeries.sum,
        ← ((regularizedHGFunSeries 0 {-(n : ℂ) + 1}).summable (by simp)).sum_add_tsum_nat_add n]
      simp
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
    _ = _ := by
      simp [regularizedHGFun, FormalMultilinearSeries.sum]

end Complex
