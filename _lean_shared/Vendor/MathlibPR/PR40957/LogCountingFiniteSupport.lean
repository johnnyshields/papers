/-
Vendored from Mathlib pull request #40957, `feat: characterize mermorphic functions with finite set
of poles in terms of logarithmic counting function`, by Stefan Kebekus (GitHub `kebekus`).

  https://github.com/leanprover-community/mathlib4/pull/40957

The pull request is merged upstream but lands after the Mathlib revision pinned by this repository.
It adds the declarations below to `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/
Asymptotic.lean` and to `Mathlib/Topology/LocallyFinsupp.lean`; only those declarations are copied
here, keeping upstream's namespaces, names and
statements, so consuming code is written exactly as it will be against a merged Mathlib.  The Lean
4.34 module-system syntax (`module`, `public import`, `public section`) is dropped, which the pinned
toolchain does not parse.

One proof is adapted to the pinned revision, where `Asymptotics.IsBigO.sum` still concludes about
`fun x ↦ ∑ i ∈ s, A i x` rather than the `Finset` sum of functions the same pull request moves it
to: the sum is put in that form with `Finset.sum_fn` before the lemma is applied.

When the Mathlib pin is bumped past the merge, delete this file and import the upstream module.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic

open Asymptotics Filter Function Real Set

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E]

/--
The logarithmic counting function of a singleton is big-O of `log`. This is the qualitative
consequence of `logCounting_single_eq_log_sub_const`.
-/
lemma logCounting_single_isBigO_log [DecidableEq E] [ProperSpace E] {e : E} {n : ℤ} :
    logCounting (single e n) =O[atTop] Real.log := by
  have h₁ : logCounting (single e n) =ᶠ[atTop] (n * log · - n * log ‖e‖) := by
    filter_upwards [eventually_ge_atTop ‖e‖] with r hr
    rw [logCounting_single_eq_log_sub_const hr]
    ring
  have hb : (n * log ·) =O[atTop] Real.log := isBigO_const_mul_self (n : ℝ) log atTop
  exact (hb.sub isLittleO_const_log_atTop.isBigO).congr' h₁.symm EventuallyEq.rfl

/--
Represent a function (of locally finite support) that in fact has finite support as a `finsum` of
singleton indicator functions.
-/
@[simp] lemma sum_apply_smul_single_eq_self_on_univ [DecidableEq E] {D : locallyFinsupp E ℤ}
    (h : D.support.Finite) :
    ∑ z ∈ h.toFinset, single z (D z) = D := by
  ext w
  simp only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
  set s := h.toFinset with hs
  by_cases hw : w ∈ s
  · simp [hw]
  · simp only [hw, if_false]
    have : w ∉ support D := by simpa only [hs, Set.Finite.mem_toFinset] using hw
    exact (notMem_support.mp this).symm

/--
A function with finite support has a logarithmic counting function that is big-O of `log`.
-/
lemma logCounting_isBigO_log_of_finite_support [ProperSpace E] {D : locallyFinsupp E ℤ}
    (h : D.support.Finite) :
    logCounting D =O[atTop] Real.log := by
  classical
  rw [← sum_apply_smul_single_eq_self_on_univ h, map_sum, Finset.sum_fn]
  exact Asymptotics.IsBigO.sum fun _ _ ↦ logCounting_single_isBigO_log

/--
A non-negative function whose logarithmic counting function is big-O of `log` has finite support.
-/
lemma finite_support_of_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) (hO : logCounting D =O[atTop] Real.log) :
    D.support.Finite := by
  classical
  -- Let (N : ℕ) be a number such that ‖logCounting D x‖ ≤ N * ‖log x‖
  obtain ⟨C, hC⟩ := isBigO_iff.1 hO
  obtain ⟨N, hCN⟩ := exists_nat_gt (max C 0)
  have hCN' : C < N := lt_of_le_of_lt (le_max_left C 0) hCN
  -- Argue by contradiction, let t be a cardinality=N finite subset in the (infinite) support of D
  -- and let D' be the divisor for the indicator function of t
  by_contra! hInf
  obtain ⟨t, htsub, htcard⟩ := hInf.exists_subset_card_eq N
  set D' := ∑ z ∈ t, single z (1 : ℤ) with hD'
  -- The auxiliary divisor `D'` is bounded above by `D`.
  have hle : D' ≤ D := by
    rw [le_def, Pi.le_def]
    intro w
    simp only [hD', coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
    by_cases hw : w ∈ t
    · simp only [hw, ite_true]
      have h₁ : D w ≠ 0 := mem_support.mp (htsub (Finset.mem_coe.2 hw))
      have h₂ : (0 : ℤ) ≤ D w := by simpa using (le_def.1 h) w
      omega
    · simpa [hw, ite_false] using (le_def.1 h) w
  -- A uniform bound on the norms of points in `t`.
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ z ∈ t, ‖z‖ ≤ R₀ := t.finite_toSet.isBounded.exists_norm_le
  set K := ∑ z ∈ t, log ‖z‖ with hK
  -- Eventually, `logCounting D' = N * log - K`.
  have hEq : ∀ᶠ r in atTop, logCounting D' r = (N : ℝ) * log r - K := by
    filter_upwards [eventually_ge_atTop R₀] with r hr using calc
      logCounting D' r = ∑ c ∈ t, logCounting (single c 1) r := by simp [hD']
       _ = ∑ z ∈ t, (log r - log ‖z‖) := by
        congr! 1 with z hz;
        simpa using logCounting_single_eq_log_sub_const (e := z) (n := 1) ((hR₀ z hz).trans hr)
       _ = (N : ℝ) * log r - K := by simp [Finset.sum_sub_distrib, hK, htcard]
  -- Combine the bounds into a contradiction with `log → ∞`.
  have hFinal : ∀ᶠ r in atTop, ((N : ℝ) - C) * log r ≤ K := by
    filter_upwards [hEq, eventually_ge_atTop (1 : ℝ), hC] with r hr₁ hr₂ hr₃
    grind [logCounting_le hle hr₂, norm_eq_abs, abs_of_nonneg, log_nonneg, logCounting_nonneg]
  have hTendsto : Tendsto (fun r ↦ ((N : ℝ) - C) * log r) atTop atTop :=
    tendsto_log_atTop.const_mul_atTop (sub_pos.mpr hCN')
  obtain ⟨r, hr₁, hr₂⟩ := (hFinal.and (hTendsto.eventually_gt_atTop K)).exists
  linarith

/--
A non-negative function with locally finite support has finite support if and only if its
logarithmic counting function is big-O of `log`.
-/
theorem finite_support_iff_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) :
    D.support.Finite ↔ logCounting D =O[atTop] Real.log :=
  ⟨logCounting_isBigO_log_of_finite_support, finite_support_of_logCounting_isBigO_log h⟩

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
A meromorphic function has a finite set of poles if and only if the logarithmic counting function
for its pole-divisor is big-O of `log`.
-/
theorem logCounting_isBigO_log_iff_finite_support {f : 𝕜 → E} :
    logCounting f ⊤ =O[atTop] Real.log ↔ (MeromorphicOn.divisor f univ)⁻.support.Finite := by
  rw [logCounting_top]
  exact (locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log (negPart_nonneg _)).symm

end ValueDistribution
