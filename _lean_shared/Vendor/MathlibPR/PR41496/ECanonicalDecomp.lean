/-
Vendored from Mathlib pull request #41496, `feat: companion lemmas to
`MeromorphicOn.exists_ecanonicalDecomp`, API for the extended canonical decomposition`, by Stefan
Kebekus (GitHub `kebekus`).

  https://github.com/leanprover-community/mathlib4/pull/41496

The PR is merged upstream but postdates the pinned Mathlib revision.  It adds four declarations to
`Mathlib/Analysis/Complex/CanonicalDecomposition.lean` and changes nothing else; those four are
reproduced here verbatim, under their upstream names, in the namespace and `variable` context the
upstream file gives them.

When the pin is bumped past this PR, delete this file and import
`Mathlib.Analysis.Complex.CanonicalDecomposition` alone.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CanonicalDecomposition
-- Adapted to the pinned revision: the `fun_prop` discharges below rely on tags that postdate the
-- pin; `Vendor.MathlibPR.PR42570.FunPropTags` restores them.
import Vendor.MathlibPR.PR42570.FunPropTags

-- Adapted to the pinned revision: this copy imports `Vendor.MathlibPR.PR42570.FunPropTags`, which brings
-- `Complex.log` transitively into scope; inside `namespace Complex` that shadows the `Real.log`
-- an unqualified `log` resolves to upstream, so the occurrences in `log_norm_eq` are qualified.

namespace Complex

open ComplexConjugate Filter Function MeromorphicOn Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}
  {f g : ℂ → E}

private lemma mulSupport_pow_subset_support {α β : Type*} [DivInvMonoid α] (f : β → α)
    (g : β → ℤ) : (fun x ↦ f x ^ g x).mulSupport ⊆ g.support := by
  simp only [mulSupport_subset_iff, ne_eq, mem_support]
  intro
  contrapose!
  simp +contextual

/--
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of the extended canonical
decomposition, write the function `h` entirely in terms of `f`.
-/
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (hw : w ∈ closedBall 0 R) (hR : 0 < R) :
    h w
      = ((∏ᶠ i, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : ℂ) R
  let S₀R := sphere (0 : ℂ) R
  lift (divisor f S₀R).support to Finset ℂ using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset ℂ using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  have := (D.analyticOnNhd w hw).meromorphicAt
  rw [Eq.comm]
  -- Proof body: Substitute `f` using `h₁f` and compute
  calc ((∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt f w
    _ = ((∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ᶠ (i : ℂ), meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ᶠ (u : ℂ), canonicalFactor R u ^ (-(divisor f B₀R) u))
        * ∏ᶠ (v : ℂ), (· - v) ^ (divisor f S₀R) v) • h) w := by
      rw [meromorphicTrailingCoeffAt_congr_nhdsNE
        ((D.meromorphicOn w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (by fun_prop) hw ?η₁ D.eventuallyEq)]
      case η₁ =>
        rw [← closure_ball _ hR.ne']
        exact isOpen_ball.perfect_closure.2
    _ = ((∏ i ∈ t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i ∈ t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • meromorphicTrailingCoeffAt (((∏ i ∈ t₂, canonicalFactor R i ^ (-(divisor f B₀R) i))
        * ∏ i ∈ t₁, (· - i) ^ (divisor f S₀R) i) • h) w := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ = ((∏ i ∈ t₂, meromorphicTrailingCoeffAt (canonicalFactor R i) w ^ (divisor f B₀R) i)
      * ∏ i ∈ t₁, meromorphicTrailingCoeffAt (· - i) w ^ (-divisor f S₀R) i)
      • ((∏ n ∈ t₂, meromorphicTrailingCoeffAt (canonicalFactor R n ^ (-(divisor f B₀R) n)) w)
        * ∏ n ∈ t₁, meromorphicTrailingCoeffAt ((· - n) ^ (divisor f S₀R) n) w)
      • h w := by
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_smul (by fun_prop)
        (D.analyticOnNhd w hw).meromorphicAt,
        MeromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop) (by fun_prop),
        meromorphicTrailingCoeffAt_prod (by fun_prop),
        meromorphicTrailingCoeffAt_prod (by fun_prop),
        (D.analyticOnNhd w hw).meromorphicTrailingCoeffAt_of_ne_zero (D.ne_zero w hw)]
    _ = h w := by
      rw [smul_smul, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        Finset.prod_eq_one ?η₁, Finset.prod_eq_one ?η₂, mul_one, one_smul]
      case η₁ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀,
          add_neg_cancel, zpow_zero]
        apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop)
          (meromorphicOrderAt_canonicalFactor_ne_top x hR)
      case η₂ =>
        intro x hx
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop), ← zpow_add₀,
          locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_add_cancel, zpow_zero]
        rw [meromorphicTrailingCoeffAt_id_sub_const]
        grind

/--
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of the extended canonical
decomposition, write the function `h` entirely in terms of `f`, under the assumption that `f` has
order zero.
-/
lemma ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0) (hR : 0 < R) :
    h w = ((∏ᶠ i, (canonicalFactor R i w) ^ (divisor f (ball 0 R) i))
          * (∏ᶠ i, (w - i) ^ (-divisor f (sphere 0 R)) i))
          • meromorphicTrailingCoeffAt f w := by
  rw [D.eq_smul_meromorphicTrailingCoeffAt h₁w hR]
  congr! 4 with x x
  · by_cases h₃x : (divisor f (ball 0 R)) x = 0
    · simp [h₃x]
    have h₁x : x ∈ ball 0 R := (divisor f (ball 0 R)).supportWithinDomain h₃x
    have h₂x : w ≠ x := by
      rintro rfl
      exact h₃x (by simp [(D.meromorphicOn.mono_set ball_subset_closedBall).divisor_apply h₁x, h₂w])
    rw [AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero
      (Complex.analyticOnNhd_canonicalFactor R x w h₂x)
      (Complex.canonicalFactor_ne_zero h₁x h₁w h₂x)]
  · by_cases h : x = w
    · simp_all [meromorphicTrailingCoeffAt_id_sub_const, divisor_def]
    grind [meromorphicTrailingCoeffAt_id_sub_const]

/--
Companion lemma to `MeromorphicOn.exists_ecanonicalDecomp`: In the setting of the extended canonical
decomposition, write the function `log ‖h‖` entirely in terms of `f`, under the assumption that `f`
has order zero.
-/
lemma ECanonicalDecomp.log_norm_eq
    {f h : ℂ → E} (D : ECanonicalDecomp f h R) (h₁w : w ∈ closedBall 0 R)
    (h₂w : meromorphicOrderAt f w = 0)
    (hR : 0 < R) :
    Real.log ‖h w‖ = ((∑ᶠ i, (divisor f (ball 0 R) i) * Real.log ‖canonicalFactor R i w‖)
          - (∑ᶠ i, (divisor f (sphere 0 R) i) * Real.log ‖w - i‖))
          + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
  -- Finiteness properties and side results used throughout the proof
  let B₀R := ball (0 : ℂ) R
  let S₀R := sphere (0 : ℂ) R
  lift (divisor f S₀R).support to Finset ℂ using divisor_sphere_support_finite with t₁ ht₁
  lift (divisor f B₀R).support to Finset ℂ using D.meromorphicOn.divisor_ball_support_finite
    with t₂ ht₂
  calc Real.log ‖h w‖
    _ = Real.log ‖((∏ᶠ (i : ℂ), canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ᶠ (i : ℂ), (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        h₁w h₂w hR, finprod_eq_prod_of_mulSupport_subset (s := t₂) _ (by aesop)]
    _ = Real.log ‖((∏ i ∈ t₂, canonicalFactor R i w ^ (divisor f B₀R) i)
        * ∏ i ∈ t₁, (w - i) ^ (-divisor f S₀R) i) • meromorphicTrailingCoeffAt f w‖ := by
      rw [finprod_eq_prod_of_mulSupport_subset (s := t₂) _ _,
        finprod_eq_prod_of_mulSupport_subset (s := t₁) _ _]
      <;> simpa [ht₁, ht₂] using mulSupport_pow_subset_support ..
    _ =  ∑ i ∈ t₂, Real.log (‖canonicalFactor R i w‖ ^ (divisor f B₀R) i)
        + ∑ i ∈ t₁, Real.log (‖w - i‖ ^ (-divisor f S₀R) i) + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      have η₀ (x) (hx : x ∈ t₁) : ‖w - x‖ ^ (-divisor f S₀R) x ≠ 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff, sub_ne_zero]
        rintro rfl
        simp_all [divisor_def, ← Finset.mem_coe]
      have η₁ (x) (hx : x ∈ t₂) : ‖canonicalFactor R x w‖ ^ (divisor f B₀R) x ≠ 0 := by
        refine zpow_ne_zero _ ?_
        rw [norm_ne_zero_iff]
        have h₁x : x ∈ ball 0 R := (divisor f B₀R).supportWithinDomain (ht₂ ▸ hx)
        refine canonicalFactor_ne_zero h₁x h₁w fun _ ↦ ?_
        simp_all [divisor_def, ← Finset.mem_coe]
      simp_rw [norm_smul, norm_mul, norm_prod, norm_zpow]
      rw [Real.log_mul (mul_ne_zero_iff.2 ⟨Finset.prod_ne_zero_iff.2 η₁,
          Finset.prod_ne_zero_iff.2 η₀⟩) ?_, Real.log_mul (Finset.prod_ne_zero_iff.2 η₁)
        (Finset.prod_ne_zero_iff.2 η₀), Real.log_prod η₁, Real.log_prod η₀]
      simpa using (D.meromorphicOn w h₁w).meromorphicTrailingCoeffAt_ne_zero (by simp [h₂w])
    _ = ((∑ᶠ i, (divisor f B₀R i) * Real.log ‖canonicalFactor R i w‖)
        - (∑ᶠ i, (divisor f S₀R i) * Real.log ‖w - i‖))
        + Real.log ‖meromorphicTrailingCoeffAt f w‖ := by
      rw [finsum_eq_sum_of_support_subset (s := t₂) _ ?η₀,
        finsum_eq_sum_of_support_subset (s := t₁) _ ?η₁]
      case η₀ | η₁ => intro _ _; simp_all [S₀R, B₀R]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr! 3 with i hi i hi <;> simp
end Complex
