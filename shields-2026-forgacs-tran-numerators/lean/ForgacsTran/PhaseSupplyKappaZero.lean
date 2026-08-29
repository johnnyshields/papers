/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PhaseSupplyCofactor

/-!
# `κ₀` at the general pencil, reduced to the two endpoint collars

`PhaseSupplyGeneral`'s last weight-free hypothesis is `h0`, the variation of the fixed
factor's branch over the arc.  `BranchSupply.exists_kappaZero_of_cover` reduces it to a
bound on `|Im((∂_tD)'/∂_tD)|` over three regions, and at the general pencil **the middle
one is free**: the cofactor group makes the ratio continuous on the open arc, and a closed
sub-interval of it is compact.

So what `h0` costs at a general pencil is the two **collars**, and nothing else.  This
module states that reduction, so the remaining gap is one named statement per endpoint
rather than a variation bound over the whole arc.

**The cut points are the caller's.**  `exists_bound_im_logDeriv_ftCofactorAlong_of_cover`
takes `b₁` and `b₂` as data, and each collar theorem *returns* the width it is valid on, so
a caller assembles the three regions at whatever cuts the two collars hand it rather than
choosing them in advance.

Sorry-free.

## Main statements

* `ft_kappaZero_mid` — the middle region, from compactness alone.
* `ft_kappaZero_of_collars` — `h0` and its constant, from the two collars.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`,
`cor:linear-phase-variation`, `eq:phase-derivative-bound`.

## Tags

fixed factor, bounded variation, collar, general pencil, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

variable {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **The middle region at the general pencil, from compactness.**  Nothing analytic:
the cofactor group makes `Im((∂_tD)'/∂_tD)` continuous on the open arc, and a closed
sub-interval of it is compact. -/
theorem ft_kappaZero_mid (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {b₁ b₂ : ℝ}
    (hsub : Icc b₁ b₂ ⊆ Ioo (0 : ℝ) (π / r)) :
    ∃ C : ℝ, ∀ θ ∈ Icc b₁ b₂,
      |(ftArcCofactorDeriv a c r x₁ θ
        / ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) x₁) θ).im| ≤ C := by
  obtain ⟨hSd, hSc, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr hnr
  exact exists_bound_im_logDeriv_ftCofactorAlong_mid hSd hSc hS0 hsub

/-- **`h0` at the general pencil, from the two endpoint collars.**  The middle region is
produced here; the two outer ones are the collars, and they are exactly what a general
`κ₀` still costs.

The conclusion is stated at every base point `c₀` of the open arc, since the branch's base
moves the fixed angle by a constant and `eVariationOn` cannot see one. -/
theorem ft_kappaZero_of_collars (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {b₁ b₂ C₁ C₃ : ℝ}
    (hb₁ : 0 < b₁) (hb₂ : b₂ < π / r)
    (hlo : ∀ θ ∈ Ioo (0 : ℝ) b₁,
      |(ftArcCofactorDeriv a c r x₁ θ
        / ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) x₁) θ).im| ≤ C₁)
    (hhi : ∀ θ ∈ Ioo b₂ (π / r),
      |(ftArcCofactorDeriv a c r x₁ θ
        / ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) x₁) θ).im| ≤ C₃) :
    ∀ c₀ ∈ Ioo (0 : ℝ) (π / r), ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧
      eVariationOn (ftFixedAngle (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
        (ftTauArc a r (n - 1) x₁) (ftArcCofactorDeriv a c r x₁) c₀)
        (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal κ₀ := by
  intro c₀ hc₀
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hsub : Icc b₁ b₂ ⊆ Ioo (0 : ℝ) (π / r) := fun θ hθ =>
    ⟨lt_of_lt_of_le hb₁ hθ.1, lt_of_le_of_lt hθ.2 hb₂⟩
  obtain ⟨C₂, hmid⟩ := ft_kappaZero_mid (x₁ := x₁) hn ha hc hr hnr hsub
  obtain ⟨hSd, hSc, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr hnr
  exact exists_kappaZero_of_cover harc.le hSd hSc hS0 hc₀ hlo hmid hhi

end ForgacsTran
