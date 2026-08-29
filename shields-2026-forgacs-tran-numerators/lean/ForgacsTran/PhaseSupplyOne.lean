/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PhaseSupplyGeneral
import ForgacsTran.UpperCollarOne

/-!
# `FTBranchSupply` at `r = 1`

`PhaseSupplyGeneral` produces the branch supply from the admissible class alone in the
`ρ ≥ 2`, `r ≥ 2` cell.  Its two `r ≥ 2` inputs are the outer estimates at the arc's upper
end — `κ₀`'s collar there and `eq:phase-derivative-bound` on the same region — and both are
`r ≥ 2` for the same reason: the branch runs into the **origin**, where `E(0) = -rQ(0) ≠ 0`
and neither `E` nor `B` degenerates.

At `r = 1` the arc ends at `π` and the principal pair collides at `-L`, so both estimates
are collision estimates instead.  `UpperCollarOne` produces them, and this module is the
same assembly with those two substituted; every other group is already stated at `1 ≤ r`.

**The weight's condition is weaker here.**  `ft_branchSupply_general_closed` asks
`B(0) ≠ 0`, which `ft_region_upper` needs because the branch reaches the origin.  At `r = 1`
it does not, and `ft_region_upper_one` reads `B`'s multiplicity at the collision off the
polynomial instead — so the corner below asks only that `B` be nonzero.

Sorry-free.

## Main statements

* `ft_kappaZero_general_one` — `κ₀` at `r = 1`, with nothing assumed.
* `ft_branchSupply_general_closed_one` — `FTBranchSupply` at `r = 1`, with nothing assumed.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `subsec:proof`.

## Tags

phase supply, branch supply, upper endpoint, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

variable {n ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **`κ₀` at a general admissible pencil with `r = 1`, with nothing assumed.**  The three
regions of `ft_kappaZero_of_collars` meet here as they do at `2 ≤ r`, but both outer ones
are collisions: `ft_lower_collar` at `θ = 0` and `ft_upper_region_one` at `θ = π`. -/
theorem ft_kappaZero_general_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∀ c₀ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧
      eVariationOn (ftFixedAngle (ftRootPoly c a) 1 (ftBranchZLower a c 1 (n - 1))
        (ftTauArc a 1 (n - 1) x₁) (ftArcCofactorDeriv a c 1 x₁) c₀)
        (Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ))) ≤ ENNReal.ofReal κ₀ := by
  have hn : 0 < n := by omega
  obtain ⟨b₁, C₁, hb₁, -, -, hlo⟩ :=
    ft_lower_collar (n := n) (r := 1) (ρ := ρ) (a := a) (c := c) (x₁ := x₁)
      hn2 ha hc.ne' le_rfl hx₁ hmin hcard hρ
  obtain ⟨b₂, C₃, -, hb₂, hhi⟩ :=
    ft_upper_region_one (n := n) (a := a) (c := c) (x₁ := x₁) hn2 ha hc
  exact ft_kappaZero_of_collars (n := n) (r := 1) (a := a) (c := c) (x₁ := x₁)
    hn ha hc.ne' le_rfl (Or.inl hn2) hb₁ hb₂ hlo hhi

/-- **`FTBranchSupply` at a general admissible pencil with `r = 1`, with nothing assumed.**

This is `PhaseSupplyGeneral.ft_branchSupply_general_closed` at the second of the four
corners `subsec:proof` walks.  The two constants are bound before the weight, which is
`thm:main` clause 3, and the weight's only condition is that it be nonzero — weaker than the
`B(0) ≠ 0` the `r ≥ 2` corner needs, because the branch does not reach the origin here.

The three cut points are reconciled exactly as at `2 ≤ r`: each region producer returns its
own width, `min` and `max` order the two outer ones, and both bounds survive the shrink
because each is stated on a set the shrink only makes smaller. -/
theorem ft_branchSupply_general_closed_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ κ₀' κ₁' : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧
      ∀ B : Polynomial ℂ, B ≠ 0 →
        FTBranchSupply (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
          (ftTauArc a 1 (n - 1) x₁) κ₀' κ₁' := by
  have hn : 0 < n := by omega
  have hπ := Real.pi_pos
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  have hrR : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
  have harc : (0 : ℝ) < π / ((1 : ℕ) : ℝ) := by positivity
  have hc₀ : π / (2 * ((1 : ℕ) : ℝ)) ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) :=
    ⟨by positivity, div_lt_div_of_pos_left Real.pi_pos hrR (by norm_num)⟩
  obtain ⟨κ₀, hκ₀, h0⟩ :=
    ft_kappaZero_general_one (ρ := ρ) (c := c) hn2 ha hc hx₁ hmin hcard hρ _ hc₀
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hsupply⟩ :=
    ft_branchSupply_general (x₁ := x₁) hn ha hc.ne' le_rfl (Or.inl hn2) hc₀ hκ₀ h0
  refine ⟨κ₀', κ₁', hκ₀', hκ₁', fun B hB0 => ?_⟩
  obtain ⟨d₁, C₁, hd₁0, hd₁, hlo⟩ :=
    ft_region_lower (n := n) (r := 1) (ρ := ρ) (a := a) (c := c) (x₁ := x₁)
      B hB0 hn2 ha hc.ne' le_rfl hx₁ hmin hcard hρ
  obtain ⟨d₂, C₃, hd₂0, hd₂, hhi⟩ :=
    ft_region_upper_one (n := n) (a := a) (c := c) (x₁ := x₁) B hB0 hn2 ha hc
  have hb₁0 : 0 < min d₁ d₂ := lt_min hd₁0 hd₂0
  have hb₂lt : max d₁ d₂ < π / ((1 : ℕ) : ℝ) := max_lt hd₁ hd₂
  have hmidsub : Icc (min d₁ d₂) (max d₁ d₂) ⊆ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) :=
    fun θ hθ => ⟨lt_of_lt_of_le hb₁0 hθ.1, lt_of_le_of_lt hθ.2 hb₂lt⟩
  obtain ⟨C₂, hmid⟩ :=
    ft_region_mid (n := n) (r := 1) (a := a) (c := c) (x₁ := x₁)
      B hB0 hn2 ha hc.ne' le_rfl hmidsub
  exact hsupply B hB0 (min d₁ d₂) (max d₁ d₂) C₁ C₂ C₃
    (fun s hs _ => hlo s ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩)
    hmid
    (fun s hs => hhi s ⟨le_trans (le_max_right _ _) hs.1, hs.2⟩)
    (ft_rootStates_general (c := c) (z := ftBranchZLower a c 1 (n - 1))
      hn ha le_rfl (Or.inl hn2)
      (fun θ hθ => ftTauArc_agree a 1 (n - 1) x₁ hθ.1 hθ.2))

/-- **`FTPhaseSupply` at a general admissible pencil with `r = 1`, with nothing assumed**, in
the `ρ ≥ 2` cell.

This is the seam at the second corner: `ft_branchSupply_general_closed_one` produces
`hbranch` and `DominanceSupplyClosure.exists_ftPhaseSupply_at_branch_one_of_branchSupply`
consumes it against the dominance chain, which was already closed there.

`3 ≤ n` is the `(deg Q, r) ≠ (2, 1)` exclusion the dominance side carries: at `n = 2` and
`r = 1` the radius is constant, the separation results the argument runs on exclude it, and
`rem:quadratic-case` reaches a sharper bound by quasi-orthogonality instead. -/
theorem ft_ftPhaseSupply_general_one {B : Polynomial ℂ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hB : HasRealCoeffs B) (hBev : B.eval 0 ≠ 0) :
    ∃ κ₀' κ₁' hcol : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧ 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
        (ftTauArc a 1 (n - 1) x₁) hcol κ₀' κ₁' M := by
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hbranch⟩ :=
    ft_branchSupply_general_closed_one (ρ := ρ) (x₁ := x₁) (c := c)
      (by omega) ha hc hx₁ hmin hcard hρ
  obtain ⟨hcol, hhcol, hs⟩ :=
    exists_ftPhaseSupply_at_branch_one_of_branchSupply (κ₀ := κ₀') (κ₁ := κ₁')
      hn3 ha hc hx₁ hmin hcard hρ B hB hBev (hbranch B hB0)
  exact ⟨κ₀', κ₁', hcol, hκ₀', hκ₁', hhcol, hs⟩

end ForgacsTran
