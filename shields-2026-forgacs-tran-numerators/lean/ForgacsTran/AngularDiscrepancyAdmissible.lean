/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.AngularDiscrepancyFT
import ForgacsTran.CompositionLinks
import ForgacsTran.CompositionLinksRhoOne
import ForgacsTran.PhaseSupplyUniform

/-!
# `prop:angular-discrepancy` at an admissible pencil, with nothing assumed

`AngularDiscrepancyFT.ftAngularDiscrepancy_of_supply` reaches
`ConsequencesComposition.FTAngularDiscrepancy` from a phase supply whose three constants
stand ahead of the weight, and `PhaseSupplyUniform` produces exactly that.  The four
theorems below run the one into the other, so the discrepancy becomes a statement about the
pencil rather than about a supply somebody has to hand it.

**What this adds over the interior count.**  `ClauseThreeAdmissible` proves the whole-arc
case: `α = 0`, `β = π/r`, one window.  `eq:angular-discrepancy` is the statement **uniform
in `0 ≤ α < β ≤ π/r`** — every sub-window of the viewing arc carries its share of the zeros
to within `C_0 + C_1\deg B_N`, at constants that see neither the window nor the weight.
That is the half of `prop:angular-discrepancy` the pencil had not been given.

The binder order is the same claim it is everywhere else in this file's neighborhood:
`C_0` and `C_1` are inside `FTAngularDiscrepancy` ahead of `∀ B`, `M₀` after it, and `α`,
`β` last of all, so one threshold serves every window at a given weight.

**Downstream.**  `ConsequencesComposition.ft_equidistribution_of_discrepancy` and
`ft_angular_clock_of_discrepancy` consume `FTAngularDiscrepancy` and nothing else besides
`1 ≤ r`, so `prop:equidistribution` and `cor:angular-rigidity` follow at the pencil from any
of these by a single application.

Sorry-free.

## Main statements

* `ftAngularDiscrepancy_admissible` — `ρ ≥ 2`, `2 ≤ r`.
* `ftAngularDiscrepancy_admissible_one` — `ρ ≥ 2`, `r = 1`.
* `ftAngularDiscrepancy_admissible_rho_one` — `ρ = 1`, `2 ≤ r`; the branch endpoint is
  produced by the pencil, so it is bound in the conclusion.
* `ftAngularDiscrepancy_admissible_rho_one_one` — `ρ = 1`, `r = 1`.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `prop:angular-discrepancy`,
`eq:angular-discrepancy`, `subsec:proof`, `thm:FT-geometry`.

## Tags

angular discrepancy, admissible pencil, uniformity, window
-/

namespace ForgacsTran

open Polynomial Set Real

variable {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **`eq:angular-discrepancy` at an admissible pencil with `2 ≤ r` and a repeated smallest
zero.**  Every window of the viewing arc carries its uniform share of the zeros of `F_M` to
within `C_0 + C_1\deg B`, with both constants fixed by the pencil. -/
theorem ftAngularDiscrepancy_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    FTAngularDiscrepancy (ftRootPoly c a) r (ftBranchZLower a c r (n - 1)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  exact ftAngularDiscrepancy_of_supply
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
    (ft_ftPhaseSupply_uniform (ρ := ρ) (x₁ := x₁) hn2 ha hc hr hx₁ hmin hcard hρ)

/-- **`eq:angular-discrepancy` at `r = 1`, repeated smallest zero.**  `3 ≤ n` is the
`(deg Q, r) ≠ (2,1)` exclusion the `r = 1` dominance corner carries. -/
theorem ftAngularDiscrepancy_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    FTAngularDiscrepancy (ftRootPoly c a) 1 (ftBranchZLower a c 1 (n - 1)) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  exact ftAngularDiscrepancy_of_supply
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
    (ft_ftPhaseSupply_uniform_one (ρ := ρ) (x₁ := x₁) hn3 ha hc hx₁ hmin hcard hρ)

/-- **`eq:angular-discrepancy` at a SIMPLE smallest zero, `2 ≤ r`.**  The branch's lower
endpoint is a critical point inside the first gap, produced by the pencil, so it is bound in
the conclusion beside the discrepancy rather than named by a hypothesis. -/
theorem ftAngularDiscrepancy_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      FTAngularDiscrepancy (ftRootPoly c a) r
        (ftBranchZLowerAt a c r (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ r)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_rho_one hn2 ha hc hr hmin hsim
  exact ⟨ta, hta, ftAngularDiscrepancy_of_supply
    (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLowerAt_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
    ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩⟩

/-- **`eq:angular-discrepancy` at a SIMPLE smallest zero, `r = 1`** — the last of the four
corners. -/
theorem ftAngularDiscrepancy_admissible_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      FTAngularDiscrepancy (ftRootPoly c a) 1
        (ftBranchZLowerAt a c 1 (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  obtain ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁, hs⟩ :=
    ft_ftPhaseSupply_uniform_rho_one_one hn3 ha hc hmin hsim
  exact ⟨ta, hta, ftAngularDiscrepancy_of_supply
    (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLowerAt_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
    ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩⟩

end ForgacsTran
