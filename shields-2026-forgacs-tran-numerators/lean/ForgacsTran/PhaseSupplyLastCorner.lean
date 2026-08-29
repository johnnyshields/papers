/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PhaseSupplyOne
import ForgacsTran.PhaseSupplyRhoOne

/-!
# `FTBranchSupply` at `ρ = 1`, `r = 1` — the last corner

The two endpoint replacements are independent of each other's parameter, which is what makes
this corner an assembly rather than a fifth argument: `UpperCollarOne`'s producers carry no
`ρ` — the `r = 1` upper endpoint is a collision of the principal pair with itself and the
smallest zero's multiplicity is not in it — and `LowerCollarSimple`'s hold at every
`1 ≤ r`, since the reduced equation is stated at every `r`.

So the four corners are covered by two producers each, drawn from a pool of four:
`ft_lower_collar`/`ft_region_lower` at `ρ ≥ 2`, `ft_lower_collar_simple`/
`ft_region_lower_simple` at `ρ = 1`, `ft_upper_region`/`ft_region_upper` at `2 ≤ r`, and
`ft_upper_region_one`/`ft_region_upper_one` at `r = 1`.  Every other group in the assembly is
stated at `1 ≤ r` with no `ρ`, so the four corners differ in exactly those two slots.

Sorry-free.

## Main statements

* `ft_kappaZero_general_rho_one_one` — `κ₀` at `r = 1`, at a simple zero of `E`.
* `ft_branchSupply_general_closed_rho_one_one` — `FTBranchSupply` there.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `subsec:proof`.

## Tags

phase supply, branch supply, corner grid, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n : ℕ} {a : Fin n → ℝ} {c : ℝ}

/-- **`κ₀` at `r = 1`, where the branch reaches a simple zero of `E` at `0⁺`.**  Both outer
regions are collisions: a simple zero of `E` inside the first gap at `θ = 0`, and the
principal pair meeting at `-L` at `θ = π`.

As at the general-`r` corner the content is the trio `hLe`/`hLd`/`hlim`, and `_hmin` and
`_hsimple` are inert: `ρ = 1` is what makes such an endpoint exist rather than anything this
proof consumes.  They are carried so the statement pairs with
`exists_simple_lower_endpoint`. -/
theorem ft_kappaZero_general_rho_one_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (_hmin : ∀ k, a i ≤ a k) (_hsimple : ∀ k, k ≠ i → a k ≠ a i)
    {ta : ℝ} (hta : 0 < ta)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) 1).eval ta = 0)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) 1)).eval ta ≠ 0)
    (hlim : Tendsto (ftTau a 1 (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta)) :
    ∀ c₀ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧
      eVariationOn (ftFixedAngle (ftRootPoly c a) 1 (ftBranchZLower a c 1 (n - 1))
        (ftTauArc a 1 (n - 1) ta) (ftArcCofactorDeriv a c 1 ta) c₀)
        (Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ))) ≤ ENNReal.ofReal κ₀ := by
  have hn : 0 < n := by omega
  obtain ⟨b₁, C₁, hb₁, -, -, hlo⟩ :=
    ft_lower_collar_simple (n := n) (r := 1) (a := a) (c := c) (L := ta)
      hn ha le_rfl (Or.inl hn2) hc.ne' hta hLe hLd hlim
  obtain ⟨b₂, C₃, -, hb₂, hhi⟩ :=
    ft_upper_region_one (n := n) (a := a) (c := c) (x₁ := ta) hn2 ha hc
  exact ft_kappaZero_of_collars (n := n) (r := 1) (a := a) (c := c) (x₁ := ta)
    hn ha hc.ne' le_rfl (Or.inl hn2) hb₁ hb₂ hlo hhi

/-- **`FTBranchSupply` at `ρ = 1`, `r = 1`, with nothing assumed** — the last of the four
corners.  As at the other `r = 1` corner, the weight's only condition is that it be nonzero:
the branch does not reach the origin, so `B(0) ≠ 0` is not needed on the branch side.

The endpoint is returned with its characterization as the branch's limit at `0⁺`. -/
theorem ft_branchSupply_general_closed_rho_one_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧ Tendsto (ftTau a 1 (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta) ∧
      ∃ κ₀' κ₁' : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧
        ∀ B : Polynomial ℂ, B ≠ 0 →
          FTBranchSupply (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
            (ftTauArc a 1 (n - 1) ta) κ₀' κ₁' := by
  have hn : 0 < n := by omega
  have hrR : (0 : ℝ) < ((1 : ℕ) : ℝ) := by norm_num
  have harc : (0 : ℝ) < π / ((1 : ℕ) : ℝ) := by positivity
  obtain ⟨ta, hta, hLe, hLd, hlim⟩ :=
    exists_simple_lower_endpoint (c := c) (r := 1) hn2 ha le_rfl hmin hsimple hc
  refine ⟨ta, hta, hlim, ?_⟩
  have hc₀ : π / (2 * ((1 : ℕ) : ℝ)) ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) :=
    ⟨by positivity, div_lt_div_of_pos_left Real.pi_pos hrR (by norm_num)⟩
  obtain ⟨κ₀, hκ₀, h0⟩ :=
    ft_kappaZero_general_rho_one_one (c := c) hn2 ha hc hmin hsimple hta hLe hLd hlim _ hc₀
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hsupply⟩ :=
    ft_branchSupply_general (x₁ := ta) hn ha hc.ne' le_rfl (Or.inl hn2) hc₀ hκ₀ h0
  refine ⟨κ₀', κ₁', hκ₀', hκ₁', fun B hB0 => ?_⟩
  obtain ⟨d₁, C₁, hd₁0, hd₁, hlo⟩ :=
    ft_region_lower_simple (n := n) (r := 1) (a := a) (c := c) (L := ta)
      B hB0 hn ha le_rfl (Or.inl hn2) hc.ne' hta hLe hLd hlim
  obtain ⟨d₂, C₃, hd₂0, hd₂, hhi⟩ :=
    ft_region_upper_one (n := n) (a := a) (c := c) (x₁ := ta) B hB0 hn2 ha hc
  have hb₁0 : 0 < min d₁ d₂ := lt_min hd₁0 hd₂0
  have hb₂lt : max d₁ d₂ < π / ((1 : ℕ) : ℝ) := max_lt hd₁ hd₂
  have hmidsub : Icc (min d₁ d₂) (max d₁ d₂) ⊆ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) :=
    fun θ hθ => ⟨lt_of_lt_of_le hb₁0 hθ.1, lt_of_le_of_lt hθ.2 hb₂lt⟩
  obtain ⟨C₂, hmid⟩ :=
    ft_region_mid (n := n) (r := 1) (a := a) (c := c) (x₁ := ta)
      B hB0 hn2 ha hc.ne' le_rfl hmidsub
  exact hsupply B hB0 (min d₁ d₂) (max d₁ d₂) C₁ C₂ C₃
    (fun s hs _ => hlo s ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩)
    hmid
    (fun s hs => hhi s ⟨le_trans (le_max_right _ _) hs.1, hs.2⟩)
    (ft_rootStates_general (c := c) (z := ftBranchZLower a c 1 (n - 1))
      hn ha le_rfl (Or.inl hn2)
      (fun θ hθ => ftTauArc_agree a 1 (n - 1) ta hθ.1 hθ.2))

end ForgacsTran
