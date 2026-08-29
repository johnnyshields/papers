/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.LowerCollarSimple
import ForgacsTran.LowerEndpointSimpleZero
import ForgacsTran.PhaseSupplyGeneral

/-!
# `FTBranchSupply` at a SIMPLE smallest zero

`PhaseSupplyGeneral` produces the branch supply from the admissible class alone in the
`ρ ≥ 2`, `r ≥ 2` cell.  Its two `ρ ≥ 2` inputs are both at the arc's **lower** end —
`κ₀`'s collar at the collision and `eq:phase-derivative-bound` on the same region — and both
are `ρ ≥ 2` for one reason: they read the endpoint through
`PhaseSupplyLowerCollar.ft_endpoint_branch_data`, whose value is the cluster expansion's.

At `ρ = 1` the endpoint is a different point, and `LowerCollarSimple` supplies the same
binders there.  This module is the same assembly with those two substituted; the upper-end
inputs carry no `ρ` at all, so nothing else changes.

**The endpoint is exposed.**  `ta` is the branch's own limit at `0⁺`, and the statement
carries that characterization rather than only its existence, so a composition against the
dominance side can identify the two endpoints rather than assume them equal.

Sorry-free.

## Main statements

* `exists_simple_lower_endpoint` — the endpoint, with `E(ta) = 0` and `E'(ta) ≠ 0`.
* `ft_kappaZero_general_rho_one` — `κ₀` where the branch reaches a simple zero of `E`.
* `ft_branchSupply_general_closed_rho_one` — `FTBranchSupply` at `ρ = 1`, with nothing
  assumed.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `subsec:proof`.

## Tags

phase supply, branch supply, simple zero, lower endpoint, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}

/-- **The lower endpoint at a simple smallest zero is a SIMPLE zero of `E`.**
`E = -Σ·Q` where the chords do not vanish, so `E' = -Σ'·Q` at a zero of `Σ`, and both
factors are nonzero: `Σ' > 0` always, and `Q(ta) ≠ 0` because the endpoint sits strictly
inside the first gap.  That is the input every rate in `LowerEndpointRates` asks for. -/
theorem exists_simple_lower_endpoint (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) (hc : 0 < c) :
    ∃ ta : ℝ, 0 < ta ∧ (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0 ∧
      (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval ta ≠ 0 ∧
      Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta) := by
  classical
  have hn : 0 < n := by omega
  obtain ⟨ta, hLi, hgap, hlim, hLe⟩ := exists_lower_endpoint_of_simple hn2 ha hr hmin hsimple hc
  have hta : 0 < ta := lt_trans (ha i) hLi
  have hne : ∀ k, a k - ta ≠ 0 := fun k =>
    sub_ne_zero.2 fun h => lower_endpoint_ne_root_of_simple hLi hgap k h.symm
  have hQ : (ftRootPolyReal c a).eval ta ≠ 0 := by
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc.ne' (Finset.prod_ne_zero_iff.2 fun k _ => hne k)
  have hSig : ftSigmaReal a r ta = 0 := by
    have h := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := r) hne
    rw [hLe] at h
    rcases mul_eq_zero.1 h.symm with h' | h'
    · simpa using h'
    · exact absurd h' hQ
  refine ⟨ta, hta, hLe, ?_, hlim⟩
  rw [eval_derivative_ftCriticalReal_of_ftSigmaReal_eq_zero (c := c) hne hSig]
  exact mul_ne_zero (by simpa using (sum_div_sq_pos hn ha hne).ne') hQ

/-- **`κ₀` where the branch reaches a simple zero of `E` at `0⁺`.**  The lower collar is
`LowerCollarSimple`'s and the outer region at the origin is unchanged: it carries no `ρ`.

What the proof consumes is the trio `hLe`/`hLd`/`hlim`: `ta` is a zero of the critical
polynomial, a simple one, and the branch's limit at `0⁺`.  `ρ = 1` is not among them —
neither `ft_lower_collar_simple` nor `ft_upper_region` takes `_hmin` or `_hsimple`, and the
"simple" in the first names `hLd` rather than the multiplicity of the smallest zero.  Those
two are carried inert so the statement pairs with `exists_simple_lower_endpoint`, which is
where `ρ = 1` does its work: it is what makes such an endpoint exist. -/
theorem ft_kappaZero_general_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) {i : Fin n} (_hmin : ∀ k, a i ≤ a k)
    (_hsimple : ∀ k, k ≠ i → a k ≠ a i) {ta : ℝ} (hta : 0 < ta)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval ta = 0)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval ta ≠ 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta)) :
    ∀ c₀ ∈ Ioo (0 : ℝ) (π / r), ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧
      eVariationOn (ftFixedAngle (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
        (ftTauArc a r (n - 1) ta) (ftArcCofactorDeriv a c r ta) c₀)
        (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal κ₀ := by
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  obtain ⟨b₁, C₁, hb₁, -, -, hlo⟩ :=
    ft_lower_collar_simple (n := n) (r := r) (a := a) (c := c) (L := ta)
      hn ha hr1 (Or.inl hn2) hc.ne' hta hLe hLd hlim
  obtain ⟨b₂, C₃, -, hb₂, hhi⟩ :=
    ft_upper_region (n := n) (r := r) (a := a) (c := c) (x₁ := ta) hn2 ha hc.ne' hr
  exact ft_kappaZero_of_collars (n := n) (r := r) (a := a) (c := c) (x₁ := ta)
    hn ha hc.ne' hr1 (Or.inl hn2) hb₁ hb₂ hlo hhi

/-- **`FTBranchSupply` at a general admissible pencil with `ρ = 1`, with nothing assumed**,
in the `2 ≤ r` cell — the third of the four corners `subsec:proof` walks.

The endpoint is returned with its characterization as the branch's limit at `0⁺`, so a
later composition against the dominance side can identify the two rather than assume it. -/
theorem ft_branchSupply_general_closed_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧ Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ta) ∧
      ∃ κ₀' κ₁' : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧
        ∀ B : Polynomial ℂ, B.eval 0 ≠ 0 →
          FTBranchSupply (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) ta) κ₀' κ₁' := by
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (0 : ℝ) < r := by positivity
  have harc : (0 : ℝ) < π / r := by positivity
  obtain ⟨ta, hta, hLe, hLd, hlim⟩ :=
    exists_simple_lower_endpoint (c := c) hn2 ha hr1 hmin hsimple hc
  refine ⟨ta, hta, hlim, ?_⟩
  have hc₀ : π / (2 * r) ∈ Ioo (0 : ℝ) (π / r) :=
    ⟨by positivity, div_lt_div_of_pos_left Real.pi_pos hrR (by linarith)⟩
  obtain ⟨κ₀, hκ₀, h0⟩ :=
    ft_kappaZero_general_rho_one (c := c) hn2 ha hc hr hmin hsimple hta hLe hLd hlim _ hc₀
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hsupply⟩ :=
    ft_branchSupply_general (x₁ := ta) hn ha hc.ne' hr1 (Or.inl hn2) hc₀ hκ₀ h0
  refine ⟨κ₀', κ₁', hκ₀', hκ₁', fun B hBev => ?_⟩
  have hB0 : B ≠ 0 := fun h0' => hBev (by rw [h0']; simp)
  obtain ⟨d₁, C₁, hd₁0, hd₁, hlo⟩ :=
    ft_region_lower_simple (n := n) (r := r) (a := a) (c := c) (L := ta)
      B hB0 hn ha hr1 (Or.inl hn2) hc.ne' hta hLe hLd hlim
  obtain ⟨d₂, C₃, hd₂0, hd₂, hhi⟩ :=
    ft_region_upper (n := n) (r := r) (a := a) (c := c) (x₁ := ta) B hBev hn2 ha hc.ne' hr
  have hb₁0 : 0 < min d₁ d₂ := lt_min hd₁0 hd₂0
  have hb₂lt : max d₁ d₂ < π / r := max_lt hd₁ hd₂
  have hmidsub : Icc (min d₁ d₂) (max d₁ d₂) ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨lt_of_lt_of_le hb₁0 hθ.1, lt_of_le_of_lt hθ.2 hb₂lt⟩
  obtain ⟨C₂, hmid⟩ :=
    ft_region_mid (n := n) (r := r) (a := a) (c := c) (x₁ := ta)
      B hB0 hn2 ha hc.ne' hr1 hmidsub
  exact hsupply B hB0 (min d₁ d₂) (max d₁ d₂) C₁ C₂ C₃
    (fun s hs _ => hlo s ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩)
    hmid
    (fun s hs => hhi s ⟨le_trans (le_max_right _ _) hs.1, hs.2⟩)
    (ft_rootStates_general (c := c) (z := ftBranchZLower a c r (n - 1))
      hn ha hr1 (Or.inl hn2)
      (fun θ hθ => ftTauArc_agree a r (n - 1) ta hθ.1 hθ.2))

end ForgacsTran
