/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchSupplyGeometry
import ForgacsTran.DominanceSupplyClosure
import ForgacsTran.PhaseSupplyCofactor
import ForgacsTran.PhaseSupplyLowerCollar
import ForgacsTran.PhaseSupplyRegionBounds
import ForgacsTran.PhaseSupplyUpperRegion
import ForgacsTran.RootStatesGeneral

/-!
# `FTPhaseSupply` at a general admissible pencil

The cubic composition showed the architecture runs at one pencil.  This is the
same assembly at generality, with the groups that are not yet general left as
explicit hypotheses, so that every seam is crossed once at a general `Q` and `r`.

**In the `ρ ≥ 2`, `r ≥ 2` cell nothing is assumed.**  `ft_ftPhaseSupply_general` below
takes the admissible class and the weight's two conditions and nothing else: the geometry
and curvature groups (`BranchSupplyGeometry`), the cofactor and amplitude groups
(`PhaseSupplyCofactor`), `κ₀` through the two endpoint estimates
(`PhaseSupplyLowerCollar`, `PhaseSupplyUpperRegion`), and `eq:phase-derivative-bound` on
all three regions (`PhaseSupplyRegionBounds`) are each produced rather than assumed.

`ft_branchSupply_general` keeps `κ₀` as a binder because it is stated at `1 ≤ r`, where
the upper endpoint is a collision rather than the origin and the outer estimate is a
different theorem.

Two things about the shape are worth recording, because both were live questions:

* **The endpoint problem does not recur here.**  `exists_uniform_ftBranchSupply`
  now asks for its geometry, cofactor and `κ₀` groups on the **open** arc
  rather than on a neighbourhood of the closed one, so the discontinuity of
  `ftTauArc` at `π/r` — which is what blocked the `r = 1` route — is out of scope
  for every one of them.
* **No `τ`-generalization is needed.**  `BranchSupplyGeometry.ft_geometry_group`
  carries the endpoint value `aEnd` as a parameter, and
  `ftTauArc a r l x₁ = ftTauArcAt a r l x₁ 0`, so instantiating at `aEnd = 0` lands
  exactly on the radius this file's dominance chain is stated at.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `subsec:proof`.

## Tags

phase supply, general pencil, composition, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real

/-- **`hbranch` at a general admissible pencil**, with the `κ₀` bound and the three
region bounds on the amplitude's logarithmic derivative as the only hypotheses.
The branch geometry, the curvature group, the cofactor group and the amplitude group
are all supplied here, and so is `hstates` in `ft_ftPhaseSupply_general` below, from
`RootStatesGeneral.ft_rootStates_general`.

`ft_branchSupply_general` keeps `hstates` as a binder because it is stated at a
free family of blocks; the composed theorem below discharges it.

The conclusion is `PhaseSupplyProducer.FTBranchSupply` at this pencil, which is
the same object `exists_ftPhaseSupply_of_dominance` takes as `hbranch`. -/
theorem ft_branchSupply_general {n r : ℕ} {a : Fin n → ℝ} {c x₁ c₀ κ₀ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hc₀ : c₀ ∈ Ioo (0 : ℝ) (π / r)) (hκ₀ : 0 ≤ κ₀)
    (h0 : eVariationOn (ftFixedAngle (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
      (ftTauArc a r (n - 1) x₁) (ftArcCofactorDeriv a c r x₁) c₀)
      (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal κ₀) :
    ∃ κ₀' κ₁' : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧
      ∀ B : Polynomial ℂ, B ≠ 0 → ∀ b₁ b₂ c₁ c₂ c₃ : ℝ,
        (∀ s ∈ Ioc (0 : ℝ) b₁, ftAmp (ftRootPoly c a) B r
            ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) s) ≠ 0 →
          |(ftArcAmpDeriv a B c r x₁ s / ftAmp (ftRootPoly c a) B r
            ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) s)).im| ≤ c₁) →
        (∀ s ∈ Icc b₁ b₂, ftAmp (ftRootPoly c a) B r
            ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) s) ≠ 0 →
          |(ftArcAmpDeriv a B c r x₁ s / ftAmp (ftRootPoly c a) B r
            ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) s)).im| ≤ c₂) →
        (∀ s ∈ Ico b₂ (π / r), ftAmp (ftRootPoly c a) B r
            ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) s) ≠ 0 →
          |(ftArcAmpDeriv a B c r x₁ s / ftAmp (ftRootPoly c a) B r
            ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) s)).im| ≤ c₃) →
        (∀ a' b' : ℝ, a' ≤ b' → Icc a' b' ⊆ Ioo (0 : ℝ) (π / r) →
          ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
          (∀ i, Lb i ∈ Icc a' b') → (∀ i, Rb i ∈ Icc a' b') →
          (∀ i j, i < j → Rb i ≤ Lb j) →
          (∀ i, ∀ θ ∈ Icc (Lb i) (Rb i),
            ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
              (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0) →
          ∀ β ∈ B.roots, ∃ ψ : Fin k → ℝ → ℝ,
            RootBranchState (ftPrincipal (ftTauArc a r (n - 1) x₁))
              (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1))
              β a' b' Lb Rb ψ) →
        FTBranchSupply (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
          (ftTauArc a r (n - 1) x₁) κ₀' κ₁' := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hγd, hd2, hc2, hreg⟩ := ft_geometry_group hn ha hr hnr hb x₁ 0
  rw [← ftTauArc_eq_ftTauArcAt] at hγd
  obtain ⟨hKγ, hKvar⟩ := ft_curvature_group hn ha hr hnr
  obtain ⟨hSd, hSc, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr hnr
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hsupply⟩ :=
    exists_uniform_ftBranchSupply (Q := ftRootPoly c a) (r := r)
      (z := ftBranchZLower a c r (n - 1)) (τ := ftTauArc a r (n - 1) x₁)
      (dS := ftArcCofactorDeriv a c r x₁) (dγ := ftGammaDeriv a r (n - 1))
      (d2γ := ftGammaDeriv2 a r (n - 1)) (c₀ := c₀) (κ₀ := κ₀) (Kγ := π / r + π)
      harc hγd hd2 hc2 hreg hKγ hKvar hSd hSc hS0 hc₀ hκ₀ h0
  refine ⟨κ₀', κ₁', hκ₀', hκ₁', fun B hB0 b₁ b₂ c₁ c₂ c₃ h₁ h₂ h₃ hstates => ?_⟩
  obtain ⟨hWd, hWc⟩ := ft_amplitude_group (x₁ := x₁) B hn ha hc hr hnr
  exact hsupply B hB0 (Ioo (0 : ℝ) (π / r)) (ftArcAmpDeriv a B c r x₁) b₁ b₂ c₁ c₂ c₃
    isOpen_Ioo subset_rfl hWd hWc h₁ h₂ h₃ hstates

/-- **`κ₀` at a general admissible pencil, with nothing assumed**, in the `ρ ≥ 2`,
`r ≥ 2` cell.  The three regions of `ft_kappaZero_of_collars` meet here: the collar at the
collision, the middle by compactness, and the outer region at the origin.

Stated at every base point of the open arc, since the fixed angle's base moves it by a
constant and `eVariationOn` cannot see one. -/
theorem ft_kappaZero_general {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∀ c₀ ∈ Ioo (0 : ℝ) (π / r), ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧
      eVariationOn (ftFixedAngle (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
        (ftTauArc a r (n - 1) x₁) (ftArcCofactorDeriv a c r x₁) c₀)
        (Ioo (0 : ℝ) (π / r)) ≤ ENNReal.ofReal κ₀ := by
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  obtain ⟨b₁, C₁, hb₁, -, -, hlo⟩ :=
    ft_lower_collar (n := n) (r := r) (ρ := ρ) (a := a) (c := c) (x₁ := x₁)
      hn2 ha hc hr1 hx₁ hmin hcard hρ
  obtain ⟨b₂, C₃, -, hb₂, hhi⟩ :=
    ft_upper_region (n := n) (r := r) (a := a) (c := c) (x₁ := x₁) hn2 ha hc hr
  exact ft_kappaZero_of_collars (n := n) (r := r) (a := a) (c := c) (x₁ := x₁)
    hn ha hc hr1 (Or.inl hn2) hb₁ hb₂ hlo hhi

/-- **`FTBranchSupply` at a general admissible pencil, with nothing assumed**, in the
`ρ ≥ 2`, `r ≥ 2` cell.

This is the object `PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` takes as
`hbranch`, and it was the last group of the manuscript's proof carried in the tree as a
hypothesis rather than produced.  The two constants are bound **before** the weight, which
is `thm:main` clause 3: they are constants of the pencil and the arc.

The three cut points are reconciled here.  Each region producer returns its own width, and
the middle region asks for an interval; `min` and `max` order the two outer widths, and
both bounds survive the shrink because each is stated on a set the shrink only makes
smaller. -/
theorem ft_branchSupply_general_closed {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ κ₀' κ₁' : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧
      ∀ B : Polynomial ℂ, B.eval 0 ≠ 0 →
        FTBranchSupply (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
          (ftTauArc a r (n - 1) x₁) κ₀' κ₁' := by
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (0 : ℝ) < r := by positivity
  have harc : (0 : ℝ) < π / r := by positivity
  have hc₀ : π / (2 * r) ∈ Ioo (0 : ℝ) (π / r) :=
    ⟨by positivity, div_lt_div_of_pos_left Real.pi_pos hrR (by linarith)⟩
  obtain ⟨κ₀, hκ₀, h0⟩ :=
    ft_kappaZero_general (c := c) hn2 ha hc hr hx₁ hmin hcard hρ _ hc₀
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hsupply⟩ :=
    ft_branchSupply_general (x₁ := x₁) hn ha hc hr1 (Or.inl hn2) hc₀ hκ₀ h0
  refine ⟨κ₀', κ₁', hκ₀', hκ₁', fun B hBev => ?_⟩
  have hB0 : B ≠ 0 := fun h0' => hBev (by rw [h0']; simp)
  obtain ⟨d₁, C₁, hd₁0, hd₁, hlo⟩ :=
    ft_region_lower (n := n) (r := r) (ρ := ρ) (a := a) (c := c) (x₁ := x₁)
      B hB0 hn2 ha hc hr1 hx₁ hmin hcard hρ
  obtain ⟨d₂, C₃, hd₂0, hd₂, hhi⟩ :=
    ft_region_upper (n := n) (r := r) (a := a) (c := c) (x₁ := x₁) B hBev hn2 ha hc hr
  have hb₁0 : 0 < min d₁ d₂ := lt_min hd₁0 hd₂0
  have hb₂lt : max d₁ d₂ < π / r := max_lt hd₁ hd₂
  have hmidsub : Icc (min d₁ d₂) (max d₁ d₂) ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨lt_of_lt_of_le hb₁0 hθ.1, lt_of_le_of_lt hθ.2 hb₂lt⟩
  obtain ⟨C₂, hmid⟩ :=
    ft_region_mid (n := n) (r := r) (a := a) (c := c) (x₁ := x₁)
      B hB0 hn2 ha hc hr1 hmidsub
  exact hsupply B hB0 (min d₁ d₂) (max d₁ d₂) C₁ C₂ C₃
    (fun s hs _ => hlo s ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩)
    hmid
    (fun s hs => hhi s ⟨le_trans (le_max_right _ _) hs.1, hs.2⟩)
    (ft_rootStates_general (c := c) (z := ftBranchZLower a c r (n - 1))
      hn ha hr1 (Or.inl hn2)
      (fun θ hθ => ftTauArc_agree a r (n - 1) x₁ hθ.1 hθ.2))

/-- **`FTPhaseSupply` at a general admissible pencil, with nothing assumed**, at the
`ρ ≥ 2`, `r ≥ 2` cell.

This is the seam between the two halves: `ft_branchSupply_general` produces `hbranch`, and
`exists_ftPhaseSupply_at_branch_of_branchSupply` consumes it against the dominance chain.
Crossing it is the whole point of the statement — each half had been checked alone.

Every group the statement used to carry as a hypothesis is now produced: the geometry and
curvature groups, the cofactor and amplitude groups, `κ₀` (`ft_kappaZero_general`), and
`eq:phase-derivative-bound` on all three regions (`PhaseSupplyRegionBounds`).  The only
inputs left are the admissible class itself and the weight's two conditions.

**The three cut points are reconciled here.**  Each region producer returns its own width,
and the middle region asks for an interval; `min` and `max` order the two outer widths, and
both bounds survive the shrink because each is stated on a set the shrink only makes
smaller. -/
theorem ft_ftPhaseSupply_general {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hB : HasRealCoeffs B) (hBev : B.eval 0 ≠ 0) :
    ∃ κ₀' κ₁' hcol : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧ 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
        (ftTauArc a r (n - 1) x₁) hcol κ₀' κ₁' M := by
  have hB0 : B ≠ 0 := fun h0' => hBev (by rw [h0']; simp)
  obtain ⟨κ₀', κ₁', hκ₀', hκ₁', hbranch⟩ :=
    ft_branchSupply_general_closed (x₁ := x₁) (c := c) hn2 ha hc.ne' hr hx₁ hmin hcard hρ
  obtain ⟨hcol, hhcol, hs⟩ :=
    exists_ftPhaseSupply_at_branch_of_branchSupply (κ₀ := κ₀') (κ₁ := κ₁')
      hn2 ha hc hr hx₁ hmin hcard hρ B hB hBev (hbranch B hBev)
  exact ⟨κ₀', κ₁', hcol, hκ₀', hκ₁', hhcol, hs⟩

end ForgacsTran
