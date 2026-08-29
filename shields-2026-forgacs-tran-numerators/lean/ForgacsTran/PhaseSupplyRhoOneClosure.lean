/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ConsequencesComposition.PhaseQuantization
import ForgacsTran.DominanceSupplyClosure
import ForgacsTran.PhaseSupplyLastCorner

/-!
# `FTPhaseSupply` at a SIMPLE smallest zero, with nothing assumed

`DominanceSupplyClosure` discharges `hdom` at all four corners and leaves `hbranch`;
`PhaseSupplyRhoOne` and `PhaseSupplyLastCorner` produce `hbranch` at the two `ρ = 1`
corners.  The two sides are stated at **different endpoint extensions**, and neither can
be restated as the other, so nothing composed them.  This module supplies the one lemma
that closes the seam, and the two producers it makes possible.

## The endpoint mismatch, and why it does not have to be resolved

At `ρ = 1` the dominance side runs at `ftBranchZLowerAt a c r l (-Q(t_a)/t_a^r)` and at
`ftTauArc a r l t_a`, because at the hardcoded value `0` the endpoint clause `hk₀` is the
false claim `Q(t_a) = 0`.  The branch supply runs at `ftBranchZLower` and at *its own*
limit, and exposes that limit as a `Tendsto` so that a composition can identify the two
endpoints rather than assume them equal.

It need not identify them.  Both extensions branch on `θ`, so **all four functions agree
wherever `0 < θ < π/r`**, and every clause of `FTBranchSupply` reads `z` and `τ` only on
blocks its own hypothesis places inside `Ioo 0 (π/r)`.  So the supply transports across
the seam pointwise, with no relation between the two endpoint values assumed, proved, or
even stateable — which is `ftBranchSupply_congr`.

The consequence is that the two `ρ = 1` corners close from what is already built: no
estimate is re-derived and no endpoint uniqueness argument is needed.  The endpoint that
survives into the conclusion is the dominance side's, since that is the one its own
clauses are stated at.

Sorry-free.

## Main statements

* `ftBranchSupply_congr` — the branch supply depends on `z` and `τ` only through the open
  viewing arc.
* `ftWindow_congr` — so does the window `thm:main` clause 2 counts zeros in, which is why
  the endpoint never has to reach the manuscript's own statements.
* `ft_ftPhaseSupply_general_rho_one` — `FTPhaseSupply` at a simple smallest zero with
  `2 ≤ r`, from the admissible class alone.
* `ft_ftPhaseSupply_general_rho_one_one` — the same at `r = 1`, the last corner.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:main`, `thm:weighted-dominance`,
  `eq:ab-def`, `subsec:proof`.

## Tags

phase supply, branch supply, simple zero, endpoint extension, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

/-! ### The branch supply sees only the open arc -/

/-- **`FTBranchSupply` transports along agreement on the open viewing arc.**

Every clause naming `z` or `τ` sits under the block hypothesis that places
`[L_i, R_i]` inside `Ioo 0 (π/r)`, so the endpoint values the extensions differ at are
never read.  This is what lets the `ρ = 1` branch supply, stated at `ftBranchZLower` and
at the branch's own limit, be consumed by a dominance chain stated at `ftBranchZLowerAt`
and at the endpoint that chain produced. -/
theorem ftBranchSupply_congr {Q B : Polynomial ℂ} {r : ℕ} {z₁ z₂ τ₁ τ₂ : ℝ → ℝ}
    {κ₀ κ₁ : ℝ}
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z₁ θ = z₂ θ)
    (hτ : ∀ θ ∈ Ioo (0 : ℝ) (π / r), τ₁ θ = τ₂ θ)
    (h : FTBranchSupply Q B r z₁ τ₁ κ₀ κ₁) :
    FTBranchSupply Q B r z₂ τ₂ κ₀ κ₁ := by
  obtain ⟨Mb, h⟩ := h
  refine ⟨Mb, fun M hM k Lb Rb hL hR hord hsub hne => ?_⟩
  have hamp : ∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
      ftAmp Q B r ((z₁ θ : ℝ) : ℂ) (ftPrincipal τ₁ θ)
        = ftAmp Q B r ((z₂ θ : ℝ) : ℂ) (ftPrincipal τ₂ θ) := by
    intro i hi θ hθ
    have hmem := hsub i hi hθ
    rw [hz θ hmem, ftPrincipal, ftPrincipal, hτ θ hmem]
  obtain ⟨ψ, dψ, varψ, h1, h2, h3, h4, h5, h6⟩ :=
    h M hM k Lb Rb hL hR hord hsub
      (fun i hi θ hθ => by rw [hamp i hi θ hθ]; exact hne i hi θ hθ)
  refine ⟨ψ, dψ, varψ, fun i hi θ hθ => ?_, h2, h3, h4, h5, h6⟩
  have hpa : ftPrincipalAmp Q B r z₁ τ₁ θ = ftPrincipalAmp Q B r z₂ τ₂ θ := by
    rw [ftPrincipalAmp, ftPrincipalAmp, hamp i hi θ hθ]
  rw [← hamp i hi θ hθ, ← hpa]
  exact h1 i hi θ hθ

/-- **The window is blind to the endpoint too.**  `ftWindow z α β` is the image of `z`
over the OPEN interval, so the two extensions cut the same window and a `ρ = 1`
conclusion may be stated at whichever spelling its neighbors use — with no endpoint in
it. -/
theorem ftWindow_congr {z z' : ℝ → ℝ} {α β : ℝ} (h : ∀ θ ∈ Ioo α β, z θ = z' θ) :
    ftWindow z α β = ftWindow z' α β := by
  rw [ftWindow, ftWindow, Set.image_congr h]

/-! ### The two `ρ = 1` corners, with nothing assumed -/

/-- **`FTPhaseSupply` at an admissible pencil whose smallest zero is SIMPLE**, in the
`2 ≤ r` cell — the third of the four corners `subsec:proof` walks.

The binders are the admissible class — `n`, positive zeros, `0 < c`, `2 ≤ r`, a minimal
index and that minimum simple — together with the weight's two conditions.  Nothing
analytic is assumed: `PhaseSupplyRhoOne` supplies the branch, `DominanceSupplyClosure`
the dominance, and the endpoint disagreement between them is absorbed by
`ftBranchSupply_congr` rather than resolved. -/
theorem ft_ftPhaseSupply_general_rho_one {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {B : Polynomial ℂ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hB : HasRealCoeffs B) (hBev : B.eval 0 ≠ 0) :
    ∃ κ₀' κ₁' hcol ta : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧ 0 < hcol ∧ 0 < ta ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a) B r
          (ftBranchZLowerAt a c r (n - 1) (-((ftRootPolyReal c a).eval ta) / ta ^ r))
          (ftTauArc a r (n - 1) ta) hcol κ₀' κ₁' M := by
  obtain ⟨tb, -, -, κ₀', κ₁', hκ₀', hκ₁', hbranch⟩ :=
    ft_branchSupply_general_closed_rho_one hn2 ha hc hr hmin hsim
  obtain ⟨ta, hta, Hs⟩ :=
    exists_ftPhaseSupply_at_branch_rho_one_of_branchSupply (κ₀ := κ₀') (κ₁ := κ₁')
      hn2 ha hc hr hmin hsim
  have hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), ftBranchZLower a c r (n - 1) θ
      = ftBranchZLowerAt a c r (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ r) θ := fun θ hθ => by
    rw [ftBranchZLower_agree a c r (n - 1) hθ.1,
      ftBranchZLowerAt_agree a c r (n - 1) _ hθ.1]
  have hτ : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftTauArc a r (n - 1) tb θ = ftTauArc a r (n - 1) ta θ := fun θ hθ => by
    rw [ftTauArc_agree a r (n - 1) tb hθ.1 hθ.2, ftTauArc_agree a r (n - 1) ta hθ.1 hθ.2]
  obtain ⟨hcol, hhcol, hs⟩ :=
    Hs B hB hBev (ftBranchSupply_congr hz hτ (hbranch B hBev))
  exact ⟨κ₀', κ₁', hcol, ta, hκ₀', hκ₁', hhcol, hta, hs⟩

/-- **`FTPhaseSupply` at an admissible pencil whose smallest zero is SIMPLE**, in the
`r = 1` cell — the last of the four corners.

`3 ≤ n` is the `(deg Q, r) ≠ (2,1)` exclusion the `r = 1` dominance corner inherits from
`Forgacs2017RationalDenominator` Props. 1--2, which the manuscript discharges separately
in `rem:quadratic-case` rather than assuming.  The branch supply itself holds at `2 ≤ n`
and asks only that the weight be nonzero. -/
theorem ft_ftPhaseSupply_general_rho_one_one {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {B : Polynomial ℂ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hB : HasRealCoeffs B) (hBev : B.eval 0 ≠ 0) :
    ∃ κ₀' κ₁' hcol ta : ℝ, 0 ≤ κ₀' ∧ 0 ≤ κ₁' ∧ 0 < hcol ∧ 0 < ta ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a) B 1
          (ftBranchZLowerAt a c 1 (n - 1) (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
          (ftTauArc a 1 (n - 1) ta) hcol κ₀' κ₁' M := by
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  obtain ⟨tb, -, -, κ₀', κ₁', hκ₀', hκ₁', hbranch⟩ :=
    ft_branchSupply_general_closed_rho_one_one (by omega : 2 ≤ n) ha hc hmin hsim
  obtain ⟨ta, hta, Hs⟩ :=
    exists_ftPhaseSupply_at_branch_rho_one_one_of_branchSupply (κ₀ := κ₀') (κ₁ := κ₁')
      hn3 ha hc hmin hsim
  have hz : ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), ftBranchZLower a c 1 (n - 1) θ
      = ftBranchZLowerAt a c 1 (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ 1) θ := fun θ hθ => by
    rw [ftBranchZLower_agree a c 1 (n - 1) hθ.1,
      ftBranchZLowerAt_agree a c 1 (n - 1) _ hθ.1]
  have hτ : ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)),
      ftTauArc a 1 (n - 1) tb θ = ftTauArc a 1 (n - 1) ta θ := fun θ hθ => by
    rw [ftTauArc_agree a 1 (n - 1) tb hθ.1 hθ.2, ftTauArc_agree a 1 (n - 1) ta hθ.1 hθ.2]
  obtain ⟨hcol, hhcol, hs⟩ :=
    Hs B hB hBev (ftBranchSupply_congr hz hτ (hbranch B hB0))
  exact ⟨κ₀', κ₁', hcol, ta, hκ₀', hκ₁', hhcol, hta, hs⟩

end ForgacsTran
