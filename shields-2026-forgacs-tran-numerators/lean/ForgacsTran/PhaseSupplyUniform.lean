/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PhaseSupplyGeneral
import ForgacsTran.PhaseSupplyOne
import ForgacsTran.PhaseSupplyRhoOneClosure

/-!
# The phase supply with its constants bound BEFORE the weight

`PhaseSupplyGeneral`, `PhaseSupplyOne` and `PhaseSupplyRhoOneClosure` each produce
`AngularDiscrepancyFT.FTPhaseSupply` at one corner of the admissible class, at a weight
`B` fixed by the statement.  Their constants are existential in the conclusion, so nothing
in those statements forbids `hcol`, `κ_0` and `κ_1` from moving with `B` — and `thm:main`
clause 3 is precisely the assertion that they do not.

The four theorems here restate the same four corners with `∀ B` **inside** the existential.
Nothing is re-derived: at every corner the collar comes from
`DominanceSupplyClosure.exists_dominance_bundle_at_branch*`, whose own statement already
quantifies over `B` after the collar, and the two variation constants from
`ft_branchSupply_general_closed*`, which do the same.  What the corner assemblies did was
apply them under `B` and re-bind; here they are applied ahead of it, and
`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` is the only step that sees the
weight at all.

That is the whole content: the binder order is the theorem.  A reader checking clause 3's
uniformity has to read one quantifier prefix rather than trace three producers.

Sorry-free.

## Main statements

* `ft_ftPhaseSupply_uniform` — the `ρ ≥ 2`, `2 ≤ r` corner.
* `ft_ftPhaseSupply_uniform_one` — `ρ ≥ 2`, `r = 1`.
* `ft_ftPhaseSupply_uniform_rho_one` — `ρ = 1`, `2 ≤ r`.
* `ft_ftPhaseSupply_uniform_rho_one_one` — `ρ = 1`, `r = 1`.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:main` clause 3,
`subsec:proof`, `prop:angular-discrepancy`, `thm:weighted-dominance`,
`cor:linear-phase-variation`.

## Tags

phase supply, uniformity, admissible pencil, binder order
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **The supply at the `ρ ≥ 2`, `2 ≤ r` corner, uniformly in the weight.**  The collar
`hcol` and the variation constants `κ_0`, `κ_1` are produced from the pencil alone and
then held fixed as `B` ranges over every real weight not vanishing at the origin. -/
theorem ft_ftPhaseSupply_uniform (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
          FTPhaseSupply (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) x₁) hcol κ₀ κ₁ M := by
  obtain ⟨κ₀, κ₁, hκ₀, hκ₁, hbranch⟩ :=
    ft_branchSupply_general_closed (x₁ := x₁) (c := c) hn2 ha hc.ne' hr hx₁ hmin hcard hρ
  obtain ⟨hcol, hhcol, Hb⟩ :=
    exists_dominance_bundle_at_branch (x₁ := x₁) hn2 ha hc hr hx₁ hmin hcard hρ
  refine ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, fun B hB hBev => ?_⟩
  obtain ⟨ε, σ, -, hσ0, hσ1, hεband, hτ, hroot, hsimple, hband, hdom⟩ := Hb B hB hBev
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB (by omega)
    (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
    (ftRootPoly_coeff_one_ne_zero (by omega) hc.ne' ha) hB0 hBev hσ0 hσ1 hhcol
    hεband hτ hroot hsimple hband hdom (hbranch B hBev)

/-- **The supply at the `ρ ≥ 2`, `r = 1` corner, uniformly in the weight.**  `3 ≤ n` is
the `(deg Q, r) ≠ (2,1)` exclusion the `r = 1` dominance corner carries. -/
theorem ft_ftPhaseSupply_uniform_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
          FTPhaseSupply (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
            (ftTauArc a 1 (n - 1) x₁) hcol κ₀ κ₁ M := by
  obtain ⟨κ₀, κ₁, hκ₀, hκ₁, hbranch⟩ :=
    ft_branchSupply_general_closed_one (ρ := ρ) (x₁ := x₁) (c := c)
      (by omega) ha hc hx₁ hmin hcard hρ
  obtain ⟨hcol, hhcol, Hb⟩ :=
    exists_dominance_bundle_at_branch_one (x₁ := x₁) hn3 ha hc hx₁ hmin hcard hρ
  refine ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, fun B hB hBev => ?_⟩
  obtain ⟨ε, σ, -, hσ0, hσ1, hεband, hτ, hroot, hsimple, hband, hdom⟩ := Hb B hB hBev
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB le_rfl
    (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
    (ftRootPoly_coeff_one_ne_zero (by omega) hc.ne' ha) hB0 hBev hσ0 hσ1 hhcol
    hεband hτ hroot hsimple hband hdom (hbranch B hB0)

/-- **The supply at the `ρ = 1`, `2 ≤ r` corner, uniformly in the weight.**  The endpoint
`ta` is produced by the pencil, so it stands beside the constants ahead of `∀ B`; the
branch supply is transported onto the dominance side's endpoint by
`PhaseSupplyRhoOneClosure.ftBranchSupply_congr`, which reads `z` and `τ` only on the open
arc. -/
theorem ft_ftPhaseSupply_uniform_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta hcol κ₀ κ₁ : ℝ, 0 < ta ∧ 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
          FTPhaseSupply (ftRootPoly c a) B r
            (ftBranchZLowerAt a c r (n - 1)
              (-((ftRootPolyReal c a).eval ta) / ta ^ r))
            (ftTauArc a r (n - 1) ta) hcol κ₀ κ₁ M := by
  obtain ⟨tb, -, -, κ₀, κ₁, hκ₀, hκ₁, hbranch⟩ :=
    ft_branchSupply_general_closed_rho_one hn2 ha hc hr hmin hsim
  obtain ⟨hcol, ta, hhcol, hta, Hb⟩ :=
    exists_dominance_bundle_at_branch_rho_one hn2 ha hc hr hmin hsim
  have hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), ftBranchZLower a c r (n - 1) θ
      = ftBranchZLowerAt a c r (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ r) θ := fun θ hθ => by
    rw [ftBranchZLower_agree a c r (n - 1) hθ.1,
      ftBranchZLowerAt_agree a c r (n - 1) _ hθ.1]
  have hτc : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftTauArc a r (n - 1) tb θ = ftTauArc a r (n - 1) ta θ := fun θ hθ => by
    rw [ftTauArc_agree a r (n - 1) tb hθ.1 hθ.2, ftTauArc_agree a r (n - 1) ta hθ.1 hθ.2]
  refine ⟨ta, hcol, κ₀, κ₁, hta, hhcol, hκ₀, hκ₁, fun B hB hBev => ?_⟩
  obtain ⟨ε, σ, -, hσ0, hσ1, hεband, hτ, hroot, hsimple, hband, hdom⟩ := Hb B hB hBev
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB (by omega)
    (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
    (ftRootPoly_coeff_one_ne_zero (by omega) hc.ne' ha) hB0 hBev hσ0 hσ1 hhcol
    hεband hτ hroot hsimple hband hdom
    (ftBranchSupply_congr hz hτc (hbranch B hBev))

/-- **The supply at the `ρ = 1`, `r = 1` corner, uniformly in the weight** — the last of
the four.  The collar is the literal `1` the dominance corner returns. -/
theorem ft_ftPhaseSupply_uniform_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta hcol κ₀ κ₁ : ℝ, 0 < ta ∧ 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
          FTPhaseSupply (ftRootPoly c a) B 1
            (ftBranchZLowerAt a c 1 (n - 1)
              (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
            (ftTauArc a 1 (n - 1) ta) hcol κ₀ κ₁ M := by
  obtain ⟨tb, -, -, κ₀, κ₁, hκ₀, hκ₁, hbranch⟩ :=
    ft_branchSupply_general_closed_rho_one_one (by omega : 2 ≤ n) ha hc hmin hsim
  obtain ⟨ta, hta, Hb⟩ :=
    exists_dominance_bundle_at_branch_rho_one_one hn3 ha hc hmin hsim
  have hz : ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), ftBranchZLower a c 1 (n - 1) θ
      = ftBranchZLowerAt a c 1 (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ 1) θ := fun θ hθ => by
    rw [ftBranchZLower_agree a c 1 (n - 1) hθ.1,
      ftBranchZLowerAt_agree a c 1 (n - 1) _ hθ.1]
  have hτc : ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)),
      ftTauArc a 1 (n - 1) tb θ = ftTauArc a 1 (n - 1) ta θ := fun θ hθ => by
    rw [ftTauArc_agree a 1 (n - 1) tb hθ.1 hθ.2, ftTauArc_agree a 1 (n - 1) ta hθ.1 hθ.2]
  refine ⟨ta, 1, κ₀, κ₁, hta, one_pos, hκ₀, hκ₁, fun B hB hBev => ?_⟩
  obtain ⟨ε, σ, -, hσ0, hσ1, hεband, hτ, hroot, hsimple, hband, hdom⟩ := Hb B hB hBev
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB le_rfl
    (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
    (ftRootPoly_coeff_one_ne_zero (by omega) hc.ne' ha) hB0 hBev hσ0 hσ1 one_pos
    hεband hτ hroot hsimple hband hdom
    (ftBranchSupply_congr hz hτc (hbranch B hB0))

end ForgacsTran
