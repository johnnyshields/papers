/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CompositionLinks
import ForgacsTran.CompositionLinksRhoOne
import ForgacsTran.MainFT
import ForgacsTran.PhaseSupplyGeneral
import ForgacsTran.PhaseSupplyOne
import ForgacsTran.PhaseSupplyRhoOneClosure

/-!
# `thm:main` at an admissible pencil, with nothing assumed

`MainFT` states the three clauses of `thm:main` against a supply of
`AngularDiscrepancyFT.FTPhaseSupply`, and `PhaseSupplyGeneral` produces that supply from
the admissible class.  This module runs the one into the other, so that the theorems
below carry **no analytic hypothesis at all**: their binders are the pencil's own data —
the zeros `a`, the leading constant `c`, the exponent `r`, the multiplicity `ρ` of the
smallest zero, and the bivariate numerator `N` — and every geometric input is discharged
by a named producer.

That is the check the producer table cannot make.  Each hypothesis of the supply having a
supplier says only that something of the right shape exists; it does not say the shapes
compose, and a bound carried as a hypothesis where a producer was meant type-checks with
*fewer* complaints than one that runs.  Here nothing can be carried, because the
statements have nowhere to carry it.

**The arc is open, and that is not a technicality.**  The supply is produced at
`ftBranchZLower` and `ftTauArc`, which are the branch's spectral parameter and radius
extended to the closed viewing arc by their endpoint limits.  At the upper end the branch
runs into the origin, so `ftTauArc` is `0` there, and at `2 ≤ r` the spectral parameter
diverges (`eq:ab-def`'s `b = +∞`).  Positivity of the radius and monotonicity of the
parameter are therefore statements about `(0, π/r)` and are false on `[0, π/r]` —
`CompositionLinks.not_continuousOn_ftBranchZLower_Icc` and
`not_strictMonoOn_ftBranchZLower_Icc` record the second of those.  The consumers in
`MainFT` ask for exactly the open-arc form.

## Main statements

* `ftPhaseSupply_laurentWeight_general` — the supply at the *reduced weight* `B_N`
  rather than at an arbitrary `B`, which is the shape `MainFT` consumes.
* `main_bound_admissible`, `main_bound_interval_admissible`,
  `interior_distinct_count_admissible` — the three clauses of `thm:main` at an admissible
  pencil with `2 ≤ r` and a repeated smallest zero.
* `ftPhaseSupply_laurentWeight_one`, `main_bound_admissible_one`,
  `main_bound_interval_admissible_one`, `interior_distinct_count_admissible_one` — the
  same seam at `r = 1`, where the branch supply is closed by a different route and the
  arc is the half-plane `(0, π)`.
* `ftPhaseSupply_laurentWeight_rho_one`, `ftPhaseSupply_laurentWeight_rho_one_one` and
  the six clauses beside them — the two corners at a **simple** smallest zero, which
  complete the manuscript's 2×2 grid.  There the branch's lower endpoint is a critical
  point strictly inside the first gap rather than the smallest zero, so the spectral
  parameter is `ftBranchZLowerAt` with that value supplied; the endpoint is produced by
  the pencil, so the interval clauses bind it existentially in the conclusion while
  clause 1, whose conclusion names only the positive ray, does not mention it at all.

The grid is complete: `DominanceCellPartition.ft_dominance_cell_of_admissible` exhausts
the admissible class by the four corners, and each corner carries all three clauses.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, `thm:main`,
`prop:angular-discrepancy`, `lem:laurent-reduction`, `thm:FT-geometry`,
`eq:ab-def`, `eq:angular-distinct-lower`.

## Tags

main theorem, admissible pencil, phase supply, composition
-/

open Polynomial Set Real

namespace ForgacsTran

section Admissible

variable {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {N : (Polynomial ℂ)[X]}

/-! ### The supply at the reduced weight -/

/-- **The phase supply at the weight the reduction actually produces.**
`PhaseSupplyGeneral.ft_ftPhaseSupply_general` holds at every real weight not vanishing at
the origin; `lem:laurent-reduction` hands the consumer one specific such weight, `B_N`, and
this is the producer read at it.  The two conditions on `B_N` are
`CompositionLinks.hasRealCoeffs_laurentWeight` and `eval_laurentWeight_zero_ne_zero`. -/
theorem ftPhaseSupply_laurentWeight_general (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ)) :
    ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply (ftRootPoly c a) (laurentWeight (ftRootPoly c a) r N) r
        (ftBranchZLower a c r (n - 1)) (ftTauArc a r (n - 1) x₁) hcol κ₀ κ₁ M := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨κ₀, κ₁, hcol, hκ₀, hκ₁, hhcol, hs⟩ :=
    ft_ftPhaseSupply_general (ρ := ρ) hn2 ha hc hr hx₁ hmin hcard hρ
      (hasRealCoeffs_laurentWeight hr1 hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
      (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) hr1 hQ0 hN hproper)
  exact ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩

/-- **The phase supply at the reduced weight, at `r = 1`.**  `3 ≤ n` is the
`(deg Q, r) ≠ (2,1)` exclusion `PhaseSupplyOne.ft_ftPhaseSupply_general_one` carries. -/
theorem ftPhaseSupply_laurentWeight_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ)) :
    ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply (ftRootPoly c a) (laurentWeight (ftRootPoly c a) 1 N) 1
        (ftBranchZLower a c 1 (n - 1)) (ftTauArc a 1 (n - 1) x₁) hcol κ₀ κ₁ M := by
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨κ₀, κ₁, hcol, hκ₀, hκ₁, hhcol, hs⟩ :=
    ft_ftPhaseSupply_general_one (ρ := ρ) hn3 ha hc hx₁ hmin hcard hρ
      (hasRealCoeffs_laurentWeight le_rfl hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
      (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) le_rfl hQ0 hN hproper)
  exact ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩

/-! ### `thm:main` at the pencil -/

variable {coeffPoly : ℕ → Polynomial ℂ}

/-- **`thm:main` clause 1 at an admissible pencil, with nothing assumed.**  A single
constant bounds the number of zeros of every nonzero `P_m` off the positive ray.

Every geometric input of `MainFT.main_bound_of_supply` is discharged by a producer named
here: `CompositionLinks.strictMonoOn_ftBranchZLower_Ioo`,
`continuousOn_ftBranchZLower_Ioo`, `ftTauArc_pos`, `ftBranchZLower_pos`, and
`ftPhaseSupply_laurentWeight_general` for the supply itself.  No hypothesis of this
statement mentions the branch, the radius, the amplitude or a zero set. -/
theorem main_bound_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) r) coeffPoly m = (swapVars N).coeff m) :
    ∃ C : ℕ, ∀ m, coeffPoly m ≠ 0 →
      (exceptionalRoots (coeffPoly m) posRay).card ≤ C := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  exact main_bound_of_supply hr1 (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN hproper
    coeffPoly hP
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
    (fun _ hθ => ftBranchZLower_pos hn ha hc hr1 hnr hθ)
    (ftPhaseSupply_laurentWeight_general (ρ := ρ) hn2 ha hc hr hx₁ hmin hcard hρ hN hNr
      hproper)

/-- **`thm:main` clause 2 at an admissible pencil, with nothing assumed.**  For all large
`m`, at most `C ≤ C₀ + C₁ deg B_N + 1` zeros of `P_m` outside the Forgács–Tran interval
counted with multiplicity, and at least `deg P_m - C` **distinct** zeros inside it. -/
theorem main_bound_interval_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) r) coeffPoly m = (swapVars N).coeff m) :
    ∃ (C₀ C₁ : ℝ) (C m0 : ℕ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m →
        (coeffPoly m ≠ 0 →
          (exceptionalRoots (coeffPoly m)
            (ftWindow (ftBranchZLower a c r (n - 1)) 0 (π / r))).card ≤ C) ∧
        ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c r (n - 1)) 0 (π / r)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  exact main_bound_interval_of_supply hr1 (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN
    hproper coeffPoly hP
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
    (fun _ hθ => ftBranchZLower_pos hn ha hc hr1 hnr hθ)
    (ftPhaseSupply_laurentWeight_general (ρ := ρ) hn2 ha hc hr hx₁ hmin hcard hρ hN hNr
      hproper)

/-- **`thm:main` clause 2(iii) at an admissible pencil, with nothing assumed.**  The zero
set is a conclusion: no hypothesis names it, and none names the branch it lies along. -/
theorem interior_distinct_count_admissible (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) r) coeffPoly m = (swapVars N).coeff m) :
    ∃ (C₀ C₁ : ℝ) (C m0 : ℕ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m → ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
        (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c r (n - 1)) 0 (π / r)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  exact interior_distinct_count_of_supply hr1 (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN
    hproper coeffPoly hP
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
    (fun _ hθ => ftBranchZLower_pos hn ha hc hr1 hnr hθ)
    (ftPhaseSupply_laurentWeight_general (ρ := ρ) hn2 ha hc hr hx₁ hmin hcard hρ hN hNr
      hproper)

/-- **`thm:main` clause 1 at `r = 1`.**  The same composition against the `r = 1` branch
supply, which is closed by a different route (`PhaseSupplyOne`). -/
theorem main_bound_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) 1) coeffPoly m = (swapVars N).coeff m) :
    ∃ C : ℕ, ∀ m, coeffPoly m ≠ 0 →
      (exceptionalRoots (coeffPoly m) posRay).card ≤ C := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  exact main_bound_of_supply le_rfl (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN hproper
    coeffPoly hP
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
    (fun _ hθ => ftBranchZLower_pos hn ha hc le_rfl hnr hθ)
    (ftPhaseSupply_laurentWeight_one (ρ := ρ) hn3 ha hc hx₁ hmin hcard hρ hN hNr hproper)

/-- **`thm:main` clause 2 at `r = 1`.**  The window is the same open arc `(0, π)`, and
the supply is the `r = 1` one; `hproper` and `hP` are stated at `1` rather than at `r`. -/
theorem main_bound_interval_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) 1) coeffPoly m = (swapVars N).coeff m) :
    ∃ (C₀ C₁ : ℝ) (C m0 : ℕ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m →
        (coeffPoly m ≠ 0 →
          (exceptionalRoots (coeffPoly m)
            (ftWindow (ftBranchZLower a c 1 (n - 1)) 0 (π / ((1 : ℕ) : ℝ)))).card ≤ C) ∧
        ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c 1 (n - 1)) 0
            (π / ((1 : ℕ) : ℝ))) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  exact main_bound_interval_of_supply le_rfl (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN
    hproper coeffPoly hP
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
    (fun _ hθ => ftBranchZLower_pos hn ha hc le_rfl hnr hθ)
    (ftPhaseSupply_laurentWeight_one (ρ := ρ) hn3 ha hc hx₁ hmin hcard hρ hN hNr hproper)

/-- **`thm:main` clause 2(iii) at `r = 1`.**  The zero set is a conclusion here too: no
hypothesis names it, and none names the branch it lies along. -/
theorem interior_distinct_count_admissible_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) 1) coeffPoly m = (swapVars N).coeff m) :
    ∃ (C₀ C₁ : ℝ) (C m0 : ℕ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m → ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
        (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLower a c 1 (n - 1)) 0
          (π / ((1 : ℕ) : ℝ))) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  exact interior_distinct_count_of_supply le_rfl
    (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN hproper coeffPoly hP
    (strictMonoOn_ftBranchZLower_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLower_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
    (fun _ hθ => ftBranchZLower_pos hn ha hc le_rfl hnr hθ)
    (ftPhaseSupply_laurentWeight_one (ρ := ρ) hn3 ha hc hx₁ hmin hcard hρ hN hNr hproper)

/-! ### The two corners at a simple smallest zero -/

/-- **The phase supply at the reduced weight, at a simple smallest zero.**  The endpoint
`ta` is produced by the pencil rather than named by the hypotheses, so it is returned
alongside the supply; on the open arc neither `ftBranchZLowerAt` nor `ftTauArc` depends on
it, which is what let the branch and dominance sides meet despite naming different
endpoints. -/
theorem ftPhaseSupply_laurentWeight_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ)) :
    ∃ ta : ℝ, 0 < ta ∧ ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a) (laurentWeight (ftRootPoly c a) r N) r
          (ftBranchZLowerAt a c r (n - 1) (-((ftRootPolyReal c a).eval ta) / ta ^ r))
          (ftTauArc a r (n - 1) ta) hcol κ₀ κ₁ M := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨κ₀, κ₁, hcol, ta, hκ₀, hκ₁, hhcol, hta, hs⟩ :=
    ft_ftPhaseSupply_general_rho_one hn2 ha hc hr hmin hsim
      (hasRealCoeffs_laurentWeight hr1 hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
      (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) hr1 hQ0 hN hproper)
  exact ⟨ta, hta, hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩

/-- **`thm:main` clause 1 at a simple smallest zero, `2 ≤ r`, with nothing assumed.**  The
conclusion names only the positive ray, so the branch's endpoint does not appear in the
statement at all — the composition leaks no existential. -/
theorem main_bound_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) r) coeffPoly m = (swapVars N).coeff m) :
    ∃ C : ℕ, ∀ m, coeffPoly m ≠ 0 →
      (exceptionalRoots (coeffPoly m) posRay).card ≤ C := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨ta, -, hsupply⟩ :=
    ftPhaseSupply_laurentWeight_rho_one hn2 ha hc hr hmin hsim hN hNr hproper
  exact main_bound_of_supply hr1 (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN hproper
    coeffPoly hP
    (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc hr1 hnr)
    (continuousOn_ftBranchZLowerAt_Ioo hn ha hr1 hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
    (fun _ hθ => ftBranchZLowerAt_pos hn ha hc hr1 hnr hθ)
    hsupply

/-- **`thm:main` clause 2 at a simple smallest zero, `2 ≤ r`, with nothing assumed.**  The
window is stated at the endpoint the pencil produces, so `ta` is bound in the conclusion —
that is the honest form, not a weakening: no hypothesis names it either. -/
theorem main_bound_interval_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) r) coeffPoly m = (swapVars N).coeff m) :
    ∃ (ta C₀ C₁ : ℝ) (C m0 : ℕ), 0 < ta ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m →
        (coeffPoly m ≠ 0 →
          (exceptionalRoots (coeffPoly m)
            (ftWindow (ftBranchZLowerAt a c r (n - 1)
              (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 (π / r))).card ≤ C) ∧
        ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 (π / r)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨ta, hta, hsupply⟩ :=
    ftPhaseSupply_laurentWeight_rho_one hn2 ha hc hr hmin hsim hN hNr hproper
  obtain ⟨C₀, C₁, C, m0, hC₀, hC₁, hCb, hmain⟩ :=
    main_bound_interval_of_supply hr1 (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN hproper
      coeffPoly hP
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc hr1 hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha hr1 hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
      (fun _ hθ => ftBranchZLowerAt_pos hn ha hc hr1 hnr hθ)
      hsupply
  exact ⟨ta, C₀, C₁, C, m0, hta, hC₀, hC₁, hCb, hmain⟩

/-- **`thm:main` clause 2(iii) at a simple smallest zero, `2 ≤ r`, with nothing
assumed.**  The zero set and the window are both conclusions, and so is the endpoint the
window is stated at: `ta` is bound existentially beside the constants. -/
theorem interior_distinct_count_admissible_rho_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) {i : Fin n} (hmin : ∀ k, a i ≤ a k)
    (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree r : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) r) coeffPoly m = (swapVars N).coeff m) :
    ∃ (ta C₀ C₁ : ℝ) (C m0 : ℕ), 0 < ta ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) r N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m → ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
        (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c r (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ r)) 0 (π / r)) := by
  have hr1 : 1 ≤ r := le_trans one_le_two hr
  have hn : 0 < n := lt_of_lt_of_le two_pos hn2
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨ta, hta, hsupply⟩ :=
    ftPhaseSupply_laurentWeight_rho_one hn2 ha hc hr hmin hsim hN hNr hproper
  obtain ⟨C₀, C₁, C, m0, hC₀, hC₁, hCb, hmain⟩ :=
    interior_distinct_count_of_supply hr1 (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN
      hproper coeffPoly hP
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc hr1 hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha hr1 hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc hr1 hnr hθ)
      (fun _ hθ => ftBranchZLowerAt_pos hn ha hc hr1 hnr hθ)
      hsupply
  exact ⟨ta, C₀, C₁, C, m0, hta, hC₀, hC₁, hCb, hmain⟩

/-- **`thm:main` clause 1 at a simple smallest zero, `r = 1`** — the last of the four
corners.  `3 ≤ n` is the manuscript's `(deg Q, r) ≠ (2,1)` exclusion. -/
theorem main_bound_admissible_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) 1) coeffPoly m = (swapVars N).coeff m) :
    ∃ C : ℕ, ∀ m, coeffPoly m ≠ 0 →
      (exceptionalRoots (coeffPoly m) posRay).card ≤ C := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨κ₀, κ₁, hcol, ta, hκ₀, hκ₁, hhcol, -, hs⟩ :=
    ft_ftPhaseSupply_general_rho_one_one hn3 ha hc hmin hsim
      (hasRealCoeffs_laurentWeight le_rfl hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
      (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) le_rfl hQ0 hN hproper)
  exact main_bound_of_supply le_rfl hQ0 hN hproper coeffPoly hP
    (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc le_rfl hnr)
    (continuousOn_ftBranchZLowerAt_Ioo hn ha le_rfl hnr)
    (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
    (fun _ hθ => ftBranchZLowerAt_pos hn ha hc le_rfl hnr hθ)
    ⟨hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩

/-- **The phase supply at the reduced weight, at a simple smallest zero with `r = 1`.**
The last corner's producer, read at `B_N`: `PhaseSupplyRhoOneClosure` returns the endpoint
`ta` it produced, and the two conditions on `B_N` are the same two as everywhere else. -/
theorem ftPhaseSupply_laurentWeight_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ)) :
    ∃ ta : ℝ, 0 < ta ∧ ∃ hcol κ₀ κ₁ : ℝ, 0 < hcol ∧ 0 ≤ κ₀ ∧ 0 ≤ κ₁ ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        FTPhaseSupply (ftRootPoly c a) (laurentWeight (ftRootPoly c a) 1 N) 1
          (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
          (ftTauArc a 1 (n - 1) ta) hcol κ₀ κ₁ M := by
  have hQ0 : (ftRootPoly c a).coeff 0 ≠ 0 := ftRootPoly_coeff_zero_ne_zero hc.ne' ha
  obtain ⟨κ₀, κ₁, hcol, ta, hκ₀, hκ₁, hhcol, hta, hs⟩ :=
    ft_ftPhaseSupply_general_rho_one_one hn3 ha hc hmin hsim
      (hasRealCoeffs_laurentWeight le_rfl hQ0 (hasRealCoeffs_ftRootPoly c a) hN hNr hproper)
      (eval_laurentWeight_zero_ne_zero (ftRootPoly c a) le_rfl hQ0 hN hproper)
  exact ⟨ta, hta, hcol, κ₀, κ₁, hhcol, hκ₀, hκ₁, hs⟩

/-- **`thm:main` clause 2 at a simple smallest zero, `r = 1`, with nothing assumed.**  The
last corner of the interval clause.  As at `2 ≤ r`, the endpoint the window is stated at
is produced by the pencil, so `ta` is bound in the conclusion. -/
theorem main_bound_interval_admissible_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) 1) coeffPoly m = (swapVars N).coeff m) :
    ∃ (ta C₀ C₁ : ℝ) (C m0 : ℕ), 0 < ta ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m →
        (coeffPoly m ≠ 0 →
          (exceptionalRoots (coeffPoly m)
            (ftWindow (ftBranchZLowerAt a c 1 (n - 1)
              (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0
              (π / ((1 : ℕ) : ℝ)))).card ≤ C) ∧
        ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0 (π / ((1 : ℕ) : ℝ))) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  obtain ⟨ta, hta, hsupply⟩ :=
    ftPhaseSupply_laurentWeight_rho_one_one hn3 ha hc hmin hsim hN hNr hproper
  obtain ⟨C₀, C₁, C, m0, hC₀, hC₁, hCb, hmain⟩ :=
    main_bound_interval_of_supply le_rfl (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN
      hproper coeffPoly hP
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc le_rfl hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha le_rfl hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
      (fun _ hθ => ftBranchZLowerAt_pos hn ha hc le_rfl hnr hθ)
      hsupply
  exact ⟨ta, C₀, C₁, C, m0, hta, hC₀, hC₁, hCb, hmain⟩

/-- **`thm:main` clause 2(iii) at a simple smallest zero, `r = 1`, with nothing assumed.**
The twelfth cell of the grid: the zero set, the window and the endpoint are all
conclusions. -/
theorem interior_distinct_count_admissible_rho_one_one (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsim : ∀ k, k ≠ i → a k ≠ a i)
    (hN : N ≠ 0) (hNr : ∀ β, HasRealCoeffs (N.coeff β))
    (hproper : ∀ β, (N.coeff β).degree
      < ((max (ftRootPoly c a).natDegree 1 : ℕ) : WithBot ℕ))
    (hP : ∀ m, denomConv (ftDenom (ftRootPoly c a) 1) coeffPoly m = (swapVars N).coeff m) :
    ∃ (ta C₀ C₁ : ℝ) (C m0 : ℕ), 0 < ta ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (C : ℝ) ≤ C₀ + C₁ * ((laurentWeight (ftRootPoly c a) 1 N).natDegree : ℝ) + 1 ∧
      ∀ m, m0 ≤ m → ∃ Z : Finset ℂ, (coeffPoly m).natDegree - C ≤ Z.card ∧
        (∀ w ∈ Z, (coeffPoly m).IsRoot w) ∧
        (∀ w ∈ Z, w ∈ ftWindow (ftBranchZLowerAt a c 1 (n - 1)
          (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) 0 (π / ((1 : ℕ) : ℝ))) := by
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ 1 := Or.inl (by omega)
  obtain ⟨ta, hta, hsupply⟩ :=
    ftPhaseSupply_laurentWeight_rho_one_one hn3 ha hc hmin hsim hN hNr hproper
  obtain ⟨C₀, C₁, C, m0, hC₀, hC₁, hCb, hmain⟩ :=
    interior_distinct_count_of_supply le_rfl
      (ftRootPoly_coeff_zero_ne_zero hc.ne' ha) hN hproper coeffPoly hP
      (strictMonoOn_ftBranchZLowerAt_Ioo hn ha hc le_rfl hnr)
      (continuousOn_ftBranchZLowerAt_Ioo hn ha le_rfl hnr)
      (fun _ hθ => ftTauArc_pos (c := c) hn ha hc le_rfl hnr hθ)
      (fun _ hθ => ftBranchZLowerAt_pos hn ha hc le_rfl hnr hθ)
      hsupply
  exact ⟨ta, C₀, C₁, C, m0, hta, hC₀, hC₁, hCb, hmain⟩

end Admissible

end ForgacsTran
