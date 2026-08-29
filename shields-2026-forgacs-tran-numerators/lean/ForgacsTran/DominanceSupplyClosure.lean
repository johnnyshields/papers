/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchRetainedNonempty
import ForgacsTran.WeightedDominanceBranch
import ForgacsTran.DominanceBandAntitone
import ForgacsTran.EventualDegree

/-!
# `eq:dominance-bound` in the producer's shape, discharged at the branch

`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance` leaves exactly two
hypotheses, `hdom` and `hbranch`.  This module discharges `hdom` — not by
assuming it under another name, but by composing
`WeightedDominanceBranch.ft_weighted_dominance` through the deleted family.

## The `ε` seam, and why one `ε` serves

`ft_weighted_dominance` produces its own `ε` and the producer takes `ε` as a
parameter, so the two have to be reconciled.  They can be, and the reason is an
asymmetry worth naming: `ε` occurs in `ft_weighted_dominance` **only in the
antecedent** — the conclusion `∀ θ, h/M ≤ θ → … → θ ∉ Θ M → …` never mentions it —
and the antecedent is *monotone* in the band, since data on `[ε, π/r-ε]` restricts
to any smaller band.  The producer's `hband`, by contrast, wants `ε` **small**, and
is monotone the same way: a band containing every amplitude zero still does when
enlarged.

Both constraints therefore pull toward smaller `ε`, so `min` settles it.  Had one
wanted `ε` large and the other small there would have been nothing to do.
`DominanceBandAntitone.ft_weighted_dominance_at_any_band` is where that antitonicity
is proved; this module consumes it rather than restating it, so the band is
dictated by `hband` and no dominance clause is shifted here.

`ε` does not appear in `FTPhaseSupply` at all, which is why it can be existential
here; `hcol` does appear, so it is threaded rather than bound away.

## Main statements

* `ftRootPoly_coeff_one_ne_zero` — `Q'(0) ≠ 0` at the pencil, from positivity.
* `exists_dominance_bundle_at_branch` — `hdom` and everything else
  `ftAngularDiscrepancy_of_dominance` asks for, except `hbranch`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:dominance-bound`, `eq:amplitude-deletion`, `subsec:proof`.

## Tags

dominance bound, deletion window, phase supply, Forgács–Tran branch
-/

namespace ForgacsTran

open Polynomial Set Real

/-! ### `Q'(0) ≠ 0` at the pencil -/

/-- The pencil in the normalized form `Q(0)∏(1 - t/x_j)` that `EventualDegree`'s
coefficient lemmas are stated against. -/
theorem ftRootPoly_eq_normalized {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k) :
    ftRootPoly c a
      = C ((c * ∏ k, a k : ℝ) : ℂ)
        * ∏ k, (1 - C ((((a k)⁻¹ : ℝ)) : ℂ) * X) := by
  have hk : ∀ k : Fin n, (C (((a k : ℝ)) : ℂ) - X)
      = C (((a k : ℝ)) : ℂ) * (1 - C ((((a k)⁻¹ : ℝ)) : ℂ) * X) := by
    intro k
    have hne : (((a k : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (ha k).ne'
    push_cast
    rw [mul_sub, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hne,
      map_one, one_mul]
  rw [ftRootPoly, Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib,
    ← map_prod]
  push_cast
  rw [← mul_assoc, ← map_mul]

theorem ftRootPoly_coeff_zero_ne_zero {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (hc : c ≠ 0)
    (ha : ∀ k, 0 < a k) : (ftRootPoly c a).coeff 0 ≠ 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact eval_ftRootPoly_zero_ne_zero hc ha

theorem ftRootPoly_coeff_one_ne_zero {n : ℕ} {c : ℝ} {a : Fin n → ℝ} (hn : 0 < n)
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) : (ftRootPoly c a).coeff 1 ≠ 0 := by
  rw [ftRootPoly_eq_normalized ha, Polynomial.coeff_C_mul, coeff_one_prod_linear]
  have hsum : (0 : ℝ) < ∑ k, ((a k)⁻¹ : ℝ) := by
    refine Finset.sum_pos (fun k _ => inv_pos.2 (ha k)) ?_
    exact Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  have h1 : ((c * ∏ k, a k : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (mul_ne_zero hc ?_)
    exact Finset.prod_ne_zero_iff.2 fun k _ => (ha k).ne'
  have h2 : (∑ k, ((((a k)⁻¹ : ℝ)) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_ne_zero.2 hsum.ne'
  exact mul_ne_zero h1 (neg_ne_zero.2 h2)

/-! ### `hdom`, composed -/

/-- **What `exists_ftPhaseSupply_of_dominance` asks for, minus `hbranch`.**

The band, the branch's regularity on it, the containment of the amplitude divisor
inside it, and `eq:dominance-bound` off the deleted windows — the bundle every
corner of the grid produces and `exists_ftPhaseSupply_of_dominance` consumes.

`ε` and `σ` are existential because neither appears in `FTPhaseSupply`; `hcol` is a
parameter because it does, so it is threaded rather than bound away.  That
asymmetry is the reason the two are on opposite sides of the binder. -/
def FTDominanceBundle (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (hcol : ℝ) : Prop :=
  ∃ ε σ : ℝ, 0 < ε ∧ 0 < σ ∧ σ < 1 ∧
    Icc ε (π / r - ε) ⊆ Ioo 0 π ∧
    (∀ θ ∈ Icc ε (π / r - ε), 0 < τ θ) ∧
    (∀ θ ∈ Icc ε (π / r - ε),
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
    (∀ θ ∈ Icc ε (π / r - ε),
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
    (∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ Icc ε (π / r - ε)) ∧
    (∃ Md : ℕ, ∀ M : ℕ, Md ≤ M → ∀ θ : ℝ,
      hcol / M ≤ θ → θ ≤ π / r - hcol / M →
      (∀ θj ∈ ftAmplitudeDivisor Q B r z τ ε (π / r - ε),
        ftWindowRadius Q B r z τ ε σ M ≤ |θ - θj|) →
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2)

/-- **The composition, once, at whichever corner supplies the dominance.**

Takes the corner's conclusion in `ft_weighted_dominance_at_any_band`'s shape and
returns the bundle `ftAngularDiscrepancy_of_dominance` asks for, minus `hbranch`.
Both `2 ≤ r` cells of the corner grid go through this; nothing here knows which
corner it came from, which is the point — the `ρ ≥ 2` cell runs at
`ftBranchZLower` and the `ρ = 1` cell at `ftBranchZLowerAt`, and `z` is what lets
one composition serve both.

`ε` is chosen as `min` of the band's and the corner's, and by
`DominanceBandAntitone` that costs nothing on the dominance side. -/
theorem dominance_bundle_of_corner {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ} {z : ℝ → ℝ}
    {B : Polynomial ℂ} {hcol εw : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr1 : 1 ≤ r)
    (_hB : HasRealCoeffs B) (hBev : B.eval 0 ≠ 0)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    (hdata : ∀ ε : ℝ, 0 < ε → ε ≤ π / r - ε →
      ∃ (CI σI AI : ℝ) (S : Finset ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
        (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π / r - ε →
          |ftRemainder (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) M θ|
            ≤ CI * σI ^ M) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ π / r - ε →
          AI * ∏ θj ∈ S, |θ - θj|
              ^ (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))
            ≤ ftPrincipalAmp (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) θ) ∧
        (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj)) ∧
        (∀ θj ∈ S, θj ∈ Icc ε (π / r - ε)))
    (hεw : 0 < εw)
    (H : ∀ ε' : ℝ, 0 < ε' → ε' ≤ εw → ∀ Θ : ℕ → Set ℝ,
      ftInteriorData c a r x₁ z B ε' Θ →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        hcol / M ≤ θ → θ ≤ π / r - hcol / M → θ ∉ Θ M →
          ftRemainder (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) M θ
            ≤ ftPrincipalAmp (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) θ / 2) :
    FTDominanceBundle (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) hcol := by
  classical
  have hn : 0 < n := by omega
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  obtain ⟨εb, hεb, hεblt, hbandb⟩ :=
    exists_band_at_branch (x₁ := x₁) (B := B) hn ha hc hr1 (Or.inl hn2) hz hB0
  -- one `ε` for both, and `min` is what settles it: each constraint wants it small
  set ε : ℝ := min εw εb with hεdef
  have hε : 0 < ε := lt_min hεw hεb
  have hεle : ε ≤ εb := min_le_right _ _
  have hεlew : ε ≤ εw := min_le_left _ _
  have hεlt : ε < π / r - ε := lt_of_le_of_lt hεle (lt_of_lt_of_le hεblt (by linarith))
  -- `hband` at the smaller `ε`: the band only grows
  have hband : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftAmp (ftRootPoly c a) B r ((z θ : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0 →
        θ ∈ Icc ε (π / r - ε) := by
    intro θ hθ hz
    have := hbandb θ hθ hz
    exact ⟨le_trans hεle this.1, le_trans this.2 (by linarith)⟩
  obtain ⟨hτband, hrootb, hsimpleb⟩ :=
    ft_branch_geometry_band (x₁ := x₁) hn ha hc hr1 (Or.inl hn2) hz hε
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :=
    hdata ε hε hεlt.le
  set N : ℕ := max B.natDegree 1 with hN
  set νf : ℝ → ℕ :=
    fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj) with hνf
  -- `S` and the divisor are the same `Finset`
  have hSD : S = ftAmplitudeDivisor (ftRootPoly c a) B r z
      (ftTauArc a r (n - 1) x₁) ε (π / r - ε) :=
    retainedSet_eq_ftAmplitudeDivisor hn2 ha hc hr1 hB0 hz hε hA hband hν hSband hfloor
  have hcount := ftAmplitudeDivisor_count (Q := ftRootPoly c a) (B := B) (r := r)
    (z := z) (τ := ftTauArc a r (n - 1) x₁)
    (lo := ε) (hi := π / r - ε) hB0 (band_subset_Ioo_pi hr1 hε) hτband
  have hνN : ∀ θj ∈ S, νf θj ≤ N := by
    intro θj hθj
    refine le_trans (le_trans ?_ hcount) (le_max_left _ _)
    exact Finset.single_le_sum (f := νf) (fun i _ => Nat.zero_le _) (hSD ▸ hθj)
  -- the deleted family, at the common radius
  -- the band is dictated by `hband` alone: `ft_weighted_dominance_at_any_band`
  -- takes the data at any smaller positive `ε`, so no clause has to be shifted
  obtain ⟨M₀, hM₀⟩ := H ε hε hεlew (amplitudeWindows σI S (fun _ => N))
    ⟨CI, σI, AI, S, νf, hσ0, hσ1, hA, hν, hrem, hfloor,
      amplitudeWindows_meets_interior_clause hσ0 hσ1 hν hνN⟩
  refine ⟨ε, σI, hε, hσ0, hσ1, band_subset_Ioo_pi hr1 hε, hτband, hrootb, hsimpleb,
    hband, ?_⟩
  obtain ⟨Md, hMd⟩ := hdom_of_threshold_form (Q := ftRootPoly c a) (B := B) (r := r)
    (z := z) (τ := ftTauArc a r (n - 1) x₁)
    (S := S) (ν := fun _ => N) (hcol := hcol) (σ := σI) ⟨M₀, hM₀⟩
  refine ⟨Md, fun M hM θ h1 h2 hgap => hMd M hM θ h1 h2 fun θj hθj => ?_⟩
  -- the two radii are one term: `ν` is constant, so the base point is immaterial,
  -- and `S` is the divisor
  refine le_trans (le_of_eq ?_) (hgap θj (hSD ▸ hθj))
  rw [ftWindowRadius, ← hSD, ← hN]
  rfl



/-- **The `ρ ≥ 2`, `2 ≤ r` cell.** -/
theorem exists_dominance_bundle_at_branch {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ hcol : ℝ, 0 < hcol ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        FTDominanceBundle (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
          (ftTauArc a r (n - 1) x₁) hcol := by
  obtain ⟨hcol, hhcol, H0⟩ :=
    ft_weighted_dominance_at_any_band hn2 ha hc hr hx₁ hmin hcard hρ
  refine ⟨hcol, hhcol, fun B hB hBev => ?_⟩
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  obtain ⟨εw, hεw, H⟩ := H0 B hB hBev
  exact dominance_bundle_of_corner hn2 ha hc (by omega) hB hBev
    (fun θ hθ => ftBranchZLower_agree a c r (n - 1) hθ.1)
    (fun ε hε hεb => ft_interior_data_on_band_two_le (x₁ := x₁) (B := B) hn2 ha hc hr
      hB hB0 (fun θ hθ => ftBranchZLower_agree a c r (n - 1) hθ.1) hε hεb) hεw H


/-- **The `ρ = 1`, `2 ≤ r` cell**, through the same composition.  Only the
endpoint and the spectral parameter differ — `ta` in place of `x₁`, and
`ftBranchZLowerAt` in place of `ftBranchZLower` — which is what the `z` parameter
of `dominance_bundle_of_corner` exists for.  Nothing is re-derived.

With this, `hdom` is discharged on the whole `2 ≤ r` half of the corner grid. -/
theorem exists_dominance_bundle_at_branch_rho_one {n r : ℕ} {a : Fin n → ℝ}
    {c : ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ hcol ta : ℝ, 0 < hcol ∧ 0 < ta ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        FTDominanceBundle (ftRootPoly c a) B r
          (ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r))
          (ftTauArc a r (n - 1) ta) hcol := by
  obtain ⟨hcol, hhcol, ta, hta, H0⟩ :=
    ft_weighted_dominance_rho_one_two_le_at_any_band hn2 ha hc hr hmin hsimple
  refine ⟨hcol, ta, hhcol, hta, fun B hB hBev => ?_⟩
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  obtain ⟨εw, hεw, H⟩ := H0 B hB hBev
  exact dominance_bundle_of_corner hn2 ha hc (by omega) hB hBev
    (fun θ hθ => ftBranchZLowerAt_agree a c r (n - 1) _ hθ.1)
    (fun ε hε hεb => ft_interior_data_on_band_two_le (x₁ := ta) (B := B) hn2 ha hc hr
      hB hB0 (fun θ hθ => ftBranchZLowerAt_agree a c r (n - 1) _ hθ.1) hε hεb) hεw H


/-! ### The two `r = 1` cells -/

/-- **The `ρ ≥ 2`, `r = 1` cell.**  `3 ≤ n` is the `(deg Q, r) ≠ (2,1)` exclusion
inherited from `Forgacs2017RationalDenominator` Props. 1--2, which the manuscript
discharges separately in `rem:quadratic-case` rather than assuming.  The corner
quantifies over every admissible `B`, so it fits this bundle with no extra
numerator clause. -/
theorem exists_dominance_bundle_at_branch_one {n ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ hcol : ℝ, 0 < hcol ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        FTDominanceBundle (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
          (ftTauArc a 1 (n - 1) x₁) hcol := by
  obtain ⟨hcol, hhcol, H0⟩ :=
    ft_weighted_dominance_one_at_any_band hn3 ha hc hx₁ hmin hcard hρ
  refine ⟨hcol, hhcol, fun B hB hBev => ?_⟩
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  obtain ⟨εw, hεw, H⟩ := H0 B hB hBev
  refine dominance_bundle_of_corner (r := 1) (by omega) ha hc le_rfl hB hBev
    (fun θ hθ => ftBranchZLower_agree a c 1 (n - 1) hθ.1)
    (fun ε hε hεb => ft_interior_data_on_band_one (x₁ := x₁) (B := B) hn3 ha hc hB hB0
      (fun θ hθ => ftBranchZLower_agree a c 1 (n - 1) hθ.1) hε hεb) hεw ?_
  intro ε' hε' hle Θ hdata
  obtain ⟨M₀, hM₀⟩ := H ε' hε' hle Θ hdata
  exact ⟨M₀, fun M hM θ h1 h2 h3 => hM₀ M hM θ h1 (by simpa using h2) h3⟩

/-- **The `ρ = 1`, `r = 1` cell**, the last of the four.  Its collar constant is
the literal `1`. -/
theorem exists_dominance_bundle_at_branch_rho_one_one {n : ℕ} {a : Fin n → ℝ}
    {c : ℝ} (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        FTDominanceBundle (ftRootPoly c a) B 1
          (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
          (ftTauArc a 1 (n - 1) ta) 1 := by
  obtain ⟨ta, hta, H0⟩ :=
    ft_weighted_dominance_rho_one_at_any_band hn3 ha hc hmin hsimple
  refine ⟨ta, hta, fun B hB hBev => ?_⟩
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  obtain ⟨εw, hεw, H⟩ := H0 B hB hBev
  refine dominance_bundle_of_corner (r := 1) (hcol := 1) (by omega) ha hc le_rfl hB hBev
    (fun θ hθ => ftBranchZLowerAt_agree a c 1 (n - 1) _ hθ.1)
    (fun ε hε hεb => ft_interior_data_on_band_one (x₁ := ta) (B := B) hn3 ha hc hB hB0
      (fun θ hθ => ftBranchZLowerAt_agree a c 1 (n - 1) _ hθ.1) hε hεb) hεw ?_
  intro ε' hε' hle Θ hdata
  obtain ⟨M₀, hM₀⟩ := H ε' hε' hle Θ hdata
  exact ⟨M₀, fun M hM θ h1 h2 h3 => hM₀ M hM θ h1 (by simpa using h2) h3⟩

/-! ### Everything but `hbranch` -/

/-- **`FTPhaseSupply` at the branch, with `hbranch` the only hypothesis left.**

`exists_ftPhaseSupply_of_dominance` leaves two; this closes one of them, so what
is owed for the general pencil at the `2 ≤ ρ`, `2 ≤ r` corner is exactly
`cor:linear-phase-variation`'s conclusion and nothing else.  `hbranch` is stated
here verbatim as that producer states it — it mentions neither `ε` nor `σ`, which
is why it can be hypothesised ahead of the bundle rather than after it.

Nothing about the dominance is assumed: the binders are the admissible class. -/
theorem exists_ftPhaseSupply_at_branch_of_branchSupply {n r ρ : ℕ} {a : Fin n → ℝ}
    {c x₁ κ₀ κ₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (B : Polynomial ℂ) (hB : HasRealCoeffs B) (hBev : B.eval 0 ≠ 0)
    (hbranch : ∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc 0 (π / r)) → (∀ i, Rb i ∈ Icc 0 (π / r)) →
      (∀ i j, i < j → Rb i ≤ Lb j) →
      (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / r)) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
        ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0) →
      ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)
            = ((ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
                (ftTauArc a r (n - 1) x₁) θ : ℝ) : ℂ)
              * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
        (∀ i, 0 ≤ varψ i) ∧
        (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
        ∑ i, varψ i ≤ κ₀ + κ₁ * B.natDegree) :
    ∃ hcol : ℝ, 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
        (ftTauArc a r (n - 1) x₁) hcol κ₀ κ₁ M := by
  obtain ⟨hcol, hhcol, Hb⟩ :=
    exists_dominance_bundle_at_branch (x₁ := x₁) hn2 ha hc hr hx₁ hmin hcard hρ
  obtain ⟨ε, σ, hε, hσ0, hσ1, hεband, hτ, hroot, hsimple, hband, hdom⟩ := Hb B hB hBev
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact ⟨hcol, hhcol,
    exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB hr1
      (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
      (ftRootPoly_coeff_one_ne_zero hn hc.ne' ha) hB0 hBev hσ0 hσ1 hhcol hεband hτ
      hroot hsimple hband hdom hbranch⟩


/-- **The supply at the `ρ ≥ 2`, `r = 1` cell.** -/
theorem exists_ftPhaseSupply_at_branch_one_of_branchSupply {n ρ : ℕ} {a : Fin n → ℝ}
    {c x₁ κ₀ κ₁ : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (B : Polynomial ℂ) (hB : HasRealCoeffs B) (hBev : B.eval 0 ≠ 0)
    (hbranch :
      (∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
        (∀ i, Lb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) → (∀ i, Rb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) →
        (∀ i j, i < j → Rb i ≤ Lb j) →
        (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ))) →
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          ftAmp (ftRootPoly c a) B 1 (((ftBranchZLower a c 1 (n - 1)) θ : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θ) ≠ 0) →
        ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
          (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
            ftAmp (ftRootPoly c a) B 1 (((ftBranchZLower a c 1 (n - 1)) θ : ℝ) : ℂ)
              (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θ)
              = ((ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
                  (ftTauArc a 1 (n - 1) x₁) θ : ℝ) : ℂ)
                * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
          (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
          (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
          (∀ i, 0 ≤ varψ i) ∧
          (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
          ∑ i, varψ i ≤ κ₀ + κ₁ * B.natDegree)) :
    ∃ hcol : ℝ, 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FTPhaseSupply (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
        (ftTauArc a 1 (n - 1) x₁) hcol κ₀ κ₁ M := by
  obtain ⟨hcol, hhcol, Hb⟩ :=
    exists_dominance_bundle_at_branch_one (x₁ := x₁) hn3 ha hc hx₁ hmin hcard hρ
  obtain ⟨ε, σ, hε, hσ0, hσ1, hεband, hτ, hroot, hsimple, hband, hdom⟩ := Hb B hB hBev
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact ⟨hcol, hhcol,
    exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB le_rfl
      (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
      (ftRootPoly_coeff_one_ne_zero (by omega) hc.ne' ha) hB0 hBev hσ0 hσ1 hhcol
      hεband hτ hroot hsimple hband hdom hbranch⟩

/-- **The supply at the `ρ = 1`, `2 ≤ r` cell.**  `ta` is produced by the pencil,
so `hbranch` is bound after it rather than ahead of the statement. -/
theorem exists_ftPhaseSupply_at_branch_rho_one_of_branchSupply {n r : ℕ}
    {a : Fin n → ℝ} {c κ₀ κ₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        (∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
          (∀ i, Lb i ∈ Icc 0 (π / r)) → (∀ i, Rb i ∈ Icc 0 (π / r)) →
          (∀ i j, i < j → Rb i ≤ Lb j) →
          (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / r)) →
          (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
            ftAmp (ftRootPoly c a) B r (((ftBranchZLowerAt a c r (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ r)) θ : ℝ) : ℂ)
              (ftPrincipal (ftTauArc a r (n - 1) ta) θ) ≠ 0) →
          ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
              ftAmp (ftRootPoly c a) B r (((ftBranchZLowerAt a c r (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ r)) θ : ℝ) : ℂ)
                (ftPrincipal (ftTauArc a r (n - 1) ta) θ)
                = ((ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLowerAt a c r (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ r))
                    (ftTauArc a r (n - 1) ta) θ : ℝ) : ℂ)
                  * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
            (∀ i, 0 ≤ varψ i) ∧
            (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
            ∑ i, varψ i ≤ κ₀ + κ₁ * B.natDegree) →
        ∃ hcol : ℝ, 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
          FTPhaseSupply (ftRootPoly c a) B r
            (ftBranchZLowerAt a c r (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ r))
            (ftTauArc a r (n - 1) ta) hcol κ₀ κ₁ M := by
  obtain ⟨hcol, ta, hhcol, hta, Hb⟩ :=
    exists_dominance_bundle_at_branch_rho_one hn2 ha hc hr hmin hsimple
  refine ⟨ta, hta, fun B hB hBev hbranch => ?_⟩
  obtain ⟨ε, σ, hε, hσ0, hσ1, hεband, hτ, hroot, hsimple', hband, hdom⟩ := Hb B hB hBev
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact ⟨hcol, hhcol,
    exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB (by omega)
      (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
      (ftRootPoly_coeff_one_ne_zero (by omega) hc.ne' ha) hB0 hBev hσ0 hσ1 hhcol
      hεband hτ hroot hsimple' hband hdom hbranch⟩

/-- **The supply at the `ρ = 1`, `r = 1` cell**, the last of the four. -/
theorem exists_ftPhaseSupply_at_branch_rho_one_one_of_branchSupply {n : ℕ}
    {a : Fin n → ℝ} {c κ₀ κ₁ : ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {i : Fin n} (hmin : ∀ k, a i ≤ a k) (hsimple : ∀ k, k ≠ i → a k ≠ a i) :
    ∃ ta : ℝ, 0 < ta ∧
      ∀ B : Polynomial ℂ, HasRealCoeffs B → B.eval 0 ≠ 0 →
        (∃ Mb : ℕ, ∀ M : ℕ, Mb ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
          (∀ i, Lb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) → (∀ i, Rb i ∈ Icc 0 (π / ((1 : ℕ) : ℝ))) →
          (∀ i j, i < j → Rb i ≤ Lb j) →
          (∀ i, Lb i < Rb i → Icc (Lb i) (Rb i) ⊆ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ))) →
          (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
            ftAmp (ftRootPoly c a) B 1 (((ftBranchZLowerAt a c 1 (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) θ : ℝ) : ℂ)
              (ftPrincipal (ftTauArc a 1 (n - 1) ta) θ) ≠ 0) →
          ∃ (ψ dψ : Fin k → ℝ → ℝ) (varψ : Fin k → ℝ),
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
              ftAmp (ftRootPoly c a) B 1 (((ftBranchZLowerAt a c 1 (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ 1)) θ : ℝ) : ℂ)
                (ftPrincipal (ftTauArc a 1 (n - 1) ta) θ)
                = ((ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZLowerAt a c 1 (n - 1)
                      (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
                    (ftTauArc a 1 (n - 1) ta) θ : ℝ) : ℂ)
                  * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
            (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) ∧
            (∀ i, 0 ≤ varψ i) ∧
            (∀ i, Lb i < Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
            ∑ i, varψ i ≤ κ₀ + κ₁ * B.natDegree) →
        ∃ hcol : ℝ, 0 < hcol ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
          FTPhaseSupply (ftRootPoly c a) B 1
            (ftBranchZLowerAt a c 1 (n - 1)
            (-((ftRootPolyReal c a).eval ta) / ta ^ 1))
            (ftTauArc a 1 (n - 1) ta) hcol κ₀ κ₁ M := by
  obtain ⟨ta, hta, Hb⟩ :=
    exists_dominance_bundle_at_branch_rho_one_one hn3 ha hc hmin hsimple
  refine ⟨ta, hta, fun B hB hBev hbranch => ?_⟩
  obtain ⟨ε, σ, hε, hσ0, hσ1, hεband, hτ, hroot, hsimple', hband, hdom⟩ := Hb B hB hBev
  have hB0 : B ≠ 0 := fun h0 => hBev (by rw [h0]; simp)
  exact ⟨1, one_pos,
    exists_ftPhaseSupply_of_dominance (hasRealCoeffs_ftRootPoly c a) hB le_rfl
      (ftRootPoly_coeff_zero_ne_zero hc.ne' ha)
      (ftRootPoly_coeff_one_ne_zero (by omega) hc.ne' ha) hB0 hBev hσ0 hσ1 one_pos
      hεband hτ hroot hsimple' hband hdom hbranch⟩

end ForgacsTran
