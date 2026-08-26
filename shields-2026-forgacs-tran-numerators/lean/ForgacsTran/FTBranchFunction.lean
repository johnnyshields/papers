/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchTauDeriv
import ForgacsTran.FTBranchExistence

/-!
# The branch radius as a function of `θ`

`FTBranchExistence` settles the branch pointwise in `θ`; the consumers of
`thm:FT-geometry` need it as a function of `θ`.  This module names that function
and proves it continuous.

## Main statements

* `FTBranchAt` — solvability of the branch equation at one angle.
* `ftTau` — the radius `τ(θ)` of `Forgacs2017RationalDenominator` Lemma 2, and
  `ftBranchAngle` the angles `θ_k(θ)` built on it.
* `ftTau_eq_of` — anything solving the branch equation *is* `ftTau`, so no
  statement below depends on the choice made in the definition.
* `ftBranchAt_of_arc_principal` — at `l = n - 1` solvability holds across the
  whole arc, so nothing downstream carries it as a hypothesis.
* `continuousAt_ftTau` — continuity, from the strict monotonicity in `τ` and
  continuity in `θ` alone; no derivative is used.

## Implementation notes

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

branch radius, continuity, Forgacs-Tran branch
-/

namespace ForgacsTran

open Real Set Filter Topology

/-- The viewing arc `(0, π/r)` sits inside `(0, π)`. -/
theorem ftArc_subset {r : ℕ} (hr : 1 ≤ r) : Ioo 0 (π / r) ⊆ Ioo 0 π := by
  intro s hs
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  refine ⟨hs.1, ?_⟩
  have := (lt_div_iff₀ hr0).1 hs.2
  nlinarith [hs.1]

theorem ftAngleSum_le_of_le {n : ℕ} {a : Fin n → ℝ} {τ₁ τ₂ θ : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hθ : θ ∈ Ioo 0 π) (hτ₁ : 0 < τ₁) (hle : τ₁ ≤ τ₂) :
    ftAngleSum a τ₂ θ ≤ ftAngleSum a τ₁ θ := by
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]
  · exact (ftAngleSum_lt hn ha hθ hτ₁ h).le

/-- The branch equation of `Forgacs2017RationalDenominator` Lemma 2 (ii) is
solvable at `θ`. -/
def FTBranchAt {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : Prop :=
  ∃ τ : ℝ, 0 < τ ∧ ftAngleSum a τ θ = r * θ + l * π

open scoped Classical in
/-- `τ(θ)`, the branch radius.  Off the arc the value is junk; every statement
about it carries `FTBranchAt`, and `ftTau_eq_of` shows the choice is forced. -/
noncomputable def ftTau {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  if h : FTBranchAt a r l θ then h.choose else 1

/-- `θ_k(θ)`, the branch angles. -/
noncomputable def ftBranchAngle {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (k : Fin n) (θ : ℝ) : ℝ :=
  ftAngle (a k) (ftTau a r l θ) θ

theorem ftTau_pos {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} {θ : ℝ} (h : FTBranchAt a r l θ) :
    0 < ftTau a r l θ := by
  rw [ftTau, dif_pos h]
  exact h.choose_spec.1

theorem ftAngleSum_ftTau {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} {θ : ℝ} (h : FTBranchAt a r l θ) :
    ftAngleSum a (ftTau a r l θ) θ = r * θ + l * π := by
  rw [ftTau, dif_pos h]
  exact h.choose_spec.2

/-- Solvability on the arc, from `Forgacs2017RationalDenominator` Lemma 2. -/
theorem ftBranchAt_of_arc {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hl : l < n) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r))
    (hrange : (n : ℝ) * θ < r * θ + l * π) : FTBranchAt a r l θ := by
  obtain ⟨⟨τ, φ⟩, ⟨hτ, hφ, hsum, hratio⟩, -⟩ :=
    exists_unique_ftAngleSystem_pencil hn ha hr hl hθ.1 hθ.2 hrange
  refine ⟨τ, hτ, ?_⟩
  have hφeq : ∀ k, φ k = ftAngle (a k) τ θ := fun k =>
    ftAngle_unique hτ (ftArc_subset hr hθ) (hφ k) (hratio k)
  simpa [ftAngleSum, ← hφeq] using hsum

/-- **Solvability across the whole arc at `l = n - 1`.**  This discharges the
hypothesis every statement about `ftTau` would otherwise carry: at the index
`Forgacs2017RationalDenominator` Remark 4 selects there is nothing to assume
beyond positive zeros.  The hypothesis `2 ≤ n ∨ 2 ≤ r` excludes only `n = r = 1`,
where the branch genuinely does not exist — there `∑_k θ_k = θ` forces `θ₁ = θ`
against clause (i). -/
theorem ftBranchAt_of_arc_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    FTBranchAt a r (n - 1) θ :=
  ftBranchAt_of_arc hn ha hr (by omega) hθ
    (ftAngleSum_range_of_eq_sub_one hn hr hnr hθ.1 hθ.2)

/-- **The choice in the definition is forced.**  Anything solving the branch
equation equals `ftTau`. -/
theorem ftTau_eq_of {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    {θ τ : ℝ} (hθ : θ ∈ Ioo 0 π) (hτ : 0 < τ)
    (hsum : ftAngleSum a τ θ = r * θ + l * π) : τ = ftTau a r l θ := by
  have hb : FTBranchAt a r l θ := ⟨τ, hτ, hsum⟩
  have h1 := ftTau_pos hb
  have h2 := ftAngleSum_ftTau hb
  rcases lt_trichotomy τ (ftTau a r l θ) with h | h | h
  · have := ftAngleSum_lt hn ha hθ hτ h
    rw [hsum, h2] at this
    exact absurd this (lt_irrefl _)
  · exact h
  · have := ftAngleSum_lt hn ha hθ h1 h
    rw [hsum, h2] at this
    exact absurd this (lt_irrefl _)

/-- The branch angles satisfy the three clauses of
`Forgacs2017RationalDenominator` Lemma 2 pointwise. -/
theorem ftBranchAngle_spec {n : ℕ} {a : Fin n → ℝ} {r l : ℕ} (ha : ∀ k, 0 < a k) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) (h : FTBranchAt a r l θ) :
    (∀ k, ftBranchAngle a r l k θ ∈ Ioo θ π) ∧
      (∑ k, ftBranchAngle a r l k θ) = r * θ + l * π ∧
      (∀ k, a k * Real.sin (ftBranchAngle a r l k θ)
        = ftTau a r l θ * Real.sin (ftBranchAngle a r l k θ - θ)) :=
  ⟨fun k => ftAngle_mem_Ioo (ha k) (ftTau_pos h) hθ,
   ftAngleSum_ftTau h,
   fun _k => ftAngle_spec (ne_of_gt (ftTau_pos h)) hθ⟩

/-- **`τ(θ)` is continuous.**  Only the strict monotonicity in `τ` and the
continuity in `θ` at fixed `τ` are used. -/
theorem continuousAt_ftTau {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    ContinuousAt (ftTau a r l) θ₀ := by
  have hθ₀π : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hb₀ := hb θ₀ hθ₀
  have hτ₀ : 0 < ftTau a r l θ₀ := ftTau_pos hb₀
  have harc : ∀ᶠ θ in 𝓝 θ₀, θ ∈ Ioo 0 (π / r) := isOpen_Ioo.mem_nhds hθ₀
  have hcont : ∀ c : ℝ, 0 < c →
      ContinuousAt (fun θ => ftAngleSum a c θ - ((r : ℝ) * θ + l * π)) θ₀ := fun c hc =>
    ((hasDerivAt_ftAngleSum_angle ha hc hθ₀π).continuousAt).sub
      (((continuous_const.mul continuous_id).add continuous_const).continuousAt)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    rcases le_or_gt c 0 with hc0 | hc0
    · filter_upwards [harc] with θ hθ using lt_of_le_of_lt hc0 (ftTau_pos (hb θ hθ))
    · -- `0 < c < τ₀`: the angle sum at `c` overshoots at `θ₀`, hence nearby
      have hgt : (r : ℝ) * θ₀ + l * π < ftAngleSum a c θ₀ := by
        have := ftAngleSum_lt hn ha hθ₀π hc0 hc
        rwa [ftAngleSum_ftTau hb₀] at this
      have hpos₀ : 0 < ftAngleSum a c θ₀ - ((r : ℝ) * θ₀ + l * π) := by linarith
      filter_upwards [harc, (hcont c hc0).eventually (eventually_gt_nhds hpos₀)]
        with θ hθ hpos
      by_contra hcon
      push Not at hcon
      have hle := ftAngleSum_le_of_le hn ha (ftArc_subset hr hθ) (ftTau_pos (hb θ hθ)) hcon
      rw [ftAngleSum_ftTau (hb θ hθ)] at hle
      linarith
  · intro c hc
    have hc0 : 0 < c := lt_trans hτ₀ hc
    have hlt : ftAngleSum a c θ₀ < (r : ℝ) * θ₀ + l * π := by
      have := ftAngleSum_lt hn ha hθ₀π hτ₀ hc
      rwa [ftAngleSum_ftTau hb₀] at this
    have hneg₀ : ftAngleSum a c θ₀ - ((r : ℝ) * θ₀ + l * π) < 0 := by linarith
    filter_upwards [harc, (hcont c hc0).eventually (eventually_lt_nhds hneg₀)] with θ hθ hneg
    by_contra hcon
    push Not at hcon
    have hle := ftAngleSum_le_of_le hn ha (ftArc_subset hr hθ) hc0 hcon
    rw [ftAngleSum_ftTau (hb θ hθ)] at hle
    linarith

end ForgacsTran
