/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.WeightedDominanceBranch
import ForgacsTran.InteriorSeparation
import ForgacsTran.InteriorSupply
import ForgacsTran.FTGeometryCone

/-!
# `thm:FT-geometry`'s minimum modulus, in the shape the separation cover consumes

`InteriorSeparation.exists_finite_separation_cover` takes the pointwise separation
`hmin` — every denominator zero other than the principal pair has `τ(θ) < ‖w‖` —
and turns it into a finite cover of a compact interior by subarcs, each with its
own separating radius.  `FTGeometryCone.ft_minModulus_at_branch_two_le` proves
that separation at the branch, unconditionally, for every `r ≥ 2`.

The two do not meet as they stand, and the gap is entirely one of spelling: the
producer is stated at `ftBranchZ`, `ftTau` and the conjugate written
`conj (ftPrincipal τ θ)`, while the two-endpoint composition of
`WeightedDominanceBranch` runs at `ftBranchZLower`, `ftTauArc` and the conjugate
written `τ(θ)e^{-iθ}`.  Every one of those four is an equality that already has a
name — `ftBranchZLower_agree`, `ftTauArc_agree`, `ftPrincipal_congr` and
`conj_ftPrincipal'` — and each holds exactly on the open arc, which is where a
compact interior `[ε, π/r - ε]` sits.

So no bridging mathematics is needed, only the rewrites, and this module does them
once so the interior producer does not have to.

## Main statements

* `ft_separation_hmin_interior` — `hmin` on `[ε, π/r - ε]` at the composition's own
  spectral parameter and radius.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`,
  `subsec:proof`.

## Tags

minimum modulus, separation, interior supply, Forgács–Tran branch
-/

namespace ForgacsTran

open Polynomial
open scoped Topology

/-- **`exists_finite_separation_cover`'s `hmin` at the branch, `r ≥ 2`**, in the
spectral parameter and radius the two-endpoint composition uses.

The interval is `[ε, π/r - ε]` with `ε > 0`, which is where the composition's own
interior antecedent lives; on it every point is interior to the viewing arc, so the
arc radius is the branch radius and the lower spectral parameter is the branch's. -/
theorem ft_separation_hmin_interior {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ θ ∈ Set.Icc ε (Real.pi / r - ε), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTauArc a r (n - 1) x₁) θ →
        w ≠ ((ftTauArc a r (n - 1) x₁ θ : ℝ) : ℂ)
          * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) →
        ftTauArc a r (n - 1) x₁ θ < ‖w‖ := by
  intro θ hθ w hroot hne1 hne2
  have hθ0 : 0 < θ := lt_of_lt_of_le hε hθ.1
  have hθb : θ < Real.pi / r := lt_of_le_of_lt hθ.2 (by linarith)
  -- the arc radius is the branch radius here, and so are the two principal points
  have hτ : ftTauArc a r (n - 1) x₁ θ = ftTau a r (n - 1) θ :=
    ftTauArc_agree a r (n - 1) x₁ hθ0 hθb
  have hP : ftPrincipal (ftTauArc a r (n - 1) x₁) θ
      = ftPrincipal (ftTau a r (n - 1)) θ := ftPrincipal_congr hτ
  have hz : ftBranchZLower a c r (n - 1) θ = ftBranchZ a c r (n - 1) θ :=
    ftBranchZLower_agree a c r (n - 1) hθ0
  rw [hτ]
  refine ft_minModulus_at_branch_two_le hn2 ha hc hr θ ⟨hθ0, hθb⟩ w ?_ ?_ ?_
  · rwa [hz] at hroot
  · rwa [hP] at hne1
  · rw [conj_ftPrincipal' (ftTau a r (n - 1)) θ]
    rwa [hτ] at hne2

/-- **The interior data of `subsec:proof` at the branch, `r ≥ 2`, unconditional.**

`InteriorSupply.exists_interior_data_on_subinterval` takes the pointwise
separation as its only geometric input and produces the remainder bound and the
amplitude floor on the whole subinterval — it runs the separation cover and
`interior_data_of_pieces` internally, so the finite cover is not something a
caller assembles.  With `ft_minModulus_at_branch_two_le` supplying that input
unconditionally at every `r ≥ 2`, the interior data at the branch follows with no
hypothesis beyond the admissible class.

Stated at `ftBranchZLower`, which is the spectral parameter the two-endpoint
composition uses; on `[ε, π/r - ε]` it agrees with `ftBranchZ` pointwise. -/
theorem ft_interior_data_of_minModulus {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hεb : ε ≤ Real.pi / r - ε)
    (hminmod : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / r), ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
        w ≠ ftPrincipal (ftTau a r (n - 1)) θ →
        w ≠ (starRingEnd ℂ) (ftPrincipal (ftTau a r (n - 1)) θ) →
        ftTau a r (n - 1) θ < ‖w‖) :
    FTInteriorData (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
      (ftTauArc a r (n - 1) x₁) ε (Real.pi / r - ε) := by
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have harc : Set.Icc ε (Real.pi / r - ε) ⊆ Set.Ioo (0 : ℝ) (Real.pi / r) := by
    intro θ hθ
    exact ⟨lt_of_lt_of_le hε hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  have hz : ∀ θ : ℝ, ε ≤ θ → θ ≤ Real.pi / r - ε →
      ftBranchZLower a c r (n - 1) θ = ftBranchZ a c r (n - 1) θ :=
    fun θ h1 _ => ftBranchZLower_agree a c r (n - 1) (lt_of_lt_of_le hε h1)
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :=
    exists_interior_data_on_subinterval (a := a) (c := c) (B := B)
      (τ := ftTauArc a r (n - 1) x₁) hn ha hc hr1 (Or.inl hn2) hB hB0
      (fun θ hθ => ftTauArc_agree a r (n - 1) x₁ hθ.1 hθ.2) hεb harc
      (fun θ hθ w hroot hne1 hne2 => by
        have hθ0 : 0 < θ := (harc hθ).1
        have hθb : θ < Real.pi / r := (harc hθ).2
        have hτ : ftTauArc a r (n - 1) x₁ θ = ftTau a r (n - 1) θ :=
          ftTauArc_agree a r (n - 1) x₁ hθ0 hθb
        have hP : ftPrincipal (ftTauArc a r (n - 1) x₁) θ
            = ftPrincipal (ftTau a r (n - 1)) θ := ftPrincipal_congr hτ
        rw [hτ]
        refine hminmod θ ⟨hθ0, hθb⟩ w hroot ?_ ?_
        · rwa [hP] at hne1
        · rw [conj_ftPrincipal' (ftTau a r (n - 1)) θ]
          rwa [hτ] at hne2)
  refine ⟨CI, σI, AI, S, hσ0, hσ1, hA, fun M θ h1 h2 => ?_, fun θ h1 h2 => ?_, hν, hSband⟩
  · simpa [ftRemainder, hz θ h1 h2] using hrem M θ h1 h2
  · simpa [ftPrincipalAmp, hz θ h1 h2] using hfloor θ h1 h2

/-- **The interior data at `2 ≤ r`**, with the separation supplied by
`FTGeometryCone.ft_minModulus_at_branch_two_le`. -/
theorem ft_interior_data_on_arc_two_le {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hεb : ε ≤ Real.pi / r - ε) :
    FTInteriorData (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
      (ftTauArc a r (n - 1) x₁) ε (Real.pi / r - ε) :=
  ft_interior_data_of_minModulus (x₁ := x₁) hn2 ha hc (by omega) hB hB0 hε hεb
    (ft_minModulus_at_branch_two_le hn2 ha hc hr)

/-- **The interior data at `r = 1`, at every multiplicity.**  The separation is
`FTMinModulus.RealCritical.ft_minModulus_at_branch_pi`, which is unconditional on
the admissible class with `3 ≤ n` — Forgács–Tran's own `(deg Q, r) ≠ (2,1)` — and
puts no restriction on the multiplicity of any zero.

This is the interior half of the `r = 1` corner of `subsec:proof`.  Nothing about
the *endpoints* at `r = 1` follows from it: there the upper endpoint is finite
rather than at the origin, and its retained set and amplitude floor are separate
work. -/
theorem ft_interior_data_on_arc_one {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hεb : ε ≤ Real.pi / ((1 : ℕ) : ℝ) - ε) :
    FTInteriorData (ftRootPoly c a) B 1 (ftBranchZLower a c 1 (n - 1))
      (ftTauArc a 1 (n - 1) x₁) ε (Real.pi / ((1 : ℕ) : ℝ) - ε) :=
  ft_interior_data_of_minModulus (x₁ := x₁) (by omega) ha hc (le_refl 1) hB hB0 hε hεb
    (ft_minModulus_at_branch_pi hn3 ha hc)

/-- **`thm:weighted-dominance` at the branch, one corner of four, with nothing
assumed on that corner.**  `2 ≤ n`, positive zeros, `0 < c`, `2 ≤ r`, the smallest
zero carried with multiplicity `ρ ≥ 2`, and `B(0) ≠ 0` give `eq:dominance-bound`
on `eq:retained-range`, away from the amplitude's zeros — with no interior
hypothesis, no separating radius and no deleted family assumed.

**The manuscript claims more, and the difference is scope rather than strength.**
`eq:Q-hypotheses` allows multiplicities without restriction and takes `r ≥ 1`, and
`subsec:proof` walks four corners: the lower endpoint retains the principal pair
when the smallest zero is simple and the full `ρ`-root cluster when `ρ > 1`; the
upper endpoint retains the principal pair at `r = 1` and the `r`-root cluster at
`r > 1`.  This theorem is the `ρ > 1`, `r > 1` corner, and
`WeightedDominanceBranchOne.ft_weighted_dominance_one_unconditional` is the
`ρ > 1`, `r = 1` one at `n = 3`.  Neither is the other with a hypothesis
relaxed, which is why each needed its own upper block:
`Cluster.clusterAlpha_one_eq_zero` and `hEp_false_of_rho_one` show the
lower endpoint's slope datum degenerates and one of its binders goes false at
`ρ = 1`, and at `r = 1` the upper endpoint is finite rather than at the origin, so
the amplitude floor takes the other of the two routes `eq:ab-def` distinguishes.
`exists_lower_endpoint_block` already covers every `r ≥ 1`, which is why the
`r = 1` corner needed a new upper block only.  The two `ρ = 1` corners remain
unformalized.

**The deleted family is written out, not existentially quantified.**  An
`∃ Θ : ℕ → Set ℝ` form of this statement would be trivially true — `Θ M := univ`
makes `θ ∉ Θ M` unsatisfiable and every instance of the bound vacuous — so the
windows appear here as `eq:amplitude-deletion`'s own inequality: `θ` is admitted
when it is at distance at least `exp(-((-log σ)/(2|S|)·M/ν_j))` from each divisor
point.  The abstract form can afford `∀ Θ` because it quantifies over every
admissible family; an unconditional statement has to produce one, and producing it
is what loses the content unless the family is named.

`h` is quantified **before** `B`, as `h = h(Q,r)` in the paper: it is built from
the two cluster gap coefficients and the two cluster sizes, none of which sees the
numerator.  `S`, `σ` and `M₀` come after it and do depend on `B`, which is the
paper's `M_0(Q,r,B)` and `c(Q,r,B)`.

`S` is pinned by the clause `1 ≤ B.rootMultiplicity (t_+(θ_j))`: every divisor
point is an angle where `B` vanishes at the principal point, so `S` cannot be
inflated into a grid that makes the distance hypothesis unmeetable — `B` has
finitely many zeros.  With `σ < 1` the exponent is positive, so the windows shrink
as `M` grows. -/
theorem ft_weighted_dominance_unconditional {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ h > (0 : ℝ), ∀ (B : Polynomial ℂ), HasRealCoeffs B → B.eval 0 ≠ 0 →
      ∃ (S : Finset ℝ) (σ : ℝ), 0 < σ ∧ σ < 1
      ∧ (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))
      ∧ (∀ θj ∈ S, θj ∈ Set.Ioo (0 : ℝ) (Real.pi / r))
      ∧ (∃ K > (0 : ℝ), ∃ cdec > (0 : ℝ), ∀ M : ℕ,
          ∑ θj ∈ S, 2 * Real.exp (-((-Real.log σ) / (2 * S.card) * M
              / (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))))
            ≤ K * Real.exp (-cdec * M))
      ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ Real.pi / r - h / M →
        (∀ θj ∈ S, Real.exp (-((-Real.log σ) / (2 * S.card) * M
            / (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj)))) ≤ |θ - θj|) →
          ftRemainder (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
              (ftTauArc a r (n - 1) x₁) M θ
            ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
              (ftTauArc a r (n - 1) x₁) θ / 2 := by
  classical
  obtain ⟨h, hh, H0⟩ := ft_weighted_dominance hn2 ha hc hr hx₁ hmin hcard hρ
  refine ⟨h, hh, fun B hB hB0 => ?_⟩
  have hB0' : B ≠ 0 := fun h0 => hB0 (by rw [h0]; simp)
  obtain ⟨ε, hε, H⟩ := H0 B hB hB0
  -- the interior data at that `ε`, produced rather than assumed; the window may be
  -- empty, and then every interior clause is vacuous and the divisor is too
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :
      FTInteriorData (ftRootPoly c a) B r (ftBranchZLower a c r (n - 1))
        (ftTauArc a r (n - 1) x₁) ε (Real.pi / r - ε) := by
    by_cases hεb : ε ≤ Real.pi / r - ε
    · exact ft_interior_data_on_arc_two_le hn2 ha hc hr hB hB0' hε hεb
    · exact ⟨1, 1 / 2, 1, ∅, by norm_num, by norm_num, by norm_num,
        fun M θ h1 h2 => absurd (le_trans h1 h2) hεb,
        fun θ h1 h2 => absurd (le_trans h1 h2) hεb, by simp, by simp⟩
  -- `eq:amplitude-deletion`'s collars, as the set the abstract form quantifies over
  obtain ⟨M₀, hM₀⟩ :=
    H (fun M => {θ : ℝ | ∃ θj ∈ S, |θ - θj| < Real.exp (-((-Real.log σI)
        / (2 * S.card) * M / (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))))})
      ⟨CI, σI, AI, S, fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj),
        hσ0, hσ1, hA, hν, hrem, hfloor, fun M θ hθ θj hθj => by
          by_contra hlt
          exact hθ ⟨θj, hθj, not_le.1 hlt⟩⟩
  have hSarc : ∀ θj ∈ S, θj ∈ Set.Ioo (0 : ℝ) (Real.pi / r) := by
    intro θj hθj
    have hb := hSband θj hθj
    exact ⟨lt_of_lt_of_le hε hb.1, lt_of_le_of_lt hb.2 (by linarith)⟩
  refine ⟨S, σI, hσ0, hσ1, hν, hSarc, ?_, M₀, fun M hM θ h1 h2 hfar => ?_⟩
  · -- `eq:amplitude-deletion`'s windows have exponentially small total length: each
    -- has length `2exp(-κM/ν_j)`, the largest multiplicity gives the slowest decay,
    -- and there are `|S|` of them
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · exact ⟨1, one_pos, 1, one_pos, fun M => by simp only [Finset.sum_empty]; positivity⟩
    have hcard0 : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 hSne
    have hlog : 0 < -Real.log σI := by
      have := Real.log_neg hσ0 hσ1; linarith
    set κ : ℝ := (-Real.log σI) / (2 * S.card) with hκ
    have hκ0 : 0 < κ := div_pos hlog (by linarith)
    set mult : ℝ → ℕ :=
      fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj) with hmult
    set N : ℕ := S.sup mult with hN
    obtain ⟨θ0, hθ0⟩ := hSne
    have hN1 : 1 ≤ N := le_trans (hν θ0 hθ0) (Finset.le_sup (f := mult) hθ0)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
    refine ⟨2 * S.card, by linarith, κ / N, div_pos hκ0 hNR, fun M => ?_⟩
    have hterm : ∀ θj ∈ S,
        2 * Real.exp (-(κ * M / (mult θj))) ≤ 2 * Real.exp (-(κ / N * M)) := by
      intro θj hθj
      have hνj : 0 < (mult θj : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hν θj hθj)
      have hle : (mult θj : ℝ) ≤ N := by
        exact_mod_cast Finset.le_sup (f := mult) hθj
      have hMnn : (0 : ℝ) ≤ κ * M := by positivity
      have : κ * M / N ≤ κ * M / (mult θj) := div_le_div_of_nonneg_left hMnn hνj hle
      have hexp := Real.exp_le_exp.2 (neg_le_neg this)
      calc 2 * Real.exp (-(κ * M / (mult θj)))
          ≤ 2 * Real.exp (-(κ * M / N)) := by linarith [hexp]
        _ = 2 * Real.exp (-(κ / N * M)) := by ring_nf
    calc ∑ θj ∈ S, 2 * Real.exp (-(κ * M / (mult θj)))
        ≤ ∑ _θj ∈ S, 2 * Real.exp (-(κ / N * M)) := Finset.sum_le_sum hterm
      _ = 2 * S.card * Real.exp (-(κ / N * M)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ = 2 * S.card * Real.exp (-(κ / N) * M) := by ring_nf
  refine hM₀ M hM θ h1 h2 fun hmem => ?_
  obtain ⟨θj, hθj, hlt⟩ := hmem
  exact absurd (hfar θj hθj) (not_le.2 hlt)

end ForgacsTran
