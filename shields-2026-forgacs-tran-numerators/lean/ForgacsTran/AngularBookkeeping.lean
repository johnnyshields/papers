/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# The angular bookkeeping of `subsec:proof`

The bookkeeping the counting argument of `prop:angular-discrepancy` runs on, none of which
needs the analysis: the reparametrization, the block count, the monotonicity of `Φ_M`, and
the deleted family of `eq:amplitude-deletion` with its negligibility.

## Main statements

* `image_Ioo_eq_Ioo` — `eq:angular-subinterval`: `I_{α,β} = z((α, β))` is the open interval
  between the endpoint values, so an angular count **is** a `z`-count.  This is what lets
  `ClauseThree.exists_phaseZeros` keep the phase in `θ` and the zeros in `z(θ)`.
* `subset_ftInterval_image` — the same subinterval sits inside `I_{Q,r} = z((0, π/r))`.
* `card_blocks_le` — `eq:Omega-M`: deleting `J` windows leaves at most `J + 1` retained
  blocks, because distinct gaps carry distinct windows.  This is the `s.card ≤ K + 1` input of
  `ClauseThree.angular_distinct_lower`, once `eq:amplitude-zero-count` gives `J ≤ K`.
* `strictMonoOn_phase` — `eq:Phi-def`: `Φ_M(θ) = (M+1)θ - ψ(θ)` is strictly increasing once
  `M + 1` exceeds the phase-derivative bound `κ` of `eq:phase-derivative-bound`.  This is the
  `hΦm` input of `ClauseThree.PhaseSupply`, and it is where the threshold in `M` is allowed to
  depend on the weight — the constants are not.
* `strictMonoOn_phase_congr` — the same for an abstract `Φ` given only `Φ = φ - ψ` on the
  component, which is the shape a phase-count lemma carries it in.
* `strictMonoOn_phase_lt`, `strictMonoOn_phase_congr_lt` — the two above with `|ψ'| < M + 1`
  **pointwise** rather than through a uniform `κ`.  This is the form the count actually
  consumes, and asking for the uniform one instead turns a threshold on `M` into a growth
  claim about `κ_M`, because the retained range moves with `M`.
* `continuousOn_phase_congr` — `Φ_M` is continuous on the component, for the same reason it
  is monotone there.
* `windowRadius`, `amplitudeWindows`, `deletedLength` — `eq:amplitude-deletion`'s family,
  **built** rather than posited: one open interval per amplitude zero, of exactly the
  half-width `thm:weighted-dominance`'s own inequality names.
* `amplitudeWindows_spec` — that family meets the dominance theorem's window inequality by
  construction, with no hypothesis at all.
* `windowRadius_le` — every radius is below the one the largest multiplicity gives, which is
  what lets `AngularBlocks` take the whole family at one common half-width; a nested family
  has no ordered block decomposition.
* `tendsto_deletedLength`, `eventually_deletedLength_le_one` —
  `eq:amplitude-window-negligible`: `(M+1)∑_j|Θ_{j,M}| → 0`, an exponential in `M` against a
  linear prefactor.  The rate sees `B` through `|S|`, `max ν_j` and `σ`; the statement it
  feeds does not.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Angular discrepancy and proof of
the main theorem» (`subsec:proof`, `eq:angular-subinterval`, `eq:Omega-M`, `eq:Phi-def`,
`eq:amplitude-deletion`, `eq:amplitude-window-negligible`).

## Tags

angular discrepancy, phase count, zero counting
-/

namespace ForgacsTran

open Set

/-! ### `eq:angular-subinterval` -/

/-- **Paper `eq:angular-subinterval`.**  For a strictly monotone continuous reparametrization
`z`, the angular subinterval `(α, β)` maps onto the open interval `(z α, z β)`. -/
theorem image_Ioo_eq_Ioo {z : ℝ → ℝ} {c d α β : ℝ}
    (hz : StrictMonoOn z (Icc c d)) (hzc : ContinuousOn z (Icc c d))
    (hcα : c ≤ α) (hαβ : α ≤ β) (hβd : β ≤ d) :
    z '' Ioo α β = Ioo (z α) (z β) := by
  have hsub : Icc α β ⊆ Icc c d := Icc_subset_Icc hcα hβd
  refine Set.Subset.antisymm ?_ ?_
  · exact (hz.mono hsub).image_Ioo_subset
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Ioo hαβ (hzc.mono hsub) hy
    exact ⟨x, hx, hxy⟩

/-- **Paper `eq:angular-subinterval`.**  `I_{α,β} ⊆ I_{Q,r}`: the angular subinterval sits
inside the image of the whole angular interval. -/
theorem subset_ftInterval_image {z : ℝ → ℝ} {c d α β : ℝ}
    (hcα : c ≤ α) (hβd : β ≤ d) :
    z '' Ioo α β ⊆ z '' Ioo c d :=
  Set.image_mono (Ioo_subset_Ioo hcα hβd)

/-! ### `eq:Omega-M` -/

/-- **Paper `eq:Omega-M`.**  Deleting `J` windows from an interval leaves at most `J + 1`
retained blocks: each of the `n - 1` gaps between consecutive blocks carries a window, and
distinct gaps carry distinct windows, so `n - 1 ≤ J`. -/
theorem card_blocks_le {ι : Type*} (W : Finset ι) {n : ℕ} (g : ℕ → ι)
    (hg : ∀ i, i + 1 < n → g i ∈ W)
    (hginj : ∀ i j, i + 1 < n → j + 1 < n → g i = g j → i = j) :
    n ≤ W.card + 1 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  have hcard : (Finset.range (n - 1)).card ≤ W.card := by
    refine Finset.card_le_card_of_injOn g (fun i hi => hg i ?_) ?_
    · have := Finset.mem_range.1 hi; omega
    · intro i hi j hj hij
      have hi' := Finset.mem_range.1 hi
      have hj' := Finset.mem_range.1 hj
      exact hginj i j (by omega) (by omega) hij
  rw [Finset.card_range] at hcard
  omega

/-! ### `eq:Phi-def` -/

/-- **Paper `eq:Phi-def`.**  `Φ_M(θ) = (M+1)θ - ψ(θ)` is strictly increasing on a component
once `M + 1` exceeds the phase-derivative bound `κ` of `eq:phase-derivative-bound`.

The threshold in `M` is where the weight is allowed to enter — `κ = κ_{Q,r,B}` depends on `B`
— and the discrepancy constants of `prop:angular-discrepancy` do not. -/
theorem strictMonoOn_phase {ψ dψ : ℝ → ℝ} {a b κ : ℝ} {M : ℕ}
    (hψ : ∀ θ ∈ Icc a b, HasDerivAt ψ (dψ θ) θ)
    (hκ : ∀ θ ∈ Icc a b, |dψ θ| ≤ κ)
    (hM : κ < (M : ℝ) + 1) :
    StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Icc a b) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun θ => ((M : ℝ) + 1) - dψ θ)
    (convex_Icc a b)
    (fun θ hθ => (((hasDerivAt_id θ).const_mul ((M : ℝ) + 1)).sub
      (hψ θ hθ)).continuousAt.continuousWithinAt)
    (fun x hx => ?_) (fun x hx => ?_)
  · have hx' := interior_subset hx
    exact ((((hasDerivAt_id x).const_mul ((M : ℝ) + 1)).sub
      (hψ x hx')).congr_deriv (by ring)).hasDerivWithinAt
  · have hx' := interior_subset hx
    have := abs_le.1 (hκ x hx')
    linarith [this.2]

/-- **Paper `eq:Phi-def`, in the form the phase count consumes.**  Any `Φ` agreeing with
`(M+1)θ - ψ(θ)` on the component is strictly increasing there, so a phase-count lemma stated
against an abstract `Φ` with `Φ = φ - ψ` need not carry `StrictMonoOn Φ` as a hypothesis. -/
theorem strictMonoOn_phase_congr {Φ ψ dψ : ℝ → ℝ} {a b κ : ℝ} {M : ℕ}
    (hΦdef : ∀ θ ∈ Icc a b, Φ θ = ((M : ℝ) + 1) * θ - ψ θ)
    (hψ : ∀ θ ∈ Icc a b, HasDerivAt ψ (dψ θ) θ)
    (hκ : ∀ θ ∈ Icc a b, |dψ θ| ≤ κ)
    (hM : κ < (M : ℝ) + 1) :
    StrictMonoOn Φ (Icc a b) := by
  intro x hx y hy hxy
  rw [hΦdef x hx, hΦdef y hy]
  exact strictMonoOn_phase hψ hκ hM hx hy hxy

/-- **Paper `eq:Phi-def`, pointwise.**  `Φ_M` is strictly increasing wherever
`|ψ'|` is below `M+1` at each point, with no uniform `κ` in between.

This is what the count actually needs, and asking for the uniform `κ` instead is
a strengthening with a cost.  `eq:phase-derivative-bound` bounds `|ψ'|` on a
component of `(0,π/r) ∖ {W = 0}`, but the retained range of `eq:retained-range`
is `[h/M, π/r - h/M]`, which **moves with `M`** — so a `κ` obtained by
compactness on the retained range is a `κ_M`, and `κ_M < M+1` is then a growth
claim about `κ_M` rather than a threshold on `M`.  The pointwise form asks
exactly what the monotonicity consumes and leaves the supplier free to use a
bound that moves with the range. -/
theorem strictMonoOn_phase_lt {ψ dψ : ℝ → ℝ} {a b : ℝ} {M : ℕ}
    (hψ : ∀ θ ∈ Icc a b, HasDerivAt ψ (dψ θ) θ)
    (hκ : ∀ θ ∈ Icc a b, |dψ θ| < (M : ℝ) + 1) :
    StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Icc a b) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun θ => ((M : ℝ) + 1) - dψ θ)
    (convex_Icc a b)
    (fun θ hθ => (((hasDerivAt_id θ).const_mul ((M : ℝ) + 1)).sub
      (hψ θ hθ)).continuousAt.continuousWithinAt)
    (fun x hx => ?_) (fun x hx => ?_)
  · have hx' := interior_subset hx
    exact ((((hasDerivAt_id x).const_mul ((M : ℝ) + 1)).sub
      (hψ x hx')).congr_deriv (by ring)).hasDerivWithinAt
  · have hx' := interior_subset hx
    have := abs_lt.1 (hκ x hx')
    linarith [this.2]

/-- `strictMonoOn_phase_lt` for an abstract `Φ` given only `Φ = φ - ψ` on the
component, which is the shape the phase count carries it in. -/
theorem strictMonoOn_phase_congr_lt {Φ ψ dψ : ℝ → ℝ} {a b : ℝ} {M : ℕ}
    (hΦdef : ∀ θ ∈ Icc a b, Φ θ = ((M : ℝ) + 1) * θ - ψ θ)
    (hψ : ∀ θ ∈ Icc a b, HasDerivAt ψ (dψ θ) θ)
    (hκ : ∀ θ ∈ Icc a b, |dψ θ| < (M : ℝ) + 1) :
    StrictMonoOn Φ (Icc a b) := by
  intro x hx y hy hxy
  rw [hΦdef x hx, hΦdef y hy]
  exact strictMonoOn_phase_lt hψ hκ hx hy hxy

/-- **Paper `eq:Phi-def`, continuity.**  `Φ_M` is continuous on the component for the same
reason it is monotone there: `ψ` is differentiable, hence continuous. -/
theorem continuousOn_phase_congr {Φ ψ dψ : ℝ → ℝ} {a b : ℝ} {M : ℕ}
    (hΦdef : ∀ θ ∈ Icc a b, Φ θ = ((M : ℝ) + 1) * θ - ψ θ)
    (hψ : ∀ θ ∈ Icc a b, HasDerivAt ψ (dψ θ) θ) :
    ContinuousOn Φ (Icc a b) := by
  refine ContinuousOn.congr ?_ (fun θ hθ => hΦdef θ hθ)
  exact (continuous_const.mul continuous_id).continuousOn.sub
    (fun θ hθ => (hψ θ hθ).continuousAt.continuousWithinAt)

/-! ### `eq:amplitude-deletion` and `eq:amplitude-window-negligible`

`thm:weighted-dominance` states its deleted family through the inequality

  `exp(-((-log σ)/(2|S|) · M / ν_j)) ≤ |θ - θ_j|`   for every `θ ∉ Θ M`,

so a family meeting it is *built* rather than posited: take the union of the open
intervals of exactly that radius.  Doing so makes the radius explicit, and then
`eq:amplitude-window-negligible` is arithmetic — an exponential in `M` against the
linear factor `M+1`.

**The order of the binders is what makes this work, and it is not incidental.**
`weighted_dominance_of_branch_any_multiplicity_at` produces the interior parameter
`ε` **before** quantifying over `Θ`, so `σ` is one fixed number by the time the
family is chosen and `c = (-log σ)/(2|S|)` is a fixed positive constant.  Under the
earlier form — `Θ` bound first, the interior group demanded at *every* `e` — the
contraction ratio runs to `1` as `e → 0`, `c` runs to `0` with it, and the radius
`exp(-cM/ν_j)` tends to a positive constant instead of shrinking;
`CubicWitnessInterior.cubicTheta_forced_of_hinterior` is that obstruction measured
at a pencil.  Nothing below would be true in that form.

The threshold in `M` depends on `B` — through `|S|`, through `max ν_j`, and through
`σ` — which is exactly the manuscript's "after increasing the `B`-dependent
threshold".  The *constants* of `eq:angular-discrepancy` do not, and that
separation is the content of `thm:main` clause 3. -/

/-- The half-width `eq:amplitude-deletion` assigns to the window at `θ_j`. -/
noncomputable def windowRadius (σ : ℝ) (S : Finset ℝ) (ν : ℝ → ℕ) (M : ℕ) (θj : ℝ) : ℝ :=
  Real.exp (-((-Real.log σ) / (2 * S.card) * M / ν θj))

/-- **`eq:amplitude-deletion`'s deleted family, built.**  One open interval per
amplitude zero, of the half-width the dominance theorem's own inequality names. -/
noncomputable def amplitudeWindows (σ : ℝ) (S : Finset ℝ) (ν : ℝ → ℕ) (M : ℕ) : Set ℝ :=
  ⋃ θj ∈ S, Set.Ioo (θj - windowRadius σ S ν M θj) (θj + windowRadius σ S ν M θj)

/-- The total deleted length `∑_j |Θ_{j,M}|`. -/
noncomputable def deletedLength (σ : ℝ) (S : Finset ℝ) (ν : ℝ → ℕ) (M : ℕ) : ℝ :=
  ∑ θj ∈ S, 2 * windowRadius σ S ν M θj

theorem windowRadius_pos (σ : ℝ) (S : Finset ℝ) (ν : ℝ → ℕ) (M : ℕ) (θj : ℝ) :
    0 < windowRadius σ S ν M θj := Real.exp_pos _

/-- **The family meets the dominance theorem's window inequality by construction.**
This is what `thm:weighted-dominance`'s last interior clause asks for, with no
hypothesis at all: outside the union, every amplitude zero is at least its own
radius away. -/
theorem amplitudeWindows_spec {σ : ℝ} {S : Finset ℝ} {ν : ℝ → ℕ} {M : ℕ} {θ : ℝ}
    (hθ : θ ∉ amplitudeWindows σ S ν M) :
    ∀ θj ∈ S, windowRadius σ S ν M θj ≤ |θ - θj| := by
  intro θj hθj
  by_contra hcon
  push Not at hcon
  refine hθ ?_
  rw [amplitudeWindows]
  refine Set.mem_biUnion hθj ?_
  rw [abs_lt] at hcon
  rw [Set.mem_Ioo]
  constructor
  · linarith [hcon.2]
  · linarith [hcon.1]

/-- Every radius is below the one the largest multiplicity gives. -/
theorem windowRadius_le {σ : ℝ} {S : Finset ℝ} {ν : ℝ → ℕ} {N : ℕ} {M : ℕ} {θj : ℝ}
    (hσ1 : σ < 1) (hσ0 : 0 < σ) (hν : 1 ≤ ν θj) (hνN : ν θj ≤ N) :
    windowRadius σ S ν M θj
      ≤ Real.exp (-((-Real.log σ) / (2 * S.card) / N * M)) := by
  have hlog : 0 < -Real.log σ := by
    have := Real.log_neg hσ0 hσ1; linarith
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ (-Real.log σ) / (2 * S.card) := by positivity
  have hνR : (0 : ℝ) < (ν θj : ℝ) := by exact_mod_cast hν
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (le_trans hν hνN)
  have hle : (ν θj : ℝ) ≤ (N : ℝ) := by exact_mod_cast hνN
  rw [windowRadius]
  refine Real.exp_le_exp.2 ?_
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hrw : (-Real.log σ) / (2 * S.card) / N * (M : ℝ)
      = ((-Real.log σ) / (2 * S.card) * M) / N := by ring
  have hkey : (-Real.log σ) / (2 * S.card) / N * (M : ℝ)
      ≤ (-Real.log σ) / (2 * S.card) * M / ν θj := by
    rw [hrw]
    gcongr
  linarith

/-- **`eq:amplitude-window-negligible`.**  `(M+1)∑_j|Θ_{j,M}| → 0`: the windows are
exponentially small in `M` and the prefactor is linear.  The rate depends on `B`
through `|S|`, `max ν_j` and `σ`; the statement it feeds does not. -/
theorem tendsto_deletedLength {σ : ℝ} {S : Finset ℝ} {ν : ℝ → ℕ} {N : ℕ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hN : 1 ≤ N)
    (hν : ∀ θj ∈ S, 1 ≤ ν θj) (hνN : ∀ θj ∈ S, ν θj ≤ N) :
    Filter.Tendsto (fun M : ℕ => ((M : ℝ) + 1) * deletedLength σ S ν M)
      Filter.atTop (nhds 0) := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp [deletedLength]
  have hlog : 0 < -Real.log σ := by
    have := Real.log_neg hσ0 hσ1; linarith
  have hcardpos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hSne
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set A : ℝ := (-Real.log σ) / (2 * S.card) / N with hA
  have hApos : 0 < A := by rw [hA]; positivity
  -- the majorant, and the exponential-beats-linear limit
  have hdlnn : ∀ M : ℕ, 0 ≤ deletedLength σ S ν M := fun M =>
    Finset.sum_nonneg fun θj _ => by
      have := windowRadius_pos σ S ν M θj; linarith
  have hmaj : ∀ M : ℕ, ((M : ℝ) + 1) * deletedLength σ S ν M
      ≤ 2 * (S.card : ℝ) * (((M : ℝ) + 1) * Real.exp (-(A * M))) := by
    intro M
    have hstep : deletedLength σ S ν M ≤ 2 * (S.card : ℝ) * Real.exp (-(A * M)) := by
      rw [deletedLength]
      calc ∑ θj ∈ S, 2 * windowRadius σ S ν M θj
          ≤ ∑ _θj ∈ S, 2 * Real.exp (-(A * M)) := by
            refine Finset.sum_le_sum fun θj hθj => ?_
            have hb := windowRadius_le (S := S) (N := N) (M := M) hσ1 hσ0 (hν θj hθj)
              (hνN θj hθj)
            have heq : (-Real.log σ) / (2 * S.card) / N * (M : ℝ) = A * M := by rw [hA]
            rw [heq] at hb
            linarith
        _ = 2 * (S.card : ℝ) * Real.exp (-(A * M)) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    calc ((M : ℝ) + 1) * deletedLength σ S ν M
        ≤ ((M : ℝ) + 1) * (2 * (S.card : ℝ) * Real.exp (-(A * M))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 * (S.card : ℝ) * (((M : ℝ) + 1) * Real.exp (-(A * M))) := by ring
  have hbase : Filter.Tendsto (fun M : ℕ => ((M : ℝ) + 1) * Real.exp (-(A * M)))
      Filter.atTop (nhds 0) := by
    have hx : Filter.Tendsto (fun M : ℕ => A * (M : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hApos tendsto_natCast_atTop_atTop
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
    have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hx
    have hs := (h1.const_mul A⁻¹).add h0
    rw [mul_zero, add_zero] at hs
    refine hs.congr fun M => ?_
    simp only [Function.comp_apply, pow_one, pow_zero, one_mul]
    field_simp
  have hlim := hbase.const_mul (2 * (S.card : ℝ))
  rw [mul_zero] at hlim
  exact squeeze_zero (fun M => mul_nonneg (by positivity) (hdlnn M)) hmaj hlim

theorem eventually_deletedLength_le_one {σ : ℝ} {S : Finset ℝ} {ν : ℝ → ℕ} {N : ℕ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hN : 1 ≤ N)
    (hν : ∀ θj ∈ S, 1 ≤ ν θj) (hνN : ∀ θj ∈ S, ν θj ≤ N) :
    ∀ᶠ M : ℕ in Filter.atTop, ((M : ℝ) + 1) * deletedLength σ S ν M ≤ 1 := by
  have h := tendsto_deletedLength hσ0 hσ1 hN hν hνN
  have := h (Metric.ball_mem_nhds (0 : ℝ) one_pos)
  filter_upwards [this] with M hM
  have : |((M : ℝ) + 1) * deletedLength σ S ν M| < 1 := by
    simpa [Real.dist_eq] using Metric.mem_ball.1 hM
  exact le_of_lt (lt_of_abs_lt this)


end ForgacsTran
