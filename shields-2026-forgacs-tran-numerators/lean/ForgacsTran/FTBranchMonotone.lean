/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchDeriv
import ForgacsTran.FTBranchAngleBound

/-!
# `τ(θ)` is strictly decreasing

`Forgacs2017RationalDenominator` Lemma 3, with the paper's own exclusion and no
other restriction: with
`l = n - 1` and `(r, n) ≠ (1, 2)`, the radius `τ(θ)` of Lemma 2 strictly
decreases across the viewing arc.

## Main statements

* `deriv_ftAngleSum_sub_neg` — the derivative of `θ ↦ ∑_k θ_k(τ, θ) - rθ` is
  negative at every point of the branch, which is `A(θ) > 0`.
* `ftTau_strictAnti` — Lemma 3, stated on two branch points rather than through a
  chosen solution function.
* `nonneg_of_deriv_neg_at_zeros` — the shape of that argument, for an arbitrary
  real function: differentiable on `[s, b]`, vanishing at `b`, with negative
  derivative at each of its zeros, it is nonnegative at `s`.  Mathlib-level and
  reusable as it stands.

## Implementation notes

**Differs from the paper's route.**  The paper differentiates `τ(θ)` itself,
which needs the branch to be known differentiable; here `τ` is never
differentiated.  Only the partial derivative in `θ` at fixed `τ` is used, and
monotonicity is read off the level set `∑_k θ_k(τ', θ) = rθ + (n-1)π`: the
function crosses zero with negative slope at every zero it has, so it cannot be
non-positive to the left of one.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

monotonicity, branch radius, angle system
-/

namespace ForgacsTran

open Real Set Filter Topology

private theorem lt_pi_of_lt_pi_div {r : ℕ} {s : ℝ} (hr : 1 ≤ r) (hs0 : 0 < s)
    (hsr : s < π / r) : s < π := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  rw [lt_div_iff₀ hr0] at hsr
  nlinarith

/-- `2 sin y cos (y - s) = sin (2y - s) + sin s`, the rewriting that turns
`Forgacs2017RationalDenominator` (15) into `sum_sin_two_mul_sub_lt`. -/
theorem two_sin_mul_cos_sub (y s : ℝ) :
    2 * Real.sin y * Real.cos (y - s) = Real.sin (2 * y - s) + Real.sin s := by
  rw [Real.cos_sub, Real.sin_sub, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (2 * Real.sin s) * (Real.sin_sq_add_cos_sq y)

/-! ### The shape of the monotonicity argument

Nothing under this heading mentions the branch.  Lemma 3 comes down to one fact
about a real function, and stating it separately is what leaves the branch proof
with only the angle system in it. -/

/-- **A function whose derivative is negative at each of its zeros does not dip
below zero to the left of one.**  With `h` differentiable on `[s, b]`, `h b = 0`,
and `h' < 0` at every zero of `h` in `[s, b]`, necessarily `0 ≤ h s`.

Were `h s < 0`, the least zero `m` of `h` on `[s, b]` would satisfy `s < m`, and
the negative derivative there would put `h > 0` immediately to the left of `m`;
the intermediate value theorem between `s` and that point then produces a zero
below `m`, contradicting leastness.  The closed interval is what makes the zero
set compact and "least zero" available. -/
theorem nonneg_of_deriv_neg_at_zeros {h : ℝ → ℝ} {s b : ℝ} (hsb : s ≤ b)
    (hd : ∀ x ∈ Icc s b, DifferentiableAt ℝ h x)
    (hzero : ∀ x ∈ Icc s b, h x = 0 → deriv h x < 0)
    (hb : h b = 0) : 0 ≤ h s := by
  by_contra hcon
  rw [not_le] at hcon
  have hcont : ContinuousOn h (Icc s b) := fun x hx =>
    ((hd x hx).continuousAt).continuousWithinAt
  have hZclosed : IsClosed (Icc s b ∩ h ⁻¹' {0}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZcompact : IsCompact (Icc s b ∩ h ⁻¹' {0}) :=
    isCompact_Icc.of_isClosed_subset hZclosed inter_subset_left
  obtain ⟨m, hmleast⟩ := hZcompact.exists_isLeast ⟨b, ⟨⟨hsb, le_refl b⟩, hb⟩⟩
  have hmmem : m ∈ Icc s b := hmleast.1.1
  have hm0 : h m = 0 := hmleast.1.2
  have hms : s < m := by
    rcases eq_or_lt_of_le hmmem.1 with heq | hlt
    · exact absurd (heq ▸ hm0) (ne_of_lt hcon)
    · exact hlt
  have hslope := ((hd m hmmem).hasDerivAt).tendsto_slope
  have hev : ∀ᶠ x in 𝓝[≠] m, slope h m x < 0 :=
    hslope.eventually (eventually_lt_nhds (hzero m hmmem hm0))
  have hevL : ∀ᶠ x in 𝓝[<] m, slope h m x < 0 :=
    hev.filter_mono (nhdsWithin_mono m fun x hx => ne_of_lt hx)
  have hevG : ∀ᶠ x in 𝓝[<] m, s < x :=
    (eventually_gt_nhds hms).filter_mono nhdsWithin_le_nhds
  have hevS : ∀ᶠ x in 𝓝[<] m, x < m := eventually_mem_nhdsWithin
  obtain ⟨x, hxs, hxg, hxl⟩ := (hevL.and (hevG.and hevS)).exists
  have hxpos : 0 < h x := by
    rw [slope_def_field, hm0, sub_zero, div_neg_iff] at hxs
    rcases hxs with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  obtain ⟨cc, hcc, hcc0⟩ := intermediate_value_Icc hxg.le
    (hcont.mono (Icc_subset_Icc_right (le_trans hxl.le hmmem.2))) ⟨hcon.le, hxpos.le⟩
  have : m ≤ cc := hmleast.2 ⟨⟨hcc.1, le_trans hcc.2 (le_trans hxl.le hmmem.2)⟩, hcc0⟩
  linarith [hcc.2]

/-! ### The branch -/

/-- **`Forgacs2017RationalDenominator` (15).**  At a point of the branch
the derivative of `θ ↦ ∑_k θ_k(τ, θ) - rθ` is strictly negative. -/
theorem deriv_ftAngleSum_sub_neg {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hne : ¬(r = 1 ∧ n = 2)) {τ s : ℝ} (hτ : 0 < τ)
    (hs0 : 0 < s) (hsr : s < π / r)
    (hbr : ftAngleSum a τ s = r * s + ((n - 1 : ℕ) : ℝ) * π) :
    (∑ k, Real.sin (ftAngle (a k) τ s) * Real.cos (ftAngle (a k) τ s - s) / Real.sin s)
      - r < 0 := by
  have hsπ : s < π := lt_pi_of_lt_pi_div hr hs0 hsr
  have hsmem : s ∈ Ioo 0 π := ⟨hs0, hsπ⟩
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs0 hsπ
  set φ : Fin n → ℝ := fun k => ftAngle (a k) τ s with hφdef
  have hφ : ∀ k, φ k ∈ Ioo s π := fun k => ftAngle_mem_Ioo (ha k) hτ hsmem
  have hsum : ∑ k, φ k = r * s + ((n - 1 : ℕ) : ℝ) * π := hbr
  have hbound := sum_sin_two_mul_sub_lt hn hr hne hs0 hsr hφ hsum
  have hterm : ∀ k, Real.sin (φ k) * Real.cos (φ k - s) / Real.sin s
      = (Real.sin (2 * φ k - s) + Real.sin s) / (2 * Real.sin s) := by
    intro k
    rw [← two_sin_mul_cos_sub (φ k) s]
    field_simp
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hterm k, ← Finset.sum_div]
  have hsplit : ∑ k, (Real.sin (2 * φ k - s) + Real.sin s)
      = (∑ k, Real.sin (2 * φ k - s)) + n * Real.sin s := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hsplit, sub_neg, div_lt_iff₀ (by positivity)]
  linarith

/-- **`Forgacs2017RationalDenominator` Lemma 3**, with `l = n - 1` and their own
exclusion `(r, n) ≠ (1, 2)`.  Two points of the branch are compared
directly, so no choice of solution function is needed. -/
theorem ftTau_strictAnti {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hne : ¬(r = 1 ∧ n = 2))
    {θ θ' τ τ' : ℝ} (hτ : 0 < τ) (hτ' : 0 < τ') (hθ0 : 0 < θ) (hlt : θ < θ')
    (hθ'r : θ' < π / r)
    (hbr : ftAngleSum a τ θ = r * θ + ((n - 1 : ℕ) : ℝ) * π)
    (hbr' : ftAngleSum a τ' θ' = r * θ' + ((n - 1 : ℕ) : ℝ) * π) :
    τ' < τ := by
  by_contra hcon
  push Not at hcon
  set c : ℝ := ((n - 1 : ℕ) : ℝ) * π with hc
  set h : ℝ → ℝ := fun s => ftAngleSum a τ' s - ((r : ℝ) * s + c) with hdef
  have hmem : ∀ s : ℝ, 0 < s → s < π / r → s ∈ Ioo 0 π := fun s hs0 hsr =>
    ⟨hs0, lt_pi_of_lt_pi_div hr hs0 hsr⟩
  have hderiv : ∀ s : ℝ, 0 < s → s < π / r → HasDerivAt h
      ((∑ k, Real.sin (ftAngle (a k) τ' s) * Real.cos (ftAngle (a k) τ' s - s) / Real.sin s)
        - r) s := by
    intro s hs0 hsr
    have h1 := hasDerivAt_ftAngleSum ha hτ' (hmem s hs0 hsr)
    have h2 : HasDerivAt (fun t : ℝ => (r : ℝ) * t + c) ((r : ℝ)) s := by
      have := ((hasDerivAt_id s).const_mul ((r : ℝ))).add_const c
      simpa using this
    exact h1.sub h2
  have hzero : ∀ s : ℝ, 0 < s → s < π / r → h s = 0 →
      (∑ k, Real.sin (ftAngle (a k) τ' s) * Real.cos (ftAngle (a k) τ' s - s) / Real.sin s)
        - r < 0 := by
    intro s hs0 hsr hs
    refine deriv_ftAngleSum_sub_neg hn ha hr hne hτ' hs0 hsr ?_
    have : ftAngleSum a τ' s - ((r : ℝ) * s + c) = 0 := hs
    linarith
  have hθ'0 : 0 < θ' := lt_trans hθ0 hlt
  have hθr : θ < π / r := lt_trans hlt hθ'r
  have hh' : h θ' = 0 := by simp only [hdef]; rw [hbr']; ring
  have hhθ : h θ ≤ 0 := by
    rcases eq_or_lt_of_le hcon with heq | hlt'
    · have hz : h θ = 0 := by simp only [hdef]; rw [← heq, hbr]; ring
      linarith
    · have hlt2 := ftAngleSum_lt (a := a) hn ha (hmem θ hθ0 hθr) hτ hlt'
      simp only [hdef]
      rw [hbr] at hlt2
      linarith
  -- the core: no point of `[θ, θ')` can carry a negative value
  have main : ∀ s₀ : ℝ, θ ≤ s₀ → s₀ < θ' → h s₀ < 0 → False := by
    intro s₀ hs₀θ hs₀θ' hs₀neg
    have hs₀0 : 0 < s₀ := lt_of_lt_of_le hθ0 hs₀θ
    have hsub : Icc s₀ θ' ⊆ Ioo 0 (π / r) := fun x hx =>
      ⟨lt_of_lt_of_le hs₀0 hx.1, lt_of_le_of_lt hx.2 hθ'r⟩
    refine absurd (nonneg_of_deriv_neg_at_zeros hs₀θ'.le
      (fun x hx => (hderiv x (hsub hx).1 (hsub hx).2).differentiableAt)
      (fun x hx hx0 => by
        rw [(hderiv x (hsub hx).1 (hsub hx).2).deriv]
        exact hzero x (hsub hx).1 (hsub hx).2 hx0) hh') (not_le.2 hs₀neg)
  rcases eq_or_lt_of_le hhθ with heq | hneg
  · -- `h θ = 0`: the negative slope pushes it below zero just to the right
    have hdθ := hzero θ hθ0 hθr heq
    have hslope := (hderiv θ hθ0 hθr).tendsto_slope
    have hev : ∀ᶠ x in 𝓝[≠] θ, slope h θ x < 0 :=
      hslope.eventually (eventually_lt_nhds hdθ)
    have hevR : ∀ᶠ x in 𝓝[>] θ, slope h θ x < 0 :=
      hev.filter_mono (nhdsWithin_mono θ fun x hx => (ne_of_lt hx).symm)
    have hevG : ∀ᶠ x in 𝓝[>] θ, x < θ' :=
      (eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds
    have hevS : ∀ᶠ x in 𝓝[>] θ, θ < x := eventually_mem_nhdsWithin
    obtain ⟨x, hxs, hxg, hxl⟩ := (hevR.and (hevG.and hevS)).exists
    refine main x hxl.le hxg ?_
    rw [slope_def_field, heq, sub_zero, div_neg_iff] at hxs
    rcases hxs with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · exact h1
  · exact main θ (le_refl θ) hlt hneg

end ForgacsTran
