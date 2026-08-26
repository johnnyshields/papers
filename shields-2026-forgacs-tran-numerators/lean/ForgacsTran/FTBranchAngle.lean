/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# The Forgács–Tran angle system

This module builds the angles `θ_k` of `Forgacs2017RationalDenominator` Lemma 2
and the one-variable analysis they need.

## Main definitions

* `ftArccot` — the inverse cotangent onto `(0, π)`, absent from Mathlib.
* `ftAngle a τ θ` — the unique `y ∈ (θ, π)` with `a sin y = τ sin (y - θ)`;
  `ftAngle_spec` and `ftAngle_unique` are the two halves of that description.
* `ftAngleSum` — `∑_k θ_k`, strictly decreasing in `τ` from `n π` to `n θ`.

## Implementation notes

**Differs from the paper's route.**  The paper produces the `n`-tuple from the
complex implicit function theorem in `n + 1` variables followed by analytic
continuation.  The relation `a sin y = τ sin (y - θ)` is instead solved in
closed form: it is `cot y = cot θ - a / (τ sin θ)`, so each `θ_k` is an explicit
elementary function of `τ` and `θ` and the whole system collapses to the single
scalar equation `∑_k θ_k(τ) = rθ + lπ`.  Clause (i) of Lemma 2 becomes automatic
rather than a conclusion, and no implicit function theorem is used.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

angle system, Forgacs-Tran branch, denominator pencil
-/

namespace ForgacsTran

open Real Set Filter Topology

/-! ### Inverse cotangent -/

/-- The inverse cotangent, valued in `(0, π)`.  Mathlib carries `arctan` but no
`arccot`; the branch angles of `Forgacs2017RationalDenominator` Lemma 2 all live
in `(0, π)`, which is exactly this branch. -/
noncomputable def ftArccot (x : ℝ) : ℝ := π / 2 - arctan x

theorem ftArccot_mem_Ioo (x : ℝ) : ftArccot x ∈ Ioo 0 π := by
  have h := arctan_mem_Ioo x
  constructor <;> [skip; skip] <;>
    · simp only [ftArccot]
      obtain ⟨h1, h2⟩ := h
      linarith

theorem sin_ftArccot_pos (x : ℝ) : 0 < sin (ftArccot x) :=
  sin_pos_of_pos_of_lt_pi (ftArccot_mem_Ioo x).1 (ftArccot_mem_Ioo x).2

/-- `cot (ftArccot x) = x`, in the division-free form used throughout. -/
theorem cos_ftArccot (x : ℝ) : cos (ftArccot x) = x * sin (ftArccot x) := by
  have h1 : cos (π / 2 - arctan x) = sin (arctan x) := cos_pi_div_two_sub _
  have h2 : sin (π / 2 - arctan x) = cos (arctan x) := sin_pi_div_two_sub _
  have h3 : sin (arctan x) = x * cos (arctan x) := by
    rw [sin_arctan, cos_arctan]; ring
  simp only [ftArccot, h1, h2, h3]

theorem ftArccot_strictAnti : StrictAnti ftArccot := fun _ _ h => by
  simp only [ftArccot]
  have := arctan_strictMono h
  linarith

theorem continuous_ftArccot : Continuous ftArccot :=
  continuous_const.sub continuous_arctan

/-- The uniqueness half: on `(0, π)` the relation `cos y = x sin y` pins `y`. -/
theorem ftArccot_eq_of_cos_eq {y x : ℝ} (hy : y ∈ Ioo 0 π) (h : cos y = x * sin y) :
    y = ftArccot x := by
  have hy' : π / 2 - y ∈ Ioo (-(π / 2)) (π / 2) := by
    obtain ⟨h1, h2⟩ := hy; constructor <;> linarith
  have hc : 0 < cos (π / 2 - y) := cos_pos_of_mem_Ioo hy'
  have h1 : cos (π / 2 - y) = sin y := cos_pi_div_two_sub _
  have h2 : sin (π / 2 - y) = cos y := sin_pi_div_two_sub _
  have htan : tan (π / 2 - y) = x := by
    rw [tan_eq_sin_div_cos, h1, h2, h, mul_div_assoc]
    rw [h1] at hc
    field_simp
  have := arctan_tan hy'.1 hy'.2
  rw [htan] at this
  rw [ftArccot, this]
  ring

theorem ftArccot_cot {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : ftArccot (cos θ / sin θ) = θ := by
  have hs : sin θ ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  exact (ftArccot_eq_of_cos_eq hθ (by field_simp)).symm

theorem tendsto_ftArccot_atBot : Tendsto ftArccot atBot (𝓝 π) := by
  have h : Tendsto arctan atBot (𝓝 (-(π / 2))) :=
    tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds
  have h2 := (tendsto_const_nhds (x := π / 2) (f := (atBot : Filter ℝ))).sub h
  have : (fun x : ℝ => π / 2 - arctan x) = ftArccot := rfl
  rw [this] at h2
  simpa only [sub_neg_eq_add, show π / 2 + π / 2 = π by ring] using h2

/-! ### The branch angles -/

/-- `θ_k` of `Forgacs2017RationalDenominator` Lemma 2: the unique angle in
`(θ, π)` with `a sin θ_k = τ sin (θ_k - θ)`, equivalently
`τ_k sin θ_k / sin (θ_k - θ) = τ`, their (10). -/
noncomputable def ftAngle (a τ θ : ℝ) : ℝ := ftArccot (cos θ / sin θ - a / (τ * sin θ))

theorem ftAngle_lt_pi (a τ θ : ℝ) : ftAngle a τ θ < π := (ftArccot_mem_Ioo _).2

theorem ftAngle_pos (a τ θ : ℝ) : 0 < ftAngle a τ θ := (ftArccot_mem_Ioo _).1

/-- Clause (i) of `Forgacs2017RationalDenominator` Lemma 2, which the closed form
makes automatic: `θ_k > θ` because `a / (τ sin θ) > 0` shifts the cotangent
strictly down. -/
theorem lt_ftAngle {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) :
    θ < ftAngle a τ θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hpos : 0 < a / (τ * sin θ) := div_pos ha (mul_pos hτ hs)
  have := ftArccot_strictAnti (show cos θ / sin θ - a / (τ * sin θ) < cos θ / sin θ by linarith)
  rwa [ftArccot_cot hθ] at this

theorem ftAngle_mem_Ioo {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) :
    ftAngle a τ θ ∈ Ioo θ π :=
  ⟨lt_ftAngle ha hτ hθ, ftAngle_lt_pi _ _ _⟩

/-- Clause (iii) of `Forgacs2017RationalDenominator` Lemma 2, cleared of
denominators. -/
theorem ftAngle_spec {a τ θ : ℝ} (hτ : τ ≠ 0) (hθ : θ ∈ Ioo 0 π) :
    a * sin (ftAngle a τ θ) = τ * sin (ftAngle a τ θ - θ) := by
  have hs : sin θ ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  set c := cos θ / sin θ - a / (τ * sin θ) with hc
  have hcos : cos (ftAngle a τ θ) = c * sin (ftAngle a τ θ) := cos_ftArccot _
  have hcs : c * sin θ = cos θ - a / τ := by rw [hc]; field_simp
  rw [sin_sub, hcos]
  have : τ * (sin (ftAngle a τ θ) * cos θ - c * sin (ftAngle a τ θ) * sin θ)
      = sin (ftAngle a τ θ) * (τ * (cos θ - c * sin θ)) := by ring
  rw [this, hcs]
  field

/-- `Forgacs2017RationalDenominator` (10) in its stated, quotient form. -/
theorem ftAngle_ratio {a τ θ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) :
    a * sin (ftAngle a τ θ) / sin (ftAngle a τ θ - θ) = τ := by
  have hm := ftAngle_mem_Ioo ha hτ hθ
  have hd : 0 < sin (ftAngle a τ θ - θ) :=
    sin_pos_of_pos_of_lt_pi (by linarith [hm.1]) (by linarith [hm.2, hθ.1])
  rw [ftAngle_spec (ne_of_gt hτ) hθ]
  field_simp

/-- The uniqueness half of the description of `θ_k`. -/
theorem ftAngle_unique {a τ θ y : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) (hy : y ∈ Ioo θ π)
    (h : a * sin y = τ * sin (y - θ)) : y = ftAngle a τ θ := by
  have hs : sin θ ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have hy0 : y ∈ Ioo 0 π := ⟨lt_trans hθ.1 hy.1, hy.2⟩
  refine ftArccot_eq_of_cos_eq hy0 ?_
  rw [sin_sub] at h
  have hτ' : τ ≠ 0 := ne_of_gt hτ
  field_simp
  nlinarith [h, sq_nonneg (sin θ)]

/-! ### The angle sum -/

/-- `∑_k θ_k(τ)`, the left-hand side of clause (ii) of
`Forgacs2017RationalDenominator` Lemma 2. -/
noncomputable def ftAngleSum {n : ℕ} (a : Fin n → ℝ) (τ θ : ℝ) : ℝ :=
  ∑ k, ftAngle (a k) τ θ

theorem ftAngleSum_lt {n : ℕ} {a : Fin n → ℝ} {τ₁ τ₂ θ : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hθ : θ ∈ Ioo 0 π) (hτ₁ : 0 < τ₁) (hlt : τ₁ < τ₂) :
    ftAngleSum a τ₂ θ < ftAngleSum a τ₁ θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hτ₂ : (0:ℝ) < τ₂ := hτ₁.trans hlt
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · exact Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  · intro k _
    refine ftArccot_strictAnti ?_
    have : a k / (τ₂ * sin θ) < a k / (τ₁ * sin θ) := by
      apply div_lt_div_of_pos_left (ha k) (mul_pos hτ₁ hs)
      exact mul_lt_mul_of_pos_right hlt hs
    linarith

theorem continuousOn_ftAngleSum {n : ℕ} (a : Fin n → ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ContinuousOn (fun τ : ℝ => ftAngleSum a τ θ) (Ioi 0) := by
  have hs : sin θ ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  refine continuousOn_finsetSum _ fun k _ => ?_
  refine continuous_ftArccot.comp_continuousOn (continuousOn_const.sub ?_)
  exact continuousOn_const.div (continuousOn_id.mul continuousOn_const)
    fun τ hτ => mul_ne_zero (ne_of_gt hτ) hs

theorem tendsto_ftAngle_nhdsGT_zero {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Ioo 0 π) :
    Tendsto (fun τ : ℝ => ftAngle a τ θ) (𝓝[>] 0) (𝓝 π) := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hrw : (fun τ : ℝ => cos θ / sin θ - a / (τ * sin θ))
      = fun τ : ℝ => cos θ / sin θ + -((a / sin θ) * τ⁻¹) := by
    funext τ
    rw [div_eq_mul_inv, mul_comm τ (sin θ), ← div_div, div_eq_mul_inv]
    ring
  have h1 : Tendsto (fun τ : ℝ => (a / sin θ) * τ⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    Tendsto.const_mul_atTop (div_pos ha hs) tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun τ : ℝ => cos θ / sin θ - a / (τ * sin θ)) (𝓝[>] (0:ℝ)) atBot := by
    rw [hrw]
    exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp h1)
  exact tendsto_ftArccot_atBot.comp h2

theorem tendsto_ftAngle_atTop {a θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    Tendsto (fun τ : ℝ => ftAngle a τ θ) atTop (𝓝 θ) := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1 : Tendsto (fun τ : ℝ => a / (τ * sin θ)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_id.atTop_mul_const hs
  have h2 : Tendsto (fun τ : ℝ => cos θ / sin θ - a / (τ * sin θ)) atTop
      (𝓝 (cos θ / sin θ)) := by
    simpa using tendsto_const_nhds.sub h1
  have := (continuous_ftArccot.tendsto _).comp h2
  rwa [ftArccot_cot hθ] at this

theorem tendsto_ftAngleSum_nhdsGT_zero {n : ℕ} {a : Fin n → ℝ} (ha : ∀ k, 0 < a k)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    Tendsto (fun τ : ℝ => ftAngleSum a τ θ) (𝓝[>] 0) (𝓝 ((n : ℝ) * π)) := by
  have := tendsto_finsetSum (Finset.univ : Finset (Fin n))
    (fun k (_ : k ∈ Finset.univ) => tendsto_ftAngle_nhdsGT_zero (ha k) hθ)
  simpa [ftAngleSum, Finset.sum_const, nsmul_eq_mul] using this

theorem tendsto_ftAngleSum_atTop {n : ℕ} (a : Fin n → ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    Tendsto (fun τ : ℝ => ftAngleSum a τ θ) atTop (𝓝 ((n : ℝ) * θ)) := by
  have := tendsto_finsetSum (Finset.univ : Finset (Fin n))
    (fun k (_ : k ∈ Finset.univ) => tendsto_ftAngle_atTop (a := a k) hθ)
  simpa [ftAngleSum, Finset.sum_const, nsmul_eq_mul] using this

theorem tendsto_ftArccot_atTop : Tendsto ftArccot atTop (𝓝 0) := by
  have h : Tendsto arctan atTop (𝓝 (π / 2)) :=
    tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have h2 := (tendsto_const_nhds (x := π / 2) (f := (atTop : Filter ℝ))).sub h
  have hf : (fun x : ℝ => π / 2 - arctan x) = ftArccot := rfl
  rw [hf] at h2
  simpa using h2

/-- `(cos θ - q)/sin θ` runs to `+∞` as `θ → 0⁺` when `q < 1`, and to `-∞` when
`q > 1`.  This is what sends a branch angle to `0` or to `π` at the endpoint. -/
theorem tendsto_inv_sin_nhdsGT_zero :
    Tendsto (fun θ : ℝ => (Real.sin θ)⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
  refine tendsto_inv_nhdsGT_zero.comp ?_
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := (Real.continuous_sin.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsGT pi_pos] with θ hθ
    exact sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

theorem tendsto_cos_sub_div_sin_atTop {q : ℝ} (hq : q < 1) :
    Tendsto (fun θ : ℝ => (Real.cos θ - q) / Real.sin θ) (𝓝[>] (0 : ℝ)) atTop := by
  have hnum : Tendsto (fun θ : ℝ => Real.cos θ - q) (𝓝[>] (0 : ℝ)) (𝓝 (1 - q)) := by
    have := (Real.continuous_cos.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this.sub tendsto_const_nhds
  have h := Filter.Tendsto.pos_mul_atTop (by linarith) hnum tendsto_inv_sin_nhdsGT_zero
  simpa only [div_eq_mul_inv] using h

theorem tendsto_cos_sub_div_sin_atBot {q : ℝ} (hq : 1 < q) :
    Tendsto (fun θ : ℝ => (Real.cos θ - q) / Real.sin θ) (𝓝[>] (0 : ℝ)) atBot := by
  have hnum : Tendsto (fun θ : ℝ => Real.cos θ - q) (𝓝[>] (0 : ℝ)) (𝓝 (1 - q)) := by
    have := (Real.continuous_cos.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this.sub tendsto_const_nhds
  have h := Filter.Tendsto.neg_mul_atTop (by linarith) hnum tendsto_inv_sin_nhdsGT_zero
  simpa only [div_eq_mul_inv] using h

theorem arctan_le_self {t : ℝ} (ht : 0 ≤ t) : arctan t ≤ t := by
  rcases eq_or_lt_of_le ht with rfl | htp
  · simp
  · have hs := arctan_mem_Ioo t
    have hspos : 0 < arctan t := by
      have : arctan 0 < arctan t := arctan_strictMono htp
      simpa using this
    have h2 := Real.lt_tan hspos hs.2
    rw [tan_arctan] at h2
    exact h2.le

/-- `ftArccot Y ≤ 1/Y` for `Y > 0`: how fast the inverse cotangent closes on `0`,
and hence how fast a branch angle closes on `π`. -/
theorem ftArccot_le_inv {Y : ℝ} (hY : 0 < Y) : ftArccot Y ≤ Y⁻¹ := by
  have h : ftArccot Y = arctan Y⁻¹ := by
    rw [ftArccot, arctan_inv_of_pos hY]
  rw [h]
  exact arctan_le_self (by positivity)

theorem pi_sub_ftArccot {X : ℝ} : π - ftArccot X = ftArccot (-X) := by
  simp only [ftArccot, Real.arctan_neg]
  ring

/-- **The rate at which an angle opens to `π`.**  If the cotangent argument is at
most `-c/θ` then the angle is within `θ/c` of `π`. -/
theorem pi_sub_ftArccot_le {X c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hX : X ≤ -(c / θ)) :
    π - ftArccot X ≤ θ / c := by
  rw [pi_sub_ftArccot]
  have hpos : 0 < -X := by
    have : (0 : ℝ) < c / θ := by positivity
    linarith
  refine le_trans (ftArccot_le_inv hpos) ?_
  rw [inv_le_comm₀ hpos (by positivity)]
  rw [le_neg]
  rw [show -(c / θ) = -(c / θ) from rfl] at hX
  have : (θ / c)⁻¹ = c / θ := by
    rw [inv_div]
  rw [this]
  linarith

end ForgacsTran
