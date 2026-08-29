/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The tangent is superadditive on the first quadrant

Mathlib carries the addition formula `Real.tan_add` but nothing about the sign of the
defect `tan(a + b) - tan a - tan b`.  That defect has a closed form,

`tan(a+b) - tan a - tan b = sin a · sin b · sin(a+b) / (cos a · cos b · cos(a+b))`,

whose three factors are all positive on `(0, π/2)`, so the tangent is strictly
superadditive there.  Two consequences follow by induction: a sum of tangents is at most
the tangent of the sum, and `tan (r θ) ≥ r · tan θ` for `r : ℕ`, strictly once `r ≥ 2`.

The hypotheses are stated on the **sum**: `a + b < π / 2` rather than `a, b < π / 2`, which
is what keeps `cos (a + b)` positive and is the form an induction over a `Finset` consumes.

## Main results

* `Shields.tan_add_sub` -- the defect of additivity, in closed form.
* `Shields.tan_add_lt`, `Shields.tan_add_le` -- strict superadditivity on `(0, π/2)`, and
  the same with the endpoints allowed.
* `Shields.sum_tan_le_tan_sum` -- `∑ tan (f i) ≤ tan (∑ f i)`.
* `Shields.tan_nat_mul_ge`, `Shields.tan_nat_mul_gt` -- `r · tan θ ≤ tan (r θ)`, strict for
  `2 ≤ r`.

Used by `forgacs-tran-numerators`.

## Tags

tangent, superadditive, subadditive, angle sum
-/

open Real

namespace Shields

/-- **The tangent's defect of additivity, in closed form.**  Every sign below is read off
this. -/
theorem tan_add_sub {a b : ℝ} (ha : Real.cos a ≠ 0) (hb : Real.cos b ≠ 0)
    (hab : Real.cos (a + b) ≠ 0) :
    Real.tan (a + b) - Real.tan a - Real.tan b
      = Real.sin a * Real.sin b * Real.sin (a + b)
        / (Real.cos a * Real.cos b * Real.cos (a + b)) := by
  have hnum : Real.sin (a + b) * (Real.cos a * Real.cos b)
      - Real.sin a * (Real.cos (a + b) * Real.cos b)
      - Real.sin b * (Real.cos (a + b) * Real.cos a)
      = Real.sin a * Real.sin b * Real.sin (a + b) := by
    rw [Real.sin_add, Real.cos_add]; ring
  have key : Real.tan (a + b) - Real.tan a - Real.tan b
      = (Real.sin (a + b) * (Real.cos a * Real.cos b)
          - Real.sin a * (Real.cos (a + b) * Real.cos b)
          - Real.sin b * (Real.cos (a + b) * Real.cos a))
        / (Real.cos a * Real.cos b * Real.cos (a + b)) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    field_simp
  rw [key, hnum]

private theorem cos_pos_of_lt {x : ℝ} (h0 : 0 ≤ x) (h : x < π / 2) : 0 < Real.cos x :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩

/-- **The tangent is strictly superadditive on `(0, π/2)`.** -/
theorem tan_add_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < π / 2) :
    Real.tan a + Real.tan b < Real.tan (a + b) := by
  have hca : 0 < Real.cos a := cos_pos_of_lt ha.le (by linarith)
  have hcb : 0 < Real.cos b := cos_pos_of_lt hb.le (by linarith)
  have hcab : 0 < Real.cos (a + b) := cos_pos_of_lt (by linarith) hab
  have hsa : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hsb : 0 < Real.sin b :=
    Real.sin_pos_of_pos_of_lt_pi hb (by linarith [Real.pi_pos])
  have hsab : 0 < Real.sin (a + b) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h := tan_add_sub hca.ne' hcb.ne' hcab.ne'
  have hpos : 0 < Real.sin a * Real.sin b * Real.sin (a + b)
      / (Real.cos a * Real.cos b * Real.cos (a + b)) := by positivity
  linarith [h ▸ hpos]

/-- The superadditivity with the endpoints allowed, which is the form an induction needs. -/
theorem tan_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < π / 2) :
    Real.tan a + Real.tan b ≤ Real.tan (a + b) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp
  exact (tan_add_lt ha' hb' hab).le

/-- **A sum of tangents is at most the tangent of the sum**, on `(0, π/2)`. -/
theorem sum_tan_le_tan_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 ≤ f i) (hlt : ∑ i ∈ s, f i < π / 2) :
    ∑ i ∈ s, Real.tan (f i) ≤ Real.tan (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x t hx ih =>
      have hfx : 0 ≤ f x := hpos x (Finset.mem_insert_self x t)
      have hpt : ∀ i ∈ t, 0 ≤ f i := fun i hi => hpos i (Finset.mem_insert_of_mem hi)
      have hts : 0 ≤ ∑ i ∈ t, f i := Finset.sum_nonneg hpt
      rw [Finset.sum_insert hx] at hlt ⊢
      have hIH := ih hpt (by linarith)
      rw [Finset.sum_insert hx]
      calc Real.tan (f x) + ∑ i ∈ t, Real.tan (f i)
          ≤ Real.tan (f x) + Real.tan (∑ i ∈ t, f i) := by linarith
        _ ≤ Real.tan (f x + ∑ i ∈ t, f i) := tan_add_le hfx hts hlt

/-- **`tan (r θ) ≥ r · tan θ`** for a natural multiple. -/
theorem tan_nat_mul_ge : ∀ (r : ℕ) {θ : ℝ}, 0 < θ → (r : ℝ) * θ < π / 2 →
    (r : ℝ) * Real.tan θ ≤ Real.tan ((r : ℝ) * θ) := by
  intro r
  induction r with
  | zero => intro θ _ _; simp
  | succ m ih =>
      intro θ hθ hlt
      have hm : (m : ℝ) * θ < π / 2 := by push_cast at hlt ⊢; nlinarith [hθ]
      have hmnn : 0 ≤ (m : ℝ) * θ := by positivity
      have hIH := ih hθ hm
      have hstep : Real.tan ((m : ℝ) * θ) + Real.tan θ ≤ Real.tan ((m : ℝ) * θ + θ) :=
        tan_add_le hmnn hθ.le (by push_cast at hlt; linarith)
      have hcast : ((m + 1 : ℕ) : ℝ) * θ = (m : ℝ) * θ + θ := by push_cast; ring
      rw [hcast]
      push_cast
      linarith

/-- The same, strict once `2 ≤ r`. -/
theorem tan_nat_mul_gt {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ : 0 < θ) (hlt : (r : ℝ) * θ < π / 2) :
    (r : ℝ) * Real.tan θ < Real.tan ((r : ℝ) * θ) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) * θ := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    nlinarith
  have hm : (m : ℝ) * θ < π / 2 := by push_cast at hlt; nlinarith [hθ]
  have hIH := tan_nat_mul_ge m hθ hm
  have hstep : Real.tan ((m : ℝ) * θ) + Real.tan θ < Real.tan ((m : ℝ) * θ + θ) :=
    tan_add_lt hmpos hθ (by push_cast at hlt; linarith)
  have hcast : ((m + 1 : ℕ) : ℝ) * θ = (m : ℝ) * θ + θ := by push_cast; ring
  rw [hcast]
  push_cast
  linarith


/-! ### Axiom footprint -/

/-- info: 'Shields.sum_tan_le_tan_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_tan_le_tan_sum

/-- info: 'Shields.tan_nat_mul_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tan_nat_mul_gt

end Shields
