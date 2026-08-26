/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Subadditivity of the sine

The elementary inequality `Forgacs2017RationalDenominator` (17) —
`sin (α + β) < sin α + sin β` on `(0, π)` — together with the two forms in which
their Lemma 3 consumes it: over a finite family, and over a repeated angle.

## Main statements

* `sin_add_lt` — their (17).
* `abs_sin_sum_le` — the non-strict bound over a `Finset`, which holds for any
  real arguments once absolute values are taken.
* `sin_nat_mul_lt` — `sin (m x) < m sin x` for `m ≥ 2` inside `(0, π)`.

## Implementation notes

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

sine, subadditivity, angle system
-/

namespace ForgacsTran

open Real Set

/-- **`Forgacs2017RationalDenominator` (17).** -/
theorem sin_add_lt {x y : ℝ} (hx : x ∈ Ioo 0 π) (hy : y ∈ Ioo 0 π) :
    Real.sin (x + y) < Real.sin x + Real.sin y := by
  have hsx : 0 < Real.sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsy : 0 < Real.sin y := sin_pos_of_pos_of_lt_pi hy.1 hy.2
  have hcx : Real.cos x < 1 := by
    rcases (Real.cos_le_one x).lt_or_eq with h | h
    · exact h
    · exact absurd (Real.sin_eq_zero_iff_cos_eq.2 (Or.inl h)) hsx.ne'
  have hcy : Real.cos y < 1 := by
    rcases (Real.cos_le_one y).lt_or_eq with h | h
    · exact h
    · exact absurd (Real.sin_eq_zero_iff_cos_eq.2 (Or.inl h)) hsy.ne'
  rw [Real.sin_add]
  nlinarith

theorem abs_sin_add_le (x y : ℝ) : |Real.sin (x + y)| ≤ |Real.sin x| + |Real.sin y| := by
  rw [Real.sin_add]
  calc |Real.sin x * Real.cos y + Real.cos x * Real.sin y|
      ≤ |Real.sin x * Real.cos y| + |Real.cos x * Real.sin y| := abs_add_le _ _
    _ = |Real.sin x| * |Real.cos y| + |Real.cos x| * |Real.sin y| := by
        rw [abs_mul, abs_mul]
    _ ≤ |Real.sin x| * 1 + 1 * |Real.sin y| := by
        gcongr <;> [exact Real.abs_cos_le_one y; exact Real.abs_cos_le_one x]
    _ = |Real.sin x| + |Real.sin y| := by ring

theorem abs_sin_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    |Real.sin (∑ i ∈ s, f i)| ≤ ∑ i ∈ s, |Real.sin (f i)| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (abs_sin_add_le _ _).trans (by linarith)

/-- Over a family in `[0, π]` the absolute values may be dropped. -/
theorem sin_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, f i ∈ Icc 0 π) :
    Real.sin (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sin (f i) := by
  refine (le_abs_self _).trans ((abs_sin_sum_le s f).trans (le_of_eq ?_))
  refine Finset.sum_congr rfl fun i hi => abs_of_nonneg ?_
  exact Real.sin_nonneg_of_nonneg_of_le_pi (hf i hi).1 (hf i hi).2

theorem abs_sin_nat_mul_le (m : ℕ) (x : ℝ) : |Real.sin (m * x)| ≤ m * |Real.sin x| := by
  induction m with
  | zero => simp
  | succ m ih =>
      have : ((m : ℝ) + 1) * x = (m : ℝ) * x + x := by ring
      push_cast
      rw [this]
      exact (abs_sin_add_le _ _).trans (by linarith)

/-- `sin (m x) < m sin x` once `m ≥ 2` and the whole multiple stays inside
`(0, π)`. -/
theorem sin_nat_mul_lt {m : ℕ} {x : ℝ} (hm : 2 ≤ m) (hx : x ∈ Ioo 0 π) (hlt : (m : ℝ) * x < π) :
    Real.sin ((m : ℝ) * x) < m * Real.sin x := by
  induction m, hm using Nat.le_induction with
  | base =>
      have h2 : ((2 : ℕ) : ℝ) * x = x + x := by push_cast; ring
      rw [h2]
      have := sin_add_lt hx hx
      push_cast
      linarith
  | succ m hm ih =>
      have hx0 : (0 : ℝ) < x := hx.1
      have hstep : ((m : ℕ) + 1 : ℝ) * x = (m : ℝ) * x + x := by ring
      have hmlt : (m : ℝ) * x < π := by
        have : (m : ℝ) * x < ((m : ℝ) + 1) * x := by nlinarith
        push_cast at hlt
        linarith
      have hmpos : (0 : ℝ) < (m : ℝ) * x := by
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
      have hih := ih hmlt
      push_cast
      rw [hstep]
      have := sin_add_lt (x := (m : ℝ) * x) (y := x) ⟨hmpos, hmlt⟩ hx
      linarith

/-- `|sin (m x)| < m sin x` for `m ≥ 2` on `(0, π)`, with **no** constraint on
`m x`.  `sin_nat_mul_lt` needs `m x < π`; this one does not, and it is what the
merged branch value of `FTBranchAngleBound` is compared against. -/
theorem abs_sin_nat_mul_lt {m : ℕ} {x : ℝ} (hm : 2 ≤ m) (hx : x ∈ Ioo 0 π) :
    |Real.sin ((m : ℝ) * x)| < m * Real.sin x := by
  have hsx : 0 < Real.sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hcx : |Real.cos x| < 1 := by
    rcases lt_or_eq_of_le (abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩) with h | h
    · exact h
    · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h with h' | h'
      · exact absurd (Real.sin_eq_zero_iff_cos_eq.2 (Or.inl h')) hsx.ne'
      · exact absurd (Real.sin_eq_zero_iff_cos_eq.2 (Or.inr h')) hsx.ne'
  induction m, hm using Nat.le_induction with
  | base =>
      have h2 : ((2 : ℕ) : ℝ) * x = x + x := by push_cast; ring
      rw [h2, Real.sin_add]
      have hrw : Real.sin x * Real.cos x + Real.cos x * Real.sin x
          = (2 * Real.sin x) * Real.cos x := by ring
      rw [hrw, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.sin x)]
      have := mul_lt_mul_of_pos_left hcx (by linarith : (0:ℝ) < 2 * Real.sin x)
      push_cast
      linarith
  | succ m hm ih =>
      have hstep : ((m : ℕ) + 1 : ℝ) * x = (m : ℝ) * x + x := by ring
      push_cast
      rw [hstep]
      have h1 := abs_sin_add_le ((m : ℝ) * x) x
      rw [abs_of_pos hsx] at h1
      linarith [ih]

end ForgacsTran
