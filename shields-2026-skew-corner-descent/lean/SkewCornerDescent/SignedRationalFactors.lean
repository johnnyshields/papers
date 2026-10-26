/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SplitRationalFactors

/-!
# Rational factors under a signed change of coordinate

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`). A fixed
orientation sign reindexes the distinct rational labels and changes only the
unit, not the nonzero integer exponents or their signed degree. Sorry-free.
-/

namespace SkewCornerDescent

/-- A determinant orientation sign preserves a rational linear-factor expansion,
including negative exponents and coincident numerator/denominator cancellations. -/
theorem signedRationalFactors_change_coordinate {E : Type*} [Field E] [CharZero E]
    (y u w : E) (ε δ : ℤ) (s : Finset ℚ) (e : ℚ → ℤ) (d : ℕ)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (he : ∀ α ∈ s, e α ≠ 0) (hdegree : (∑ α ∈ s, e α) = d)
    (hfactor : y = (ε : E) * ∏ α ∈ s, (w - (α : E)) ^ e α)
    (hcoord : w = (δ : E) * u) :
    ∃ ε' : ℤ, ∃ s' : Finset ℚ, ∃ e' : ℚ → ℤ,
      (ε' = 1 ∨ ε' = -1) ∧ (∀ α ∈ s', e' α ≠ 0) ∧ (∑ α ∈ s', e' α) = d ∧
      (∀ α, e' α = e ((δ : ℚ) * α)) ∧
      (∀ α, α ∈ s' ↔ (δ : ℚ) * α ∈ s) ∧
      y = (ε' : E) * ∏ α ∈ s', (u - (α : E)) ^ e' α := by
  classical
  have hδQ : (δ : ℚ) ≠ 0 := by rcases hδ with rfl | rfl <;> norm_num
  have hδE : (δ : E) ≠ 0 := by rcases hδ with rfl | rfl <;> norm_num
  have hcancel (α : ℚ) : (δ : ℚ) * ((δ : ℚ) * α) = α := by
    rcases hδ with rfl | rfl <;> simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul,
      mul_neg, neg_neg]
  let f : ℚ ↪ ℚ := ⟨fun α => (δ : ℚ) * α, mul_right_injective₀ hδQ⟩
  let e' : ℚ → ℤ := fun α => e ((δ : ℚ) * α)
  have hexp (α : ℚ) : e' (f α) = e α := congrArg e (hcancel α)
  have hsign : ε * δ ^ d = 1 ∨ ε * δ ^ d = -1 :=
    Int.isUnit_iff.mp ((Int.isUnit_iff.mpr hε).mul ((Int.isUnit_iff.mpr hδ).pow d))
  have hsum : (∑ α ∈ s.map f, e' α) = d := by
    rw [Finset.sum_map]
    simpa only [hexp] using hdegree
  have hsplit (α : ℚ) : w - (α : E) = (δ : E) * (u - ((f α : ℚ) : E)) := by
    rw [hcoord]
    have hsquare : (δ : E) * (δ : E) = 1 := by
      rcases hδ with rfl | rfl <;> norm_num
    change (δ : E) * u - (α : E) = (δ : E) * (u - (((δ : ℚ) * α : ℚ) : E))
    rw [Rat.cast_mul, Rat.cast_intCast, mul_sub, ← mul_assoc, hsquare, one_mul]
  have hprod : (∏ α ∈ s, (δ : E) ^ e α) = (δ : E) ^ (∑ α ∈ s, e α) := by
    clear he hdegree hfactor hsum
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, zpow_zero]
    | @insert α s hα ih =>
      rw [Finset.prod_insert hα, Finset.sum_insert hα, zpow_add₀ hδE, ih]
  refine ⟨ε * δ ^ d, s.map f, e', hsign, ?_, hsum, fun _ => rfl, ?_, ?_⟩
  · intro α hα
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_map.mp hα
    rw [hexp]
    exact he β hβ
  · intro α
    constructor
    · intro hα
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_map.mp hα
      simpa only [f, Function.Embedding.coeFn_mk, hcancel] using hβ
    · intro hα
      exact Finset.mem_map.mpr ⟨(δ : ℚ) * α, hα, hcancel α⟩
  · rw [hfactor, Finset.prod_map]
    simp only [hexp]
    simp_rw [hsplit, mul_zpow]
    rw [Finset.prod_mul_distrib, hprod, hdegree, zpow_natCast, Int.cast_mul, Int.cast_pow,
      mul_assoc]

end SkewCornerDescent
