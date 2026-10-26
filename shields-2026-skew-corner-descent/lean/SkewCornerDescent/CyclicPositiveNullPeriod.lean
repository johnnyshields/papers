/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.PositiveWindowEquality
import SkewCornerDescent.CyclicDetectors

/-!
# Period rigidity of one-active positive literal inventories

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`). Literal
signed class counts produce the exact log product balance. A zero full-period
detector produces the exact reciprocal mean, hence the completed response cycle
has the period of the supplied full window. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

private theorem sum_one_class {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (d : ℤ) (f : α → ℝ) :
    (∑ x, ((if x = a then d else 0 : ℤ) : ℝ) * f x) = (d : ℝ) * f a := by
  simp [ite_mul]

/-- A one-active complete literal inventory with zero full-period detector has
its actual completed response cycle periodic. Neither log balance nor its mean
identity is an extra assumption. -/
theorem one_active_positive_null_period {α : Type*} [Fintype α] [DecidableEq α]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s)
    (word : ZMod (r * d) → α) (response : α → ℝ) (hpos : ∀ a, 0 < response a)
    (active : α)
    (hsingle : ∀ a, classDefect word 1 d s (r * s - 1) 0 a =
      if a = active then (d : ℤ) else 0)
    (hzero : windowDefect (response ∘ word) response
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * d) = 0) :
    Function.Periodic (closureWord (response ∘ word) (response active)
      (k * (r * d) + r * s)) (r * d : ℕ) := by
  classical
  let f := response ∘ word
  let B := k * (r * d) + r * s
  let b := k * d + s
  let P := ∏ i, f i
  let T := windowProduct f 1 (B - 1) 0
  let Q := closureWord f (response active) B
  have hf (i) : 0 < f i := hpos (word i)
  have hP : 0 < P := Finset.prod_pos fun i _ => hf i
  have hT : 0 < T := Finset.prod_pos fun _ _ => hf _
  have hQ (i) : 0 < Q i := by
    dsimp only [Q, closureWord]
    split_ifs
    · exact hpos active
    · exact hf _
  have hd : 0 < d := Nat.pos_of_ne_zero (by
    intro hd
    have hn := NeZero.ne (r * d)
    exact hn (by rw [hd, Nat.mul_zero]))
  have hlogP : Real.log P = ∑ i, Real.log (f i) := Real.log_prod fun i _ => (hf i).ne'
  have hTprod : (∏ i ∈ Finset.range (B - 1), f (i : ZMod (r * d))) = T := by
    simp only [T, windowProduct, zero_add, nsmul_eq_mul, mul_one]
  have hlogQ : (∑ i, Real.log (Q i)) = Real.log T + Real.log (response active) := by
    rw [← Real.log_prod (fun i _ => (hQ i).ne'), closureWord_product, hTprod]
    exact Real.log_mul hT.ne' (hpos active).ne'
  have hbalance := cyclic_signed_log_balance (k := k) hr hs word response hpos
  change (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : ℝ) *
    Real.log ((T * response a)⁻¹)) = -(b : ℝ) * ∑ i, Real.log (f i) at hbalance
  simp_rw [hsingle] at hbalance
  rw [sum_one_class, Real.log_inv, Real.log_mul hT.ne' (hpos active).ne'] at hbalance
  simp only [Int.cast_natCast] at hbalance
  have hbal : (B : ℝ) * Real.log P = (r * d : ℕ) * ∑ i, Real.log (Q i) := by
    rw [hlogP, hlogQ]
    have he : (B : ℝ) = (r : ℝ) * (b : ℝ) := by
      dsimp only [B, b]
      push_cast
      ring
    rw [he, Nat.cast_mul]
    have hsigned : (b : ℝ) * (∑ i, Real.log (f i)) =
        (d : ℝ) * (Real.log T + Real.log (response active)) := by linarith
    calc
      (r : ℝ) * (b : ℝ) * (∑ i, Real.log (f i)) =
          (r : ℝ) * ((b : ℝ) * (∑ i, Real.log (f i))) := by ring
      _ = (r : ℝ) * ((d : ℝ) * (Real.log T + Real.log (response active))) := by rw [hsigned]
      _ = _ := by ring
  have hsumP : inverseWindowSum f (r * d) = (r * d : ℕ) * P⁻¹ := by
    unfold inverseWindowSum
    simp_rw [zmod_windowProduct_cycle]
    simp only [P, Finset.sum_const, Finset.card_univ, ZMod.card (r * d), nsmul_eq_mul]
  have hsumQ : (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : ℝ) *
      inverseWindowSum (closureWord f (response a) B) (r * d)) =
      (d : ℝ) * inverseWindowSum Q (r * d) := by
    simp_rw [hsingle]
    exact sum_one_class active (d : ℤ) _
  change (b : ℝ) * inverseWindowSum f (r * d) -
    (∑ a, (classDefect word 1 d s (r * s - 1) 0 a : ℝ) *
      inverseWindowSum (closureWord f (response a) B) (r * d)) = 0 at hzero
  rw [hsumP, hsumQ] at hzero
  have heq := sub_eq_zero.mp hzero
  have hcount : (b : ℝ) * (r * d : ℕ) = (d : ℝ) * (B : ℝ) := by
    dsimp only [b, B]
    push_cast
    ring
  have hmean : P * inverseWindowSum Q (r * d) = (B : ℝ) := by
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd) : (d : ℝ) ≠ 0)
    calc
      (d : ℝ) * (P * inverseWindowSum Q (r * d)) =
          P * ((d : ℝ) * inverseWindowSum Q (r * d)) := by ring
      _ = P * ((b : ℝ) * ((r * d : ℕ) * P⁻¹)) := by rw [← heq]
      _ = ((b : ℝ) * (r * d : ℕ)) * (P * P⁻¹) := by ring
      _ = (d : ℝ) * (B : ℝ) := by rw [mul_inv_cancel₀ hP.ne', mul_one, hcount]
  exact positive_reciprocal_inventory_periodic Q hQ (r * d) P hP hbal hmean

/-- Coprime complete source counts reduce the actual full-window period to
the selected multiplicity, retaining the entire completed response cycle. -/
theorem one_active_positive_null_primitive {α : Type*} [Fintype α] [DecidableEq α]
    {r d s k : ℕ} [NeZero (r * d)] [NeZero (k * (r * d) + r * s)]
    (hr : 0 < r) (hs : 0 < s) (hcoprime : Nat.Coprime (k * d + s) d)
    (word : ZMod (r * d) → α) (response : α → ℝ) (hpos : ∀ a, 0 < response a)
    (active : α)
    (hsingle : ∀ a, classDefect word 1 d s (r * s - 1) 0 a =
      if a = active then (d : ℤ) else 0)
    (hzero : windowDefect (response ∘ word) response
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s)
      (k * (r * d) + r * s) (r * d) = 0) :
    Function.Periodic (closureWord (response ∘ word) (response active)
      (k * (r * d) + r * s)) (r : ZMod (k * (r * d) + r * s)) := by
  have hp := one_active_positive_null_period hr hs word response hpos active hsingle hzero
  have hg := zmod_periodic_gcd _ hp
  have hB : k * (r * d) + r * s = r * (k * d + s) := by ring
  have hgc : Nat.gcd (r * d) (k * (r * d) + r * s) = r := by
    rw [hB, Nat.gcd_mul_left, hcoprime.symm.gcd_eq_one, Nat.mul_one]
  rwa [hgc] at hg

end SkewCornerDescent.CyclicWindows
