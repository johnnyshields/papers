/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicLogBalance
import SkewCornerDescent.CyclicLastInventory
import SkewCornerDescent.SignedSupportWeights

/-!
# The signed-support last detector from literal cyclic counts

Supports `shields-2026-skew-corner-descent.tex` (`lem:two-support`,
`cor:one-positive-short`). On one positive assignment, complete class counts
produce the logarithmic product balance and the exact normalization of the last
inventory. Arbitrarily many negative supports are allowed. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open PhaseInventory
open scoped BigOperators

/-- A positive cyclic assignment with one positive signed class and a distinct
negative class has strictly positive last detector. The logarithmic balance is
proved from the literal word, not supplied as an analytic hypothesis. -/
theorem one_positive_cyclic_last_pos {α : Type*} [Fintype α] [DecidableEq α]
    {r d s k : ℕ} [NeZero (r * d)] (hr : 0 < r) (hs : 0 < s)
    (word : ZMod (r * d) → α) (response : α → ℝ) (hpos : ∀ a, 0 < response a)
    (p : α)
    (hothers : ∀ a, a ≠ p → classDefect word 1 d s (r * s - 1) 0 a ≤ 0)
    (hnegative : ∃ a, classDefect word 1 d s (r * s - 1) 0 a < 0 ∧ response a ≠ response p) :
    0 < lastWindowDefect (response ∘ word) response
      (classDefect word 1 d s (r * s - 1) 0) (k * d + s) (k * (r * d) + r * s) := by
  classical
  let f := response ∘ word
  let n := r * d
  let b := k * d + s
  let B := k * (r * d) + r * s
  let T := windowProduct f 1 (B - 1) 0
  let e := classDefect word 1 d s (r * s - 1) 0
  let weight := fun a => (e a : ℝ) / (d : ℝ)
  let Z := fun a => (T * response a)⁻¹
  let V := fun i => (windowProduct f 1 B i)⁻¹
  let meanWeight := fun _ : ZMod (r * d) => (n : ℝ)⁻¹
  have hd : 0 < d := by
    have hn := Nat.pos_of_ne_zero (NeZero.ne (r * d))
    nlinarith
  have hn : 0 < (n : ℝ) := by
    dsimp only [n]
    exact_mod_cast Nat.mul_pos hr hd
  have hb : 0 < (b : ℝ) := by
    dsimp only [b]
    exact_mod_cast (show 0 < k * d + s by omega)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hf : ∀ i, 0 < f i := fun i => hpos (word i)
  have hT : 0 < T := Finset.prod_pos fun _ _ => hf _
  have hZ : ∀ a, 0 < Z a := fun a => inv_pos.mpr (mul_pos hT (hpos a))
  have hV : ∀ i, 0 < V i := fun i => inv_pos.mpr (Finset.prod_pos fun _ _ => hf _)
  have he : ∑ a, (e a : ℝ) = (d : ℝ) := by
    exact_mod_cast sum_reduced_classDefect hr hs word
  have hweight : ∑ a, weight a = 1 := by
    dsimp only [weight]
    rw [← Finset.sum_div, he, div_self hdR.ne']
  have hothers' : ∀ a, a ≠ p → weight a ≤ 0 := by
    intro a hap
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hothers a hap) hdR.le
  have hnegative' : ∃ a, weight a < 0 ∧ Z a ≠ Z p := by
    obtain ⟨a, hea, hresponse⟩ := hnegative
    refine ⟨a, div_neg_of_neg_of_pos (by exact_mod_cast hea) hdR, ?_⟩
    intro heq
    exact hresponse (mul_left_cancel₀ hT.ne' (inv_inj.mp heq))
  have hw : ∀ i ∈ (Finset.univ : Finset (ZMod (r * d))), 0 ≤ meanWeight i :=
    fun _ _ => inv_nonneg.mpr hn.le
  have hwone : ∑ i : ZMod (r * d), meanWeight i = 1 := by
    simp only [meanWeight, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    change (n : ℝ) * (n : ℝ)⁻¹ = 1
    exact mul_inv_cancel₀ hn.ne'
  have hlogs := cyclic_signed_log_balance (k := k) hr hs word response hpos
  change (∑ a, (e a : ℝ) * Real.log (Z a)) =
    -(b : ℝ) * ∑ i, Real.log (f i) at hlogs
  have hwindows := sum_log_inverse_windowProduct f hf 1 B
  change (∑ i, Real.log (V i)) = -(B : ℝ) * ∑ i, Real.log (f i) at hwindows
  have hsumweight : (∑ a, weight a * Real.log (Z a)) =
      (d : ℝ)⁻¹ * ∑ a, (e a : ℝ) * Real.log (Z a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [weight]
    rw [div_eq_mul_inv]
    ring
  have hbalance : ∑ i, meanWeight i * Real.log (V i) = ∑ a, weight a * Real.log (Z a) := by
    change ∑ i, (n : ℝ)⁻¹ * Real.log (V i) = _
    rw [← Finset.mul_sum, hsumweight, hlogs, hwindows]
    dsimp only [n, b, B]
    push_cast
    field_simp
  have hstrict := SinglePositive.finite_mean_one_positive_weights weight Z p
    hweight hothers' hZ hnegative' Finset.univ meanWeight V hw hwone
    (fun i _ => hV i) hbalance
  have hsumZ : (∑ a, weight a * Z a) =
      (d : ℝ)⁻¹ * T⁻¹ * closureLabelSum e response := by
    unfold closureLabelSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [weight, Z]
    rw [div_eq_mul_inv, mul_inv]
    ring
  have hmean : (∑ i, meanWeight i * V i) = (n : ℝ)⁻¹ * inverseWindowSum f B := by
    change ∑ i, (n : ℝ)⁻¹ * V i = _
    rw [← Finset.mul_sum]
    rfl
  have hprefix : (∏ i ∈ Finset.range (B - 1), f (i : ZMod (r * d))) = T := by
    simp only [T, windowProduct, zero_add, nsmul_eq_mul, mul_one]
  have hnormal : lastWindowDefect f response e b B =
      (b : ℝ) * (n : ℝ) * ((∑ i, meanWeight i * V i) - ∑ a, weight a * Z a) := by
    rw [lastWindowDefect, hprefix, hmean, hsumZ]
    dsimp only [n, b, B]
    push_cast
    field_simp
  change 0 < lastWindowDefect f response e b B
  rw [hnormal]
  exact mul_pos (mul_pos hb hn) hstrict

end SkewCornerDescent.CyclicWindows
