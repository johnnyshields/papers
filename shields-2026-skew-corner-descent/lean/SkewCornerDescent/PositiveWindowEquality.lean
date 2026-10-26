/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicLogBalance
import Mathlib.Tactic

/-!
# Equality rigidity of positive reciprocal window inventories

Supports `shields-2026-skew-corner-descent.tex` (`lem:positive-support`). The
logarithmic product balance and the exact arithmetic mean force every positively
weighted normalized window to equal one. Sliding then gives the actual response
period, without independence of response values. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

/-- Strict positive weighted logarithmic balance excludes arithmetic-mean
identity as soon as one normalized window differs from one. -/
theorem positive_log_balance_strict {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hx : ∀ i ∈ s, 0 < x i)
    (hlog : (∑ i ∈ s, w i * Real.log (x i)) = 0)
    (hne : ∃ i ∈ s, x i ≠ 1) :
    (∑ i ∈ s, w i) < ∑ i ∈ s, w i * x i := by
  have hle (i) (hi : i ∈ s) :
      w i * Real.log (x i) ≤ w i * (x i - 1) :=
    mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (hx i hi)) (hw i hi).le
  obtain ⟨i, hi, hxi⟩ := hne
  have hlt : w i * Real.log (x i) < w i * (x i - 1) :=
    mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (hx i hi) hxi) (hw i hi)
  have hs := Finset.sum_lt_sum hle ⟨i, hi, hlt⟩
  rw [hlog] at hs
  have hsum : (∑ i ∈ s, w i * (x i - 1)) =
      (∑ i ∈ s, w i * x i) - ∑ i ∈ s, w i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hsum] at hs
  exact sub_pos.mp hs

/-- Exact positive log and mean balance makes every normalized window one. -/
theorem positive_log_balance_eq_one {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hx : ∀ i ∈ s, 0 < x i)
    (hlog : (∑ i ∈ s, w i * Real.log (x i)) = 0)
    (hmean : (∑ i ∈ s, w i * x i) = ∑ i ∈ s, w i) :
    ∀ i ∈ s, x i = 1 := by
  intro i hi
  by_contra hn
  have h := positive_log_balance_strict s w x hw hx hlog ⟨i, hi, hn⟩
  rw [hmean] at h
  exact (lt_irrefl _ h)

/-- Equal positive complete window products force the literal cyclic response
values periodic at the window length. Every start and crossing window remains. -/
theorem positive_equal_windows_periodic {M : ℕ} [NeZero M]
    (Q : ZMod M → ℝ) (hQ : ∀ i, 0 < Q i) (n : ℕ)
    (hprod : ∀ i, CyclicWindows.windowProduct Q 1 n i =
      CyclicWindows.windowProduct Q 1 n 0) :
    ∀ i, Q (i + (n : ZMod M)) = Q i := by
  intro i
  have h := CyclicWindows.windowSum_slide (Real.log ∘ Q) 1 n i
  have hw (j) : CyclicWindows.windowSum (Real.log ∘ Q) 1 n j =
      Real.log (CyclicWindows.windowProduct Q 1 n 0) := by
    rw [← CyclicWindows.log_windowProduct Q hQ, hprod]
  rw [hw, hw] at h
  simp only [Function.comp_apply, nsmul_eq_mul, mul_one] at h
  have hlog : Real.log (Q (i + (n : ZMod M))) = Real.log (Q i) := by linarith
  have he := congrArg Real.exp hlog
  rwa [Real.exp_log (hQ _), Real.exp_log (hQ _)] at he

/-- The exact mean and product-log balances of a positive full reciprocal
inventory force response periodicity at its window length. -/
theorem positive_reciprocal_inventory_periodic {M : ℕ} [NeZero M]
    (Q : ZMod M → ℝ) (hQ : ∀ i, 0 < Q i) (n : ℕ) (A : ℝ) (hA : 0 < A)
    (hbalance : (M : ℝ) * Real.log A = (n : ℝ) * ∑ i, Real.log (Q i))
    (hmean : A * (∑ i, (CyclicWindows.windowProduct Q 1 n i)⁻¹) = (M : ℝ)) :
    ∀ i, Q (i + (n : ZMod M)) = Q i := by
  let x := fun i => A * (CyclicWindows.windowProduct Q 1 n i)⁻¹
  have hp (i) : 0 < CyclicWindows.windowProduct Q 1 n i :=
    Finset.prod_pos fun _ _ => hQ _
  have hx (i) : 0 < x i := mul_pos hA (inv_pos.mpr (hp i))
  have hlog (i) : Real.log (x i) = Real.log A +
      Real.log ((CyclicWindows.windowProduct Q 1 n i)⁻¹) :=
    Real.log_mul hA.ne' (inv_ne_zero (hp i).ne')
  have hsumlog : (∑ i, Real.log (x i)) = 0 := by
    simp_rw [hlog]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card M,
      CyclicWindows.sum_log_inverse_windowProduct Q hQ]
    simp only [nsmul_eq_mul]
    linarith
  have hsumx : (∑ i, x i) = (M : ℝ) := by
    dsimp only [x]
    rw [← Finset.mul_sum, hmean]
  have hall := positive_log_balance_eq_one (Finset.univ : Finset (ZMod M))
    (fun _ => (1 : ℝ)) x (fun _ _ => zero_lt_one) (fun i _ => hx i)
    (by simpa only [one_mul] using hsumlog)
    (by simpa only [one_mul, Finset.sum_const, Finset.card_univ, ZMod.card M,
      nsmul_eq_mul, mul_one]
      using hsumx)
  have hwindow (i) : CyclicWindows.windowProduct Q 1 n i = A := by
    have h := hall i (Finset.mem_univ i)
    change A * (CyclicWindows.windowProduct Q 1 n i)⁻¹ = 1 at h
    have he := congrArg (fun a : ℝ => a * CyclicWindows.windowProduct Q 1 n i) h
    rw [mul_assoc, inv_mul_cancel₀ (hp i).ne', mul_one, one_mul] at he
    exact he.symm
  apply positive_equal_windows_periodic Q hQ n
  intro i
  rw [hwindow, hwindow]

end SkewCornerDescent
