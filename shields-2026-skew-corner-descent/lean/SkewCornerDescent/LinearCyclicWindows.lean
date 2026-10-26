/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.LinearWindows
import SkewCornerDescent.CyclicFiniteIntervals

/-!
# Extra linear starts form a complete cyclic inventory

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Periodic extensions retain every linear start and every cyclic wrap, including windows
longer than one cyclic period.
Sorry-free.
-/

namespace SkewCornerDescent

open CyclicWindows

/-- An offset inverse product is the complete inverse cyclic product at that start. -/
theorem linearOffset_inverse_product {n : ℕ} [NeZero n] {F : Type*} [Field F]
    (f : ZMod n → F) (j s : ℕ) :
    (∏ a : Fin j, (f ((s + a.val : ℕ) : ZMod n))⁻¹) =
      (windowProduct f 1 j (s : ZMod n))⁻¹ := by
  unfold windowProduct
  rw [← Fin.prod_univ_eq_prod_range, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro a _
  simp only [Nat.cast_add, nsmul_eq_mul, mul_one]

/-- The linear windows of an actual positional truncation of a cyclic word retain
exactly its eligible start range. No complete-period or distinct-value assumption is used. -/
theorem linearInverseWindowSum_cyclic_truncation {n L : ℕ} [NeZero n]
    {F : Type*} [Field F] (f : ZMod n → F) (j : ℕ) :
    linearInverseWindowSum (fun k : Fin L => f (k.val : ZMod n)) j =
      ∑ s ∈ Finset.range (L + 1 - j), (windowProduct f 1 j (s : ZMod n))⁻¹ := by
  classical
  unfold linearInverseWindowSum
  change (∑ s : Fin (L + 1 - j),
    ∏ a : Fin j, (f ((s.val + a.val : ℕ) : ZMod n))⁻¹) = _
  simp_rw [linearOffset_inverse_product]
  exact Fin.sum_univ_eq_sum_range
    (fun s : ℕ => (windowProduct f 1 j (s : ZMod n))⁻¹) (L + 1 - j)

/-- Adding one complete period adds exactly one full cyclic inverse inventory, also
when a window wraps repeatedly and when the shorter linear word has no eligible start. -/
theorem linearInverseWindowSum_add_period {n L : ℕ} [NeZero n]
    {F : Type*} [Field F] (f : ZMod n → F) (j : ℕ) (hj : j ≤ L + 1) :
    linearInverseWindowSum (fun k : Fin (L + n) => f (k.val : ZMod n)) j =
      linearInverseWindowSum (fun k : Fin L => f (k.val : ZMod n)) j +
        inverseWindowSum f j := by
  rw [linearInverseWindowSum_cyclic_truncation, linearInverseWindowSum_cyclic_truncation,
    show L + n + 1 - j = (L + 1 - j) + n by omega, Finset.sum_range_add]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  unfold inverseWindowSum
  have he : (∑ a : Fin n,
      (windowProduct f 1 j (((L + 1 - j) + a.val : ℕ) : ZMod n))⁻¹) =
      ∑ a : Fin n,
        (windowProduct f 1 j ((L + 1 - j : ℕ) + ZMod.finEquiv n a))⁻¹ := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Nat.cast_add, CyclicWindows.finEquiv_eq_natCast]
  rw [he]
  exact ((ZMod.finEquiv n).toEquiv.trans
    (Equiv.addLeft ((L + 1 - j : ℕ) : ZMod n))).sum_comp
      (fun s : ZMod n => (windowProduct f 1 j s)⁻¹)

end SkewCornerDescent
