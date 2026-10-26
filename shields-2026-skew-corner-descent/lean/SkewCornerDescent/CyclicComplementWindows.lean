/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicClosureInventories

/-!
# Complementary windows of the full closure cycle

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original
coefficients» (`sec:dual`, `lem:dual-identities`, `eq:dual-first`). The complements
of crossing full-period windows are identified by actual positions in the constructed
closure word. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

variable {R : Type*}

/-- A window lying before the closure is literally a periodic window. -/
theorem closureWord_prefix_product {n B j i : ℕ} [CommMonoid R]
    (f : ZMod n → R) (S : R) (hij : i + j < B) :
    windowProduct (closureWord f S B) 1 j (i : ZMod B) =
      windowProduct f 1 j (i : ZMod n) := by
  unfold windowProduct
  apply Finset.prod_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  simp only [nsmul_eq_mul, mul_one, ← Nat.cast_add]
  unfold closureWord
  rw [ZMod.val_natCast_of_lt (by omega : i + a < B),
    ite_eq_right (by omega : i + a ≠ B - 1)]

/-- A full-period noncrossing start has the complete original period product. -/
theorem closureWord_period_noncrossing {n C : ℕ} [NeZero n] [CommMonoid R]
    (f : ZMod n → R) (S : R) {i : ℕ} (hi : i < C) :
    windowProduct (closureWord f S (n + C)) 1 n (i : ZMod (n + C)) =
      ∏ x : ZMod n, f x := by
  rw [closureWord_prefix_product f S (by omega : i + n < n + C),
    zmod_windowProduct_cycle]

/-- The complement of a crossing period window is the forward periodic `C`-window. -/
theorem closureWord_crossing_complement {n C : ℕ} [NeZero n] [NeZero (n + C)]
    [CommMonoid R] (f : ZMod n → R) (S : R) {i : ℕ} (hi : i < n) :
    windowProduct (closureWord f S (n + C)) 1 n ((C + i : ℕ) : ZMod (n + C)) *
      windowProduct f 1 C (i : ZMod n) =
        ∏ x : ZMod (n + C), closureWord f S (n + C) x := by
  have hshift : ((C + i : ℕ) : ZMod (n + C)) + n • (1 : ZMod (n + C)) =
      (i : ZMod (n + C)) := by
    simp only [nsmul_eq_mul, mul_one]
    calc
      _ = ((n + C : ℕ) : ZMod (n + C)) + i := by push_cast; ring
      _ = _ := by simp
  have he := windowProduct_add (closureWord f S (n + C)) 1 n C
    ((C + i : ℕ) : ZMod (n + C))
  rw [hshift, closureWord_prefix_product f S (by omega : i + C < n + C),
    zmod_windowProduct_cycle] at he
  exact he.symm

/-- Inverting a crossing window divides its actual complement by the complete product. -/
theorem closureWord_crossing_inverse {n C : ℕ} [NeZero n] [NeZero (n + C)]
    [Field R] (f : ZMod n → R) (S : R) {i : ℕ} (hi : i < n)
    (hprod : (∏ x : ZMod (n + C), closureWord f S (n + C) x) ≠ 0) :
    (windowProduct (closureWord f S (n + C)) 1 n
      ((C + i : ℕ) : ZMod (n + C)))⁻¹ =
      windowProduct f 1 C (i : ZMod n) /
        (∏ x : ZMod (n + C), closureWord f S (n + C) x) := by
  have he := closureWord_crossing_complement (C := C) f S hi
  have hw : windowProduct (closureWord f S (n + C)) 1 n
      ((C + i : ℕ) : ZMod (n + C)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    exact hprod he.symm
  field_simp [hprod, hw]
  simpa only [mul_comm] using he.symm

/-- The full-period inventory consists of `C` noncrossings and exactly `n` complements. -/
theorem inverseWindowSum_closure_period {n C : ℕ} [NeZero n] [NeZero (n + C)]
    [Field R] (f : ZMod n → R) (S : R)
    (hprod : (∏ x : ZMod (n + C), closureWord f S (n + C) x) ≠ 0) :
    inverseWindowSum (closureWord f S (n + C)) n =
      C • (∏ x : ZMod n, f x)⁻¹ +
        (∑ i : ZMod n, windowProduct f 1 C i) /
          (∏ x : ZMod (n + C), closureWord f S (n + C) x) := by
  classical
  unfold inverseWindowSum
  rw [zmod_sum_eq_range]
  have hsplit := Finset.sum_range_add
    (fun i => (windowProduct (closureWord f S (n + C)) 1 n
      (i : ZMod (n + C)))⁻¹) C n
  rw [← Nat.add_comm n C] at hsplit
  rw [hsplit]
  have hn : (∑ i ∈ Finset.range C,
      (windowProduct (closureWord f S (n + C)) 1 n (i : ZMod (n + C)))⁻¹) =
      C • (∏ x : ZMod n, f x)⁻¹ := by
    calc
      _ = ∑ _i ∈ Finset.range C, (∏ x : ZMod n, f x)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [closureWord_period_noncrossing f S (Finset.mem_range.mp hi)]
      _ = _ := by simp only [Finset.sum_const, Finset.card_range]
  have hc : (∑ i ∈ Finset.range n,
      (windowProduct (closureWord f S (n + C)) 1 n
        ((C + i : ℕ) : ZMod (n + C)))⁻¹) =
      (∑ i : ZMod n, windowProduct f 1 C i) /
        (∏ x : ZMod (n + C), closureWord f S (n + C) x) := by
    calc
      _ = ∑ i ∈ Finset.range n, windowProduct f 1 C (i : ZMod n) /
          (∏ x : ZMod (n + C), closureWord f S (n + C) x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [closureWord_crossing_inverse f S (Finset.mem_range.mp hi) hprod]
      _ = _ := by rw [← Finset.sum_div, ← zmod_sum_eq_range]
  rw [hn, hc]

end SkewCornerDescent.CyclicWindows
