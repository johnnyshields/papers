/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicClosureWindows

/-!
# Complete short-window inventories of a closure word

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original
coefficients» (`sec:dual`, `lem:dual-identities`, `eq:dual-short`). The closure word
is constructed from its literal periodic prefix. All crossing and noncrossing starts
are counted, including repeated occurrences of the same response. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

variable {R : Type*}

/-- Repeating a cycle repeats its sum with the full multiplicity. -/
theorem zmod_sum_range_mul {n : ℕ} [NeZero n] [AddCommMonoid R]
    (f : ZMod n → R) (k : ℕ) :
    (∑ i ∈ Finset.range (k * n), f (i : ZMod n)) = k • ∑ i, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have he : (∑ i ∈ Finset.range n, f ((k * n + i : ℕ) : ZMod n)) = ∑ i, f i := by
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
      exact (zmod_sum_eq_range f).symm
    rw [he, succ_nsmul]

/-- Every noncrossing window has the same product as the original periodic word. -/
theorem closureWord_noncrossing_product {n m k : ℕ} [NeZero n] [NeZero m]
    [CommMonoid R] (f : ZMod n → R) (S : R) {i : ℕ} (hi : i < k * n) :
    windowProduct (closureWord f S (k * n + m)) 1 m (i : ZMod (k * n + m)) =
      windowProduct f 1 m (i : ZMod n) := by
  unfold windowProduct
  apply Finset.prod_congr rfl
  intro a ha
  exact closureWord_noncrossing f S hi (Finset.mem_range.mp ha)

/-- The short detector contains `k` complete periodic inventories and all `m` crossings. -/
theorem inverseWindowSum_closure_short {n m k : ℕ} [NeZero n] [NeZero m]
    [NeZero (k * n + m)] [Semifield R] (f : ZMod n → R) (S : R)
    (hmn : m ≤ n) (hk : 0 < k) :
    inverseWindowSum (closureWord f S (k * n + m)) m =
      k • inverseWindowSum f m +
        m • ((∏ i ∈ Finset.range (m - 1), f (i : ZMod n)) * S)⁻¹ := by
  classical
  unfold inverseWindowSum
  rw [zmod_sum_eq_range, Finset.sum_range_add]
  have hn : (∑ i ∈ Finset.range (k * n),
      (windowProduct (closureWord f S (k * n + m)) 1 m
        (i : ZMod (k * n + m)))⁻¹) =
      k • ∑ i : ZMod n, (windowProduct f 1 m i)⁻¹ := by
    calc
      _ = ∑ i ∈ Finset.range (k * n), (windowProduct f 1 m (i : ZMod n))⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [closureWord_noncrossing_product f S (Finset.mem_range.mp hi)]
      _ = _ := zmod_sum_range_mul (fun i : ZMod n => (windowProduct f 1 m i)⁻¹) k
  have hc : (∑ i ∈ Finset.range m,
      (windowProduct (closureWord f S (k * n + m)) 1 m
        ((k * n + i : ℕ) : ZMod (k * n + m)))⁻¹) =
      m • ((∏ i ∈ Finset.range (m - 1), f (i : ZMod n)) * S)⁻¹ := by
    calc
      _ = ∑ _i ∈ Finset.range m, (∏ j : ZMod m, remainderClosure f S m j)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [closureWord_crossing_product f S hmn hk (Finset.mem_range.mp hi)]
      _ = _ := by
        unfold remainderClosure
        rw [closureWord_product]
        simp only [Finset.sum_const, Finset.card_range]
  rw [hn, hc]

/-- The full word product contains all repeated periods, the literal prefix, and the closure. -/
theorem closureWord_product_mul_add {n m k : ℕ} [NeZero n] [NeZero m]
    [NeZero (k * n + m)] [CommMonoid R] (f : ZMod n → R) (S : R) :
    (∏ i : ZMod (k * n + m), closureWord f S (k * n + m) i) =
      (∏ i : ZMod n, f i) ^ k *
        (∏ i ∈ Finset.range (m - 1), f (i : ZMod n)) * S := by
  rw [closureWord_product]
  have hm : k * n + m - 1 = k * n + (m - 1) := by have := NeZero.ne m; omega
  have he : (∏ i ∈ Finset.range (k * n + m - 1), f (i : ZMod n)) =
      windowProduct f 1 (k * n + (m - 1)) 0 := by
    simp only [windowProduct, zero_add, nsmul_eq_mul, mul_one, hm]
  rw [he, zmod_windowProduct_mul_add]
  simp only [windowProduct, zero_add, nsmul_eq_mul, mul_one]

/-- All full-cycle starts are retained; equal products do not collapse their multiplicity. -/
theorem inverseWindowSum_closure_full {n m k : ℕ} [NeZero n] [NeZero m]
    [NeZero (k * n + m)] [Semifield R] (f : ZMod n → R) (S : R) :
    inverseWindowSum (closureWord f S (k * n + m)) (k * n + m) =
      (k * n + m) • ((∏ i : ZMod n, f i) ^ k *
        (∏ i ∈ Finset.range (m - 1), f (i : ZMod n)) * S)⁻¹ := by
  unfold inverseWindowSum
  rw [zmod_sum_inverse_full_cycle, closureWord_product_mul_add]

end SkewCornerDescent.CyclicWindows
