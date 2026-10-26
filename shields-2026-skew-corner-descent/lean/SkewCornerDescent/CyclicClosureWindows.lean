/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicWindows

/-!
# Crossing windows in the complete cyclic closure word

Supports `shields-2026-skew-corner-descent.tex`, «Cyclic inventories and original
coefficients» (`sec:dual`, `lem:dual-identities`). The word is constructed as repeated copies
of its period, followed by the actual prefix and one closure response. Crossing windows are
proved by their literal positions, without a crossing-product hypothesis. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

variable {R : Type*}

/-- The complete cyclic word `P^k R S`, retaining its one closure position. -/
def closureWord {n : ℕ} (f : ZMod n → R) (S : R) (B : ℕ) (i : ZMod B) : R :=
  if i.val = B - 1 then S else f (i.val : ZMod n)

/-- The shorter cycle made from the length-`m-1` prefix and the same closure position. -/
def remainderClosure {n : ℕ} (f : ZMod n → R) (S : R) (m : ℕ) : ZMod m → R :=
  closureWord f S m

/-- Every noncrossing position is literally a position of the original periodic word. -/
theorem closureWord_noncrossing {n m k : ℕ} [NeZero n] [NeZero m]
    (f : ZMod n → R) (S : R) {i a : ℕ} (hi : i < k * n) (ha : a < m) :
    closureWord f S (k * n + m) ((i : ZMod (k * n + m)) + a • 1) =
      f ((i : ZMod n) + a • 1) := by
  have hlt : i + a < k * n + m := by omega
  have hne : i + a ≠ k * n + m - 1 := by omega
  simp only [nsmul_eq_mul, mul_one, ← Nat.cast_add]
  unfold closureWord
  rw [ZMod.val_natCast_of_lt hlt, ite_eq_right hne]

/-- Each crossing window rotates the short prefix-plus-closure cycle, including wrapped cells. -/
theorem closureWord_crossing {n m k : ℕ} [NeZero n] [NeZero m]
    (f : ZMod n → R) (S : R) (hmn : m ≤ n) (hk : 0 < k)
    {i a : ℕ} (hi : i < m) (ha : a < m) :
    closureWord f S (k * n + m) (((k * n + i : ℕ) : ZMod (k * n + m)) + a • 1) =
      remainderClosure f S m ((i : ZMod m) + a • 1) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hn : m ≤ k * n := (Nat.le_mul_of_pos_left n hk).trans' hmn
  simp only [nsmul_eq_mul, mul_one, ← Nat.cast_add]
  unfold remainderClosure closureWord
  by_cases hsmall : i + a < m
  · rw [ZMod.val_natCast_of_lt (by omega : k * n + i + a < k * n + m),
      ZMod.val_natCast_of_lt hsmall]
    have he : k * n + i + a = (k * n + m - 1) ↔ i + a = m - 1 := by omega
    by_cases hEnd : i + a = m - 1
    · rw [ite_eq_left (he.mpr hEnd), ite_eq_left hEnd]
    · rw [ite_eq_right (fun h => hEnd (he.mp h)), ite_eq_right hEnd]
      congr 1
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  · have hsum : m ≤ i + a := Nat.le_of_not_gt hsmall
    have hr : i + a - m < m - 1 := by omega
    have hB : k * n + i + a = (i + a - m) + (k * n + m) := by omega
    have hvB : ((k * n + i + a : ℕ) : ZMod (k * n + m)).val = i + a - m := by
      rw [ZMod.val_natCast, hB, Nat.add_mod, Nat.mod_self, Nat.add_zero,
        Nat.mod_eq_of_lt (by omega : i + a - m < k * n + m)]
      exact Nat.mod_eq_of_lt (by omega)
    have hvm : ((i + a : ℕ) : ZMod m).val = i + a - m := by
      have he : i + a = (i + a - m) + m := by omega
      calc
        ((i + a : ℕ) : ZMod m).val = (i + a) % m := ZMod.val_natCast _ _
        _ = ((i + a - m) + m) % m := congrArg (· % m) he
        _ = i + a - m := by
          rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
            Nat.mod_eq_of_lt (by omega : i + a - m < m)]
    rw [hvB, hvm, ite_eq_right (by omega : i + a - m ≠ k * n + m - 1),
      ite_eq_right (by omega : i + a - m ≠ m - 1)]

/-- The crossing length-`m` product includes the entire short prefix and exactly one closure. -/
theorem closureWord_crossing_product {n m k : ℕ} [NeZero n] [NeZero m] [CommMonoid R]
    (f : ZMod n → R) (S : R) (hmn : m ≤ n) (hk : 0 < k) {i : ℕ} (hi : i < m) :
    windowProduct (closureWord f S (k * n + m)) 1 m ((k * n + i : ℕ) : ZMod (k * n + m)) =
      ∏ j : ZMod m, remainderClosure f S m j := by
  have he : windowProduct (closureWord f S (k * n + m)) 1 m
      ((k * n + i : ℕ) : ZMod (k * n + m)) =
      windowProduct (remainderClosure f S m) 1 m (i : ZMod m) := by
    unfold windowProduct
    apply Finset.prod_congr rfl
    intro a ha
    exact closureWord_crossing f S hmn hk hi (Finset.mem_range.mp ha)
  rw [he, zmod_windowProduct_cycle]

/-- Natural positions enumerate every cyclic start exactly once. -/
theorem zmod_sum_eq_range {n : ℕ} [NeZero n] [AddCommMonoid R] (f : ZMod n → R) :
    (∑ i, f i) = ∑ i ∈ Finset.range n, f (i : ZMod n) := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  have he (i : Fin n) : (i.val : ZMod n) = ZMod.finEquiv n i := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact Fin.cast_val_eq_self i
  simp only [he]
  exact ((ZMod.finEquiv n).toEquiv.sum_comp f).symm

/-- The complete closure product retains every periodic position and its last closure. -/
theorem closureWord_product {n B : ℕ} [NeZero B] [CommMonoid R]
    (f : ZMod n → R) (S : R) :
    (∏ i : ZMod B, closureWord f S B i) =
      (∏ i ∈ Finset.range (B - 1), f (i : ZMod n)) * S := by
  classical
  rw [← zmod_windowProduct_cycle _ 0]
  unfold windowProduct
  simp only [zero_add, nsmul_eq_mul, mul_one]
  have hB : B = (B - 1) + 1 := by have := NeZero.ne B; omega
  have hp := Finset.prod_range_succ (fun i => closureWord f S B (i : ZMod B)) (B - 1)
  rw [← hB] at hp
  rw [hp]
  have hlast : closureWord f S B ((B - 1 : ℕ) : ZMod B) = S := by
    unfold closureWord
    rw [ZMod.val_natCast_of_lt (by have := NeZero.ne B; omega), ite_eq_left rfl]
  rw [hlast]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  unfold closureWord
  rw [ZMod.val_natCast_of_lt (by have := Finset.mem_range.mp hi; omega),
    ite_eq_right (by have := Finset.mem_range.mp hi; omega)]

end SkewCornerDescent.CyclicWindows
