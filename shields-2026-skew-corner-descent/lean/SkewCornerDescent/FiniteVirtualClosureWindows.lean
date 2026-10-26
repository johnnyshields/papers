/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.FiniteClosureWindows

/-!
# Replacing the true closure position in a complete finite response cycle

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`). Every eligible
crossing window contains the closure position once, while noncrossing starts retain the
literal internal word. Equal response values remain distinct positions. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- A crossing window of at most one full cycle meets the closure position exactly once. -/
theorem closure_position_unique {B : ℕ} [NeZero B] (i j a : ℕ)
    (hi : i < B) (hj : j ≤ B) (ha : a < j) :
    (((i : ZMod B) + a • 1).val = B - 1) ↔ a = B - 1 - i := by
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have he : (i : ZMod B) + a • 1 = ((i + a : ℕ) : ZMod B) := by
    simp only [Nat.cast_add, nsmul_eq_mul, mul_one]
  rw [he, ZMod.val_natCast]
  by_cases hlt : i + a < B
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hv : (i + a) % B = i + a - B := by
      have hsum : i + a = (i + a - B) + B := by omega
      rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hv]
    omega

/-- Changing the closure response scales every crossing product once, including full windows. -/
theorem completeResponseCycle_crossing_product_replace {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S T : F) (hS : S ≠ 0)
    (i j : ℕ) (hi : i < B) (hj : j ≤ B) (hcross : B - j ≤ i) :
    windowProduct (completeResponseCycle l T) 1 j (i : ZMod B) =
      windowProduct (completeResponseCycle l S) 1 j (i : ZMod B) * (T / S) := by
  classical
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have ht : B - 1 - i ∈ Finset.range j := Finset.mem_range.mpr (by omega)
  have hletter (a : ℕ) (ha : a ∈ Finset.range j) :
      completeResponseCycle l T ((i : ZMod B) + a • 1) =
        completeResponseCycle l S ((i : ZMod B) + a • 1) *
          (if a = B - 1 - i then T / S else 1) := by
    have hval := ZMod.val_lt ((i : ZMod B) + a • 1)
    have he := closure_position_unique i j a hi hj (Finset.mem_range.mp ha)
    unfold completeResponseCycle
    by_cases ha' : a = B - 1 - i
    · have hlast := he.mpr ha'
      rw [hlast, dite_eq_right (by omega), dite_eq_right (by omega),
        ite_eq_left ha']
      field_simp
    · have hnot : ((i : ZMod B) + a • 1).val < B - 1 := by
        have hn := mt he.mp ha'
        omega
      rw [dite_eq_left hnot, dite_eq_left hnot, ite_eq_right ha', mul_one]
  unfold windowProduct
  rw [Finset.prod_congr rfl hletter, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq']
  rw [ite_eq_left ht]

/-- Noncrossing starts omit the closure position and are independent of its value. -/
theorem completeResponseCycle_noncrossing_product {B : ℕ} [NeZero B]
    {F : Type*} [CommMonoid F] (l : Fin (B - 1) → F) (S T : F)
    (i j : ℕ) (hi : i < B - j) :
    windowProduct (completeResponseCycle l S) 1 j (i : ZMod B) =
      windowProduct (completeResponseCycle l T) 1 j (i : ZMod B) := by
  unfold windowProduct
  apply Finset.prod_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  have he : (i : ZMod B) + a • 1 = ((i + a : ℕ) : ZMod B) := by
    simp only [Nat.cast_add, nsmul_eq_mul, mul_one]
  rw [he]
  unfold completeResponseCycle
  rw [ZMod.val_natCast_of_lt (by omega), dite_eq_left (by omega), dite_eq_left (by omega)]

/-- Replacing the single closure response scales precisely the crossing part of the
complete cyclic inverse inventory, also at the full-length boundary. -/
theorem inverseWindowSum_complete_replace {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S T : F)
    (hS : S ≠ 0) (hT : T ≠ 0) (j : ℕ) (hj : j ≤ B) :
    inverseWindowSum (completeResponseCycle l T) j =
      linearInverseWindowSum l j + S / T *
        (inverseWindowSum (completeResponseCycle l S) j - linearInverseWindowSum l j) := by
  classical
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hpref (V : F) : linearInverseWindowSum l j =
      ∑ i ∈ Finset.range (B - j),
        (windowProduct (completeResponseCycle l V) 1 j (i : ZMod B))⁻¹ := by
    have hl : (fun i : Fin (B - 1) => completeResponseCycle l V (i.val : ZMod B)) = l :=
      funext (completeResponseCycle_prefix l V)
    have he := linearInverseWindowSum_cyclic_truncation
      (L := B - 1) (completeResponseCycle l V) j
    rw [hl, show B - 1 + 1 = B by omega] at he
    exact he
  have hsum (V : F) : inverseWindowSum (completeResponseCycle l V) j =
      (∑ i ∈ Finset.range (B - j),
        (windowProduct (completeResponseCycle l V) 1 j (i : ZMod B))⁻¹) +
      ∑ i ∈ Finset.range j,
        (windowProduct (completeResponseCycle l V) 1 j ((B - j + i : ℕ) : ZMod B))⁻¹ := by
    unfold inverseWindowSum
    have he := (ZMod.finEquiv B).toEquiv.sum_comp
      (fun z => (windowProduct (completeResponseCycle l V) 1 j z)⁻¹)
    change (∑ i : Fin B, (windowProduct (completeResponseCycle l V) 1 j
      (ZMod.finEquiv B i))⁻¹) = _ at he
    rw [← he]
    simp_rw [finEquiv_eq_natCast]
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (windowProduct (completeResponseCycle l V) 1 j (i : ZMod B))⁻¹) B]
    conv_lhs => arg 1; rw [show B = (B - j) + j by omega]
    rw [Finset.sum_range_add]
  have hcross : (∑ i ∈ Finset.range j,
      (windowProduct (completeResponseCycle l T) 1 j ((B - j + i : ℕ) : ZMod B))⁻¹) =
      S / T * ∑ i ∈ Finset.range j,
      (windowProduct (completeResponseCycle l S) 1 j ((B - j + i : ℕ) : ZMod B))⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [completeResponseCycle_crossing_product_replace l S T hS (B - j + i) j
      (by have := Finset.mem_range.mp hi; omega) hj (by omega), mul_inv_rev]
    field_simp
  rw [hsum T, ← hpref T, hcross, hsum S, ← hpref S]
  ring

end SkewCornerDescent.CyclicWindows
