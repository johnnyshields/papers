/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FilteredClosureWindows
import SkewCornerDescent.LinearCyclicWindows

/-!
# Gap-filtered finite word inventories

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). The gap
filter is attached to the literal start, independently of the response values.
A doubled closure word retains one full cyclic inventory and its noncrossing
linear prefix. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- A linear reciprocal inventory with a cyclic geometric filter at every start. -/
noncomputable def filteredLinearInverseWindowSum {L B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin L → F) (g : ZMod B → ℤ) (j : ℕ) (M : ℤ) : F :=
  ∑ s : Fin (L + 1 - j), if windowSum g 1 j (s.val : ZMod B) = M then
    ∏ a : Fin j, (l ⟨s.val + a.val, by have := s.isLt; have := a.isLt; omega⟩)⁻¹
  else 0

/-- A noncrossing complete cycle product retains every literal linear position. -/
theorem completeResponseCycle_noncrossing_inverse_product {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S : F) (j : ℕ) (i : ℕ)
    (hi : i < B - j) :
    (windowProduct (completeResponseCycle l S) 1 j (i : ZMod B))⁻¹ =
      ∏ a : Fin j, (l ⟨i + a.val, by have := a.isLt; omega⟩)⁻¹ := by
  classical
  unfold windowProduct
  rw [← Fin.prod_univ_eq_prod_range, Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  have he : (i : ZMod B) + a.val • 1 = ((i + a.val : ℕ) : ZMod B) := by
    simp only [Nat.cast_add, nsmul_eq_mul, mul_one]
  rw [he]
  exact completeResponseCycle_prefix l S ⟨i + a.val, by have := a.isLt; omega⟩

/-- The gap-filtered linear inventory of the doubled word has one complete cyclic
summand, including every full-length start, plus the literal noncrossing prefix. -/
theorem filteredLinearInverseWindowSum_complete_double {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S : F)
    (g : ZMod B → ℤ) (j : ℕ) (hj : j ≤ B) (M : ℤ) :
    filteredLinearInverseWindowSum
      (fun i : Fin (2 * B - 1) => completeResponseCycle l S (i.val : ZMod B)) g j M =
      filteredLinearInverseWindowSum l g j M +
        filteredInverseWindowSum (completeResponseCycle l S) g j M := by
  classical
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hd : 2 * B - 1 + 1 - j = B + (B - j) := by omega
  have hp : B - 1 + 1 - j = B - j := by omega
  let f := fun i : ℕ => if windowSum g 1 j (i : ZMod B) = M then
    (windowProduct (completeResponseCycle l S) 1 j (i : ZMod B))⁻¹ else 0
  have he : filteredLinearInverseWindowSum
      (fun i : Fin (2 * B - 1) => completeResponseCycle l S (i.val : ZMod B)) g j M =
      ∑ i ∈ Finset.range (2 * B - 1 + 1 - j), f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    unfold filteredLinearInverseWindowSum
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    split_ifs
    · unfold windowProduct
      rw [← Fin.prod_univ_eq_prod_range, Finset.prod_inv_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      congr 2
      simp only [Nat.cast_add, nsmul_eq_mul, mul_one]
    · rfl
  have hcycle : (∑ i ∈ Finset.range B, f i) =
      filteredInverseWindowSum (completeResponseCycle l S) g j M := by
    rw [← Fin.sum_univ_eq_sum_range]
    unfold filteredInverseWindowSum
    have hs := (ZMod.finEquiv B).toEquiv.sum_comp
      (fun z => if windowSum g 1 j z = M then
        (windowProduct (completeResponseCycle l S) 1 j z)⁻¹ else 0)
    change (∑ i : Fin B, if windowSum g 1 j (ZMod.finEquiv B i) = M then
      (windowProduct (completeResponseCycle l S) 1 j (ZMod.finEquiv B i))⁻¹ else 0) = _ at hs
    simpa only [f, finEquiv_eq_natCast] using hs
  have hprefix : (∑ i ∈ Finset.range (B - j), f (B + i)) =
      filteredLinearInverseWindowSum l g j M := by
    unfold filteredLinearInverseWindowSum
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← (finCongr hp).sum_comp (fun i => f (B + i.val))]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    simp only [finCongr_apply, Fin.val_cast, Nat.cast_add, ZMod.natCast_self, zero_add]
    split_ifs
    · exact completeResponseCycle_noncrossing_inverse_product l S j i.val
        (by have := i.isLt; omega)
    · rfl
  rw [he, hd, Finset.sum_range_add, hcycle, hprefix, add_comm]

/-- The filtered linear prefix is precisely the noncrossing part of a complete
cyclic inventory, independently of the closure response. -/
theorem filteredLinearInverseWindowSum_eq_noncrossing_sum {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S : F)
    (g : ZMod B → ℤ) (j : ℕ) (M : ℤ) :
    filteredLinearInverseWindowSum l g j M =
      ∑ i ∈ Finset.range (B - j), if windowSum g 1 j (i : ZMod B) = M then
        (windowProduct (completeResponseCycle l S) 1 j (i : ZMod B))⁻¹ else 0 := by
  classical
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hp : B - 1 + 1 - j = B - j := by omega
  let f := fun i : ℕ => if windowSum g 1 j (i : ZMod B) = M then
    (windowProduct (completeResponseCycle l S) 1 j (i : ZMod B))⁻¹ else 0
  change _ = ∑ i ∈ Finset.range (B - j), f i
  symm
  unfold filteredLinearInverseWindowSum
  rw [← Fin.sum_univ_eq_sum_range, ← (finCongr hp).sum_comp (fun i => f i.val)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [f]
  simp only [finCongr_apply, Fin.val_cast]
  split_ifs
  · exact completeResponseCycle_noncrossing_inverse_product l S j i.val
      (by have := i.isLt; omega)
  · rfl

/-- Replacing the actual closure response scales exactly the retained crossing
windows. Every geometric mask and noncrossing start is preserved. The formula
also holds at `T = 0` under the total inverse convention. -/
theorem filteredInverseWindowSum_complete_replace {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S T : F) (hS : S ≠ 0)
    (g : ZMod B → ℤ) (j : ℕ) (hj : j ≤ B) (M : ℤ) :
    filteredInverseWindowSum (completeResponseCycle l T) g j M =
      filteredLinearInverseWindowSum l g j M + S / T *
        (filteredInverseWindowSum (completeResponseCycle l S) g j M -
          filteredLinearInverseWindowSum l g j M) := by
  classical
  let f := fun V i => if windowSum g 1 j i = M then
    (windowProduct (completeResponseCycle l V) 1 j i)⁻¹ else 0
  let L := fun i : ZMod B => if i.val < B - j then f S i else 0
  have hpoint (i : ZMod B) : f T i = L i + S / T * (f S i - L i) := by
    by_cases hi : i.val < B - j
    · have hp := completeResponseCycle_noncrossing_product l S T i.val j hi
      simp only [ZMod.natCast_zmod_val] at hp
      dsimp only [f, L]
      rw [ite_eq_left hi, ← hp]
      ring
    · have hp := completeResponseCycle_crossing_product_replace l S T hS i.val j
        (ZMod.val_lt i) hj (Nat.le_of_not_gt hi)
      simp only [ZMod.natCast_zmod_val] at hp
      dsimp only [f, L]
      rw [ite_eq_right hi, zero_add, sub_zero]
      by_cases hret : windowSum g 1 j i = M
      · rw [ite_eq_left hret, ite_eq_left hret, hp]
        simp only [div_eq_mul_inv, mul_inv, inv_inv]
        ring
      · simp only [ite_eq_right hret, mul_zero]
  have hsumL : (∑ i, L i) = filteredLinearInverseWindowSum l g j M := by
    have he := (ZMod.finEquiv B).toEquiv.sum_comp L
    change (∑ i : Fin B, L (ZMod.finEquiv B i)) = ∑ i, L i at he
    simp only [finEquiv_eq_natCast] at he
    rw [← he, Fin.sum_univ_eq_sum_range (fun i : ℕ => L (i : ZMod B)) B]
    have hfirst : (∑ i ∈ Finset.range (B - j), L (i : ZMod B)) =
        ∑ i ∈ Finset.range (B - j), f S (i : ZMod B) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      dsimp only [L]
      rw [ZMod.val_natCast_of_lt (by omega), ite_eq_left hi']
    have hlast : (∑ i ∈ Finset.range j, L ((B - j + i : ℕ) : ZMod B)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      dsimp only [L]
      rw [ZMod.val_natCast_of_lt (by omega), ite_eq_right (by omega)]
    conv_lhs => arg 1; rw [show B = (B - j) + j by omega]
    rw [Finset.sum_range_add, hfirst, hlast, add_zero]
    exact (filteredLinearInverseWindowSum_eq_noncrossing_sum l S g j M).symm
  change (∑ i, f T i) = _
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsumL]
  rfl

end SkewCornerDescent.CyclicWindows
