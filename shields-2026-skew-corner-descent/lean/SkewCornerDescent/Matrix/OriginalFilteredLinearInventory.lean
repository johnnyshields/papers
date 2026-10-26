/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FilteredLinearWindows
import SkewCornerDescent.Matrix.OriginalStrictGapFrontier
import SkewCornerDescent.Matrix.HessenbergLinearWindows

/-!
# Literal linear starts for the filtered original interval inventory

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Both true
boundary caps are excluded by strict completion, not replaced by closure letters.
Each surviving interval is its full internal response product, filtered by its
actual complete gap sum. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewCornerDescent.CyclicWindows
open scoped BigOperators

/-- A geometric filter preserves the literal internal-start bijection and each
complete reciprocal product, including the empty full-length start set. -/
theorem hessenberg_filtered_internal_inverse_windows {B m : ℕ} [NeZero B]
    (hmB : m < B) {F : Type*} [Field F] (d : Fin (B + 1) → F)
    (g : ZMod B → ℤ) (M : ℤ) :
    (∑ s : Fin (B - (m + 1)), if windowSum g 1 (m + 1) (s.val : ZMod B) = M then
      ∏ l ∈ Finset.Icc (⟨s.val + 1, by have := s.isLt; omega⟩ : Fin (B + 1))
        ⟨s.val + m + 1, by have := s.isLt; omega⟩, (d l)⁻¹ else 0) =
      filteredLinearInverseWindowSum
        (fun i : Fin (B - 1) => d ⟨i.val + 1, by have := i.isLt; omega⟩) g (m + 1) M := by
  classical
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hp : B - 1 + 1 - (m + 1) = B - (m + 1) := by omega
  let f := fun s : Fin (B - (m + 1)) => if windowSum g 1 (m + 1) (s.val : ZMod B) = M then
    ∏ l ∈ Finset.Icc (⟨s.val + 1, by have := s.isLt; omega⟩ : Fin (B + 1))
      ⟨s.val + m + 1, by have := s.isLt; omega⟩, (d l)⁻¹ else 0
  change (∑ s, f s) = _
  rw [← (finCongr hp).sum_comp f]
  unfold filteredLinearInverseWindowSum
  apply Finset.sum_congr rfl
  intro s _
  dsimp only [f]
  simp only [finCongr_apply, Fin.val_cast]
  split_ifs
  · have h := hessenberg_internal_interval_product hmB (fun l => (d l)⁻¹) (finCongr hp s)
    simpa only [finCongr_apply, Fin.val_cast, Nat.add_assoc] using h
  · rfl

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete actual filtered interval inventory is the literal filtered
linear word. No gap period or response correspondence is assumed. -/
theorem originalFilteredIntervalInventory_eq_linear {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (m : ℕ) (hm : 0 < m) (hmB : m < originalSelectedCount (hD := hD) P)
    (M : ℤ)
    (hbound : ∀ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 (m + 1) z ≤ M)
    (K : ℕ+) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    c.originalFilteredIntervalInventory P (m + 1) K =
      filteredLinearInverseWindowSum (c.originalInternalResidue P)
        (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z)) (m + 1) M := by
  classical
  let F := fun i k : Fin (originalSelectedCount (hD := hD) P + 1) =>
    if originalHessenbergDistance (hD := hD) P i k = (K : ℤ) then
      ∏ l ∈ Finset.Icc i k, (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹ else 0
  have hs : c.originalFilteredIntervalInventory P (m + 1) K =
      ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
        ∑ k : Fin (originalSelectedCount (hD := hD) P + 1),
          if i.val ≤ k.val ∧ k.val - i.val = m ∧ 0 < i.val ∧
              k.val < originalSelectedCount (hD := hD) P then F i k else 0 := by
    unfold originalFilteredIntervalInventory
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : i.val ≤ k.val
    · by_cases hcost : k.val - i.val = m
      · by_cases hend : i.val = 0 ∨ k.val = originalSelectedCount (hD := hD) P
        · have hlt := c.originalHessenbergDistance_boundary_lt_gap_bound P hB m hm hmB
            M hbound i k hik hcost hend
          rw [← hKeq] at hlt
          have hne := ne_of_lt hlt
          have hnot : ¬(0 < i.val ∧ k.val < originalSelectedCount (hD := hD) P) := by omega
          simp only [Nat.add_sub_cancel, hik, hcost, true_and, hne, ite_false, hnot]
        · have hi := i.isLt
          have hk := k.isLt
          have hipos : 0 < i.val := by omega
          have hklt : k.val < originalSelectedCount (hD := hD) P := by omega
          simp only [Nat.add_sub_cancel, hik, hcost, hipos, hklt, true_and, ite_true, F]
      · simp only [Nat.add_sub_cancel, hik, hcost, true_and, false_and, ite_false]
    · simp only [Nat.add_sub_cancel, hik, false_and, ite_false]
  rw [hs, hessenberg_internal_interval_sum hmB]
  calc
    _ = ∑ s : Fin (originalSelectedCount (hD := hD) P - (m + 1)),
        if windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
            1 (m + 1) (s.val : ZMod (originalSelectedCount (hD := hD) P)) = M then
          ∏ l ∈ Finset.Icc
            (⟨s.val + 1, by have := s.isLt; omega⟩ : Fin (originalSelectedCount (hD := hD) P + 1))
            ⟨s.val + m + 1, by have := s.isLt; omega⟩,
              (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      let i : Fin (originalSelectedCount (hD := hD) P) := ⟨s.val, by have := s.isLt; omega⟩
      let k : Fin (originalSelectedCount (hD := hD) P) := ⟨s.val + m, by have := s.isLt; omega⟩
      have he := c.originalCompletedGap_cyclic_internal_window P i k
        (by change s.val ≤ s.val + m; omega)
        (by change s.val + m + 1 < originalSelectedCount (hD := hD) P; have := s.isLt; omega)
      have hlen : k.val - i.val + 1 = m + 1 := by dsimp only [i, k]; omega
      rw [hlen] at he
      have hiff : originalHessenbergDistance (hD := hD) P i.succ k.succ = (K : ℤ) ↔
          windowSum (fun z => c.originalCompletedGap P ((ZMod.finEquiv _).symm z))
            1 (m + 1) (s.val : ZMod (originalSelectedCount (hD := hD) P)) = M := by
        rw [he, hKeq, add_left_cancel_iff]
      change (if originalHessenbergDistance (hD := hD) P i.succ k.succ = (K : ℤ) then
        ∏ l ∈ Finset.Icc i.succ k.succ,
          (c.regularResidue (c.originalHessenbergResponse P l l))⁻¹ else 0) = _
      simp only [hiff]
      rfl
    _ = _ := hessenberg_filtered_internal_inverse_windows hmB
      (fun l => c.regularResidue (c.originalHessenbergResponse P l l)) _ M

end SelectedCoordinate
end SkewCornerDescent.Matrix
