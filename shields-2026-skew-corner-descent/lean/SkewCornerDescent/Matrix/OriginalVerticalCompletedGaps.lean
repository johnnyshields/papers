/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalEndpointCoordinates
import SkewCornerDescent.Matrix.OriginalCompletedGapEndpoints

/-!
# Complete actual vertical closure gap copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual selected endpoint coordinates retain both internal copies, the central
vertical splice, and both true exterior caps in the completed gap word.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual completed vertical gap is the corresponding source gap,
including the central join and the final cap-splice position. -/
theorem originalVerticalClosure_completed_gap_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (k : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalCompletedGap Q (originalVerticalClosureSelectedIndex P Q v hQ upper k) =
      c.originalCompletedGap P k := by
  let B := originalSelectedCount (hD := hD) P
  have hB : 0 < B := by have := k.isLt; omega
  have hc := originalVerticalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hQpos : 0 < originalSelectedCount (hD := hD) Q := by dsimp only [B] at hB; omega
  let idx := originalVerticalClosureSelectedIndex (hD := hD) P Q v hQ
  let xP := fun (j : Fin B) => P.xi (originalRowSplitEquiv (hD := hD) P
    (.inl (some (originalSelectedEnumeration (hD := hD) P j))))
  let yP := fun (j : Fin B) => P.zeta (originalColSplitEquiv (hD := hD) P
    (.inl (some (originalSelectedEnumeration (hD := hD) P j))))
  let xQ := fun (j : Fin (originalSelectedCount (hD := hD) Q)) =>
    Q.xi (originalRowSplitEquiv (hD := hD) Q
      (.inl (some (originalSelectedEnumeration (hD := hD) Q j))))
  let yQ := fun (j : Fin (originalSelectedCount (hD := hD) Q)) =>
    Q.zeta (originalColSplitEquiv (hD := hD) Q
      (.inl (some (originalSelectedEnumeration (hD := hD) Q j))))
  have hcoord (up : Bool) (j : Fin B) :
      xQ (idx up j) = xP j + (if up then P.xi 0 else 0) ∧
      yQ (idx up j) = yP j + (if up then P.xi 0 else 0) :=
    c.originalVerticalClosure_ordered_endpoints P Q v hQ up j
  change c.originalCompletedGap Q (idx upper k) = c.originalCompletedGap P k
  by_cases hk : k.val + 1 < B
  · let next : Fin B := ⟨k.val + 1, hk⟩
    have hnext : (idx upper k).val + 1 = (idx upper next).val := by
      dsimp only [idx, originalVerticalClosureSelectedIndex, next]
      split <;> omega
    have hq : (idx upper k).val + 1 < originalSelectedCount (hD := hD) Q := by
      rw [hnext]
      exact (idx upper next).isLt
    have hp := c.originalCompletedGap_internal_endpoints P k hk
    have hqgap := c.originalCompletedGap_internal_endpoints Q (idx upper k) hq
    have he : (⟨(idx upper k).val + 1, hq⟩ : Fin (originalSelectedCount (hD := hD) Q)) =
        idx upper next := Fin.ext hnext
    rw [he] at hqgap
    change c.originalCompletedGap Q (idx upper k) = xQ (idx upper k) - yQ (idx upper next) -
      (c.top : ℤ) at hqgap
    change c.originalCompletedGap P k = xP k - yP next - (c.top : ℤ) at hp
    rw [hqgap, hp, (hcoord upper k).1, (hcoord upper next).2]
    ring
  · have hklast : k.val = B - 1 := by have := k.isLt; omega
    let first : Fin B := ⟨0, hB⟩
    have hplast : c.originalCompletedGap P k =
        P.xi 0 - yP first + xP k - P.zeta (Fin.last n) - (c.top : ℤ) := by
      have he : k = (⟨B - 1, by omega⟩ : Fin B) := Fin.ext hklast
      rw [he]
      exact c.originalCompletedGap_last_endpoints P hB
    cases upper with
    | true =>
      have hnext : (idx true k).val + 1 = (idx false first).val := by
        dsimp only [idx, originalVerticalClosureSelectedIndex, first]
        simp only [ite_true, Bool.false_eq_true, ite_false, zero_add, add_zero]
        omega
      have hq : (idx true k).val + 1 < originalSelectedCount (hD := hD) Q := by
        rw [hnext]
        exact (idx false first).isLt
      have hg := c.originalCompletedGap_internal_endpoints Q (idx true k) hq
      have he : (⟨(idx true k).val + 1, hq⟩ : Fin (originalSelectedCount (hD := hD) Q)) =
          idx false first := Fin.ext hnext
      rw [he] at hg
      change c.originalCompletedGap Q (idx true k) =
        xQ (idx true k) - yQ (idx false first) - (c.top : ℤ) at hg
      rw [hg, hplast, (hcoord true k).1, (hcoord false first).2, P.zeta_last]
      simp only [ite_true, Bool.false_eq_true, ite_false, add_zero, sub_zero]
      ring
    | false =>
      have hl : (idx false k).val = originalSelectedCount (hD := hD) Q - 1 := by
        dsimp only [idx, originalVerticalClosureSelectedIndex]
        simp only [Bool.false_eq_true, ite_false]
        dsimp only [B] at hklast
        omega
      have he : idx false k =
          (⟨originalSelectedCount (hD := hD) Q - 1, by omega⟩ :
            Fin (originalSelectedCount (hD := hD) Q)) := Fin.ext hl
      have hfirst : (⟨0, hQpos⟩ : Fin (originalSelectedCount (hD := hD) Q)) = idx true first := by
        apply Fin.ext
        simp only [idx, originalVerticalClosureSelectedIndex, first, ite_true, zero_add]
      have hg := c.originalCompletedGap_last_endpoints Q hQpos
      dsimp only at hg
      rw [← he, hfirst] at hg
      change c.originalCompletedGap Q (idx false k) = Q.xi 0 - yQ (idx true first) +
        xQ (idx false k) - Q.zeta (Fin.last m) - (c.top : ℤ) at hg
      rw [hg, hplast, (hcoord true first).2, (hcoord false k).1,
        originalVerticalClosure_profile_top P Q v hQ, P.zeta_last, Q.zeta_last]
      simp only [ite_true, Bool.false_eq_true, ite_false, add_zero, sub_zero]
      ring

/-- The complete actual vertical gap cycle is the positional repetition of the
source cycle, retaining the central and final closure positions. -/
theorem originalVerticalClosure_completed_gap_mod {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (k : Fin (originalSelectedCount (hD := hD) Q)) :
    c.originalCompletedGap Q k = c.originalCompletedGap P
      ⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ := by
  let B := originalSelectedCount (hD := hD) P
  have hc := originalVerticalClosure_profile_selected_count (hD := hD) P Q v hQ
  by_cases hk : k.val < B
  · let i : Fin B := ⟨k.val, hk⟩
    have h := c.originalVerticalClosure_completed_gap_copy P Q v hQ true i
    have he : originalVerticalClosureSelectedIndex P Q v hQ true i = k := by
      apply Fin.ext
      simp only [originalVerticalClosureSelectedIndex, i, ite_true, zero_add]
    have hm : k.val % originalSelectedCount (hD := hD) P = i.val :=
      Nat.mod_eq_of_lt hk
    have hi : (⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ :
        Fin (originalSelectedCount (hD := hD) P)) = i := Fin.ext hm
    rw [hi]
    simpa only [he] using h
  · have hsmall : k.val - B < B := by have := k.isLt; dsimp only [B] at *; omega
    let i : Fin B := ⟨k.val - B, hsmall⟩
    have h := c.originalVerticalClosure_completed_gap_copy P Q v hQ false i
    have he : originalVerticalClosureSelectedIndex P Q v hQ false i = k := by
      apply Fin.ext
      change B + (k.val - B) = k.val
      omega
    have hki : B + i.val = k.val := by dsimp only [i]; omega
    have hm : k.val % B = i.val := by
      rw [← hki]
      simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt i.isLt]
    have hi : (⟨k.val % originalSelectedCount (hD := hD) P, Nat.mod_lt _ hB⟩ :
        Fin (originalSelectedCount (hD := hD) P)) = i := Fin.ext hm
    rw [hi]
    simpa only [he] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
