/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivatePeriodTop
import SkewCornerDescent.Matrix.OriginalPrivateWindowMembership
import SkewCornerDescent.Matrix.OriginalWindowSelectedTranslation
import SkewCornerDescent.Matrix.OriginalWindowRows

/-!
# Produced actual endpoint coordinates at the private period boundary

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Literal selected-occurrence translation identifies the retained right endpoint.
The completed actual gap period then identifies the left endpoint from the
sum of both true cap tops. No candidate-position match is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual interval at rank `r*(b-a)` has retained endpoints on the two
sides of the cut with exactly the genuine cap distances. Full source occurrence
counts, literal windows, and completed periodic gaps supply both coordinates. -/
theorem originalPrivateLower_cap_coordinates {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (a b r : ℕ) [NeZero r]
    (ha : 0 < a) (hab : a < b) (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hcard : Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * a)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    let cut := r * (b - a)
    let i : Fin (originalSelectedCount (hD := hD) P) := ⟨cut - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left (show b - a < b by omega) (NeZero.pos r)
      omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P) := ⟨cut, by
      have hlt := Nat.mul_lt_mul_of_pos_left (show b - a < b by omega) (NeZero.pos r)
      omega⟩
    let left := originalSelectedEnumeration (hD := hD) P i
    let right := originalSelectedEnumeration (hD := hD) P j
    let p₀ := originalHessenbergDistance (hD := hD) P 0 0
    let q₀ := originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some right))) = P.xi 0 - q - p₀ ∧
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some left))) = P.xi 0 - q + q₀ := by
  have hr := NeZero.pos r
  have hcutpos : 0 < r * (b - a) := Nat.mul_pos hr (by omega)
  have hcutlt : r * (b - a) < r * b := Nat.mul_lt_mul_of_pos_left (by omega) hr
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcount]
    exact Nat.mul_pos hr (by omega)
  let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * (b - a) - 1, by omega⟩
  let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * (b - a), by omega⟩
  let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
  let left := originalSelectedEnumeration (hD := hD) P i
  let right := originalSelectedEnumeration (hD := hD) P j
  let f := originalSelectedEnumeration (hD := hD) P first
  have hshift : originalSelectedCount (hD := hD) P -
      Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * (b - a) := by
    rw [hcount, hcard, Nat.mul_sub_left_distrib]
  have hnlo := profile_normalized_lower_private_boundaries P
  have hnhi := profile_normalized_upper_private_boundaries P
  have htranslate := originalWindow_selected_index_translation (hD := hD) P q v hv hprefix
    hwindow (private_diagonal_no_interior hnlo.1) (private_diagonal_no_interior hcutq)
    (private_diagonal_no_interior hcutLq) (private_diagonal_no_interior hnhi.1)
    first j (by change r * (b - a) = 0 + _; rw [zero_add, hshift])
  have hend := c.originalSelected_translated_endpoints P P right f v htranslate
  rw [hv] at hend
  have htop := c.originalPrivatePeriod_top_eq_cap_sum P a b r ha hab hcount hgap
  have hcol : i.succ = j.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    dsimp only [i, j]
    omega
  have hdist : originalHessenbergDistance (hD := hD) P i.succ i.succ =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some left))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some right))) := by
    unfold originalHessenbergDistance
    rw [originalHessenbergRows_succ, hcol, originalHessenbergCols_castSucc]
  dsimp only at htop
  change originalHessenbergDistance (hD := hD) P i.succ i.succ = _ at htop
  rw [hdist] at htop
  have hfirst : originalHessenbergDistance (hD := hD) P 0 0 =
      P.xi 0 - P.zeta (interiorBlockLast P f.val.val).castSucc := by
    rw [originalHessenbergDistance_first P hB]
    rfl
  dsimp only
  rw [originalColSplitEquiv_selected, originalRowSplitEquiv_selected]
  rw [originalColSplitEquiv_selected, originalRowSplitEquiv_selected] at htop
  rw [hfirst] at htop
  dsimp only [left, right, f, i, j, first] at *
  omega

/-- The complementary private interval at rank `r*a` has the same genuine
cap distances around the upper cut. Literal translation identifies its retained
left endpoint; the actual completed gap period supplies the right endpoint. -/
theorem originalPrivateUpper_cap_coordinates {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (a b r : ℕ) [NeZero r]
    (ha : 0 < a) (hab : a < b) (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hcard : Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * a)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P))) :
    let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left hab (NeZero.pos r)
      omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a, by
      have hlt := Nat.mul_lt_mul_of_pos_left hab (NeZero.pos r)
      omega⟩
    let left := originalSelectedEnumeration (hD := hD) P i
    let right := originalSelectedEnumeration (hD := hD) P j
    let p₀ := originalHessenbergDistance (hD := hD) P 0 0
    let q₀ := originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some left))) = q + q₀ ∧
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some right))) = q - p₀ := by
  have hr := NeZero.pos r
  have hpos : 0 < r * a := Nat.mul_pos hr ha
  have hlt : r * a < r * b := Nat.mul_lt_mul_of_pos_left hab hr
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcount]
    exact Nat.mul_pos hr (by omega)
  let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a - 1, by omega⟩
  let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a, by omega⟩
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  let left := originalSelectedEnumeration (hD := hD) P i
  let right := originalSelectedEnumeration (hD := hD) P j
  let l := originalSelectedEnumeration (hD := hD) P last
  have hsplit : r * a + r * (b - a) = r * b := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hab.le]
  have hshift : originalSelectedCount (hD := hD) P -
      Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * (b - a) := by
    rw [hcount, hcard, Nat.mul_sub_left_distrib]
  have hnlo := profile_normalized_lower_private_boundaries P
  have hnhi := profile_normalized_upper_private_boundaries P
  have htranslate := originalWindow_selected_index_translation (hD := hD) P q v hv hprefix
    hwindow (private_diagonal_no_interior hnlo.1) (private_diagonal_no_interior hcutq)
    (private_diagonal_no_interior hcutLq) (private_diagonal_no_interior hnhi.1)
    i last (by dsimp only [i, last]; rw [hshift]; omega)
  have hend := c.originalSelected_translated_endpoints P P l left v htranslate
  rw [hv] at hend
  have hba : b - (b - a) = a := by omega
  have htop := c.originalPrivatePeriod_top_eq_cap_sum P (b - a) b r
    (by omega) (by omega) hcount hgap
  simp only [hba] at htop
  have hcol : i.succ = j.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    dsimp only [i, j]
    omega
  have hdist : originalHessenbergDistance (hD := hD) P i.succ i.succ =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some left))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some right))) := by
    unfold originalHessenbergDistance
    rw [originalHessenbergRows_succ, hcol, originalHessenbergCols_castSucc]
  change originalHessenbergDistance (hD := hD) P i.succ i.succ = _ at htop
  rw [hdist] at htop
  have hlast : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) =
      P.xi l.val.val.succ := by
    rw [originalHessenbergDistance_last P hB]
    unfold originalLastCapDistance
    simp only [P.zeta_last, sub_zero]
    rfl
  dsimp only
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected] at htop
  rw [hlast] at htop
  dsimp only [left, right, l, i, j, last] at *
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
