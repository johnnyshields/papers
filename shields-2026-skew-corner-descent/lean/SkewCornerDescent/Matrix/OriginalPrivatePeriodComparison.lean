/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateJoinComparison
import SkewCornerDescent.Matrix.OriginalPrivateCapCoordinates

/-!
# Produced lower private period boundary and its actual reference

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual selected counts and the completed gap period produce both endpoint
coordinates. Whole-window ranks produce the literal cap match. The resulting
comparison carries no supplied inverse or cap-coordinate equality. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At the produced lower private period boundary, every ordinary contraction
below the cut equals the actual horizontal reference plus its vertical unit. -/
theorem originalPrivatePeriod_comparison_lower {n m : ℕ}
    (P : Profile n) [NeZero (originalSelectedCount (hD := hD) P)]
    (Q : Profile m) (v w : ℤ × ℤ) (q : ℤ) (hv : content v = q)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevcut : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (a b r : ℕ) [NeZero r] (ha : 0 < a) (hab : a < b)
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hcard : Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * a)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = P.xi 0 - q) (hp : content prev = P.xi 0 - q - 1)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : z ≤ P.xi 0 - q)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0)
    (hA0 : A.coeff 0 = 1) (hT0 : T.coeff 0 = 1) :
    let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * (b - a) - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left (show b - a < b by omega) (NeZero.pos r)
      omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * (b - a), by
      have hlt := Nat.mul_lt_mul_of_pos_left (show b - a < b by omega) (NeZero.pos r)
      omega⟩
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, NeZero.pos _⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by
        have h := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩
    let E := originalSelectedEnumeration (hD := hD) P
    c.originalIntervalInverseProjection P (some (E i)) (some (E j)) A T z =
      c.originalIntervalInverseProjection Q
          (some (originalHorizontalClosureSelectedCopy P Q w hQ true (E last)))
          (some (originalHorizontalClosureSelectedCopy P Q w hQ false (E first))) A T (z + q) +
        if z = P.xi 0 - q ∧ cur.2 = prev.2 then 1 else 0 := by
  intro i j first last E
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hcoords := c.originalPrivateLower_cap_coordinates P a b r ha hab q v hv
    hprefix hwindow hcutq hcutLq hcount hcard hgap
  dsimp only at hcoords
  change P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E j)))) = _ ∧
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E i)))) = _ at hcoords
  have hptop := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
  have hqtop := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
  have hN := c.top.property
  have hb : P.xi 0 - q < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E i)))) := by
    omega
  have hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E j)))) < P.xi 0 - q := by
    omega
  have hshift : originalSelectedCount (hD := hD) P -
      Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * (b - a) := by
    rw [hcount, hcard, Nat.mul_sub_left_distrib]
  have hnlo := profile_normalized_lower_private_boundaries P
  have hnhi := profile_normalized_upper_private_boundaries P
  have he := originalWindow_selected_index_translation (hD := hD) P q v hv hprefix hwindow
    (private_diagonal_no_interior hnlo.1) (private_diagonal_no_interior hcutq)
    (private_diagonal_no_interior hcutLq) (private_diagonal_no_interior hnhi.1)
    first j (by dsimp only [first, j]; rw [hshift, zero_add])
  have hj := (originalWindow_prefix_iff_rank (hD := hD) P q j).mpr (by
    dsimp only [j]
    rw [hshift])
  exact c.originalPrivateJoin_comparison_lower P Q v w q hv hQ hwindow hcutq hcutLq
    hprevcut (E i) (E j) (E first) (E last) hj he cur prev hcur hprev hc hp hb hd
    A T z hz hA hT hA0 hT0

/-- The complementary upper private period boundary supplies the same actual
reference comparison, retaining the complete lower cap. -/
theorem originalPrivatePeriod_comparison_upper {n m : ℕ}
    (P : Profile n) [NeZero (originalSelectedCount (hD := hD) P)]
    (Q : Profile m) (v w : ℤ × ℤ) (q : ℤ) (hv : content v = q)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevcut : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (a b r : ℕ) [NeZero r] (ha : 0 < a) (hab : a < b)
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hcard : Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * a)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = q) (hp : content prev = q - 1)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) (hz : q ≤ z)
    (hA : ∀ j, j < 0 → A.coeff j = 0) (hT : ∀ j, j < 0 → T.coeff j = 0)
    (hA0 : A.coeff 0 = 1) (hT0 : T.coeff 0 = 1) :
    let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left hab (NeZero.pos r)
      omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a, by
      have hlt := Nat.mul_lt_mul_of_pos_left hab (NeZero.pos r)
      omega⟩
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, NeZero.pos _⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by
        have h := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩
    let E := originalSelectedEnumeration (hD := hD) P
    c.originalIntervalInverseProjection P (some (E i)) (some (E j)) A T z =
      c.originalIntervalInverseProjection Q
          (some (originalHorizontalClosureSelectedCopy P Q w hQ true (E last)))
          (some (originalHorizontalClosureSelectedCopy P Q w hQ false (E first))) A T
          (z + P.xi 0 - q) +
        if z = q ∧ cur.2 = prev.2 then 1 else 0 := by
  intro i j first last E
  have hr := NeZero.pos r
  have hpos : 0 < r * a := Nat.mul_pos hr ha
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hcoords := c.originalPrivateUpper_cap_coordinates P a b r ha hab q v hv
    hprefix hwindow hcutq hcutLq hcount hcard hgap
  dsimp only at hcoords
  change P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E i)))) = _ ∧
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E j)))) = _ at hcoords
  have hptop := c.originalHessenbergDistance_gt_top P hB 0 0 le_rfl
  have hqtop := c.originalHessenbergDistance_gt_top P hB (Fin.last _) (Fin.last _) le_rfl
  have hN := c.top.property
  have hb : q < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E i)))) := by omega
  have hd : P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E j)))) < q := by omega
  have hshift : originalSelectedCount (hD := hD) P -
      Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * (b - a) := by
    rw [hcount, hcard, Nat.mul_sub_left_distrib]
  have hsplit : r * a + r * (b - a) = r * b := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hab.le]
  have hnlo := profile_normalized_lower_private_boundaries P
  have hnhi := profile_normalized_upper_private_boundaries P
  have he := originalWindow_selected_index_translation (hD := hD) P q v hv hprefix hwindow
    (private_diagonal_no_interior hnlo.1) (private_diagonal_no_interior hcutq)
    (private_diagonal_no_interior hcutLq) (private_diagonal_no_interior hnhi.1)
    i last (by dsimp only [i, last]; rw [hshift]; omega)
  have hj := (originalWindow_prefix_iff_rank (hD := hD) P q last).mpr (by
    dsimp only [last]
    rw [hshift]
    omega)
  exact c.originalPrivateJoin_comparison_upper P Q v w q hv hQ hwindow hcutq hcutLq
    hprevcut (E i) (E j) (E first) (E last) hj he cur prev hcur hprev hc hp hb hd
    A T z hz hA hT hA0 hT0

end SkewCornerDescent.Matrix.SelectedCoordinate
