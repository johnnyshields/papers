/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalSelectedCopies
import SkewCornerDescent.Matrix.OriginalPrivateEndpointSeparation

/-!
# The literal vertical closure's surviving original join unit

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The actual two join cells share a column. Canonical normalization preserves
their contents and their private flags, so the original remaining matrix has
one literal h-zero vertex. Actual selected endpoints put it in the full join
interval. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Both private join cells occur in the actual vertical union and share
one literal column, before any choice of a canonical profile. -/
theorem originalVerticalClosure_join_cells {n : ℕ} (P : Profile n) :
    (-1, P.xi 0 - 1) ∈ originalVerticalClosure P ∧
      (0, P.xi 0 - 1) ∈ originalVerticalClosure P := by
  constructor
  · rw [originalVerticalClosure_union]
    apply Finset.mem_union_right
    apply mem_translate.mpr
    rw [originalHorizontalDisplacement_pair]
    rw [show (-1, P.xi 0 - 1) - ((-(n : ℤ), P.xi 0 - n) - eCell) =
      ((n : ℤ), (n : ℤ)) by
      ext <;> simp only [eCell, Prod.fst_sub, Prod.snd_sub] <;> omega]
    simpa only [P.zeta_last, Fin.val_last, zero_add] using P.row_left_mem_cells (Fin.last n)
  · rw [originalVerticalClosure_union]
    apply Finset.mem_union_left
    simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using P.row_right_mem_cells 0

/-- Every canonical profile of the literal vertical closure inherits both
actual private join flags; no diagonal-coordinate match is supplied. -/
theorem originalVerticalClosure_profile_join_private {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) :
    diagLo Q.cells (P.xi 0) = diagHi Q.cells (P.xi 0) ∧
      diagLo Q.cells (P.xi 0 - 1) = diagHi Q.cells (P.xi 0 - 1) := by
  have hpriv := originalVerticalClosure_join_private P
  have hv := originalVerticalClosure_profile_content P Q v hQ
  have lift (x : ℤ × ℤ) (hx : x ∈ diagramInterior Q.cells) :
      x + v ∈ diagramInterior (originalVerticalClosure P) := by
    obtain ⟨hx, hn⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    constructor
    · rw [hQ]
      exact mem_translate.mpr (by simpa only [add_sub_cancel_right] using hx)
    · rw [hQ]
      apply mem_translate.mpr
      rw [show x + v + eCell - v = x + eCell by abel]
      exact hn
  have hc (x : ℤ × ℤ) : content (x + v) = content x := by
    simp only [content, Prod.fst_add, Prod.snd_add] at *
    omega
  exact ⟨private_diagonal_of_no_interior Q.isConnectedSkew_cells.1 (fun x hx he =>
    private_diagonal_no_interior hpriv.1 _ (lift x hx) (by rw [hc, he])),
    private_diagonal_of_no_interior Q.isConnectedSkew_cells.1 (fun x hx he =>
      private_diagonal_no_interior hpriv.2 _ (lift x hx) (by rw [hc, he]))⟩

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual complete vertical remaining matrix has exactly one join unit.
Its existence, survival, and uniqueness follow from literal cells and beta order. -/
theorem originalVerticalClosure_join_unit {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) :
    ∃! i : OriginalRemainingIndices (hD := hD) Q,
      originalResponseRows Q i = P.xi 0 ∧ originalResponseCols Q i = P.xi 0 := by
  have hpriv := originalVerticalClosure_profile_join_private P Q v hQ
  have hv := originalVerticalClosure_profile_content P Q v hQ
  have hm := originalVerticalClosure_join_cells P
  rw [hQ] at hm
  let cur : ℤ × ℤ := (-1, P.xi 0 - 1) - v
  let prev : ℤ × ℤ := (0, P.xi 0 - 1) - v
  have hc : content cur = P.xi 0 := by
    dsimp only [cur]
    simp only [content, Prod.fst_sub, Prod.snd_sub] at *
    omega
  have hp : content prev = P.xi 0 - 1 := by
    dsimp only [prev]
    simp only [content, Prod.fst_sub, Prod.snd_sub] at *
    omega
  obtain ⟨i, hi⟩ := (originalRemaining_private_unit_iff_vertical (hD := hD) Q (P.xi 0)
    cur prev (mem_translate.mp hm.1) (mem_translate.mp hm.2) hc hp hpriv.1 hpriv.2).mpr rfl
  exact ⟨i, hi, fun j hj => originalRemaining_private_unit_unique Q (P.xi 0) j i hj hi⟩

include c in
/-- Every actual upper-to-lower selected join interval contains that same
literal surviving unit. No interval-membership or endpoint inequality is assumed. -/
theorem originalVerticalClosure_join_interval_unit {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    let upper := originalVerticalClosureSelectedCopy P Q v hQ true b
    let lower := originalVerticalClosureSelectedCopy P Q v hQ false d
    ∃! i : OriginalResponseInterval (hD := hD) Q (some upper) (some lower),
      originalResponseRows Q i.1.1 = P.xi 0 ∧ originalResponseCols Q i.1.1 = P.xi 0 := by
  intro upper lower
  obtain ⟨j, hj, _⟩ := originalVerticalClosure_join_unit (hD := hD) P Q v hQ
  have hb : P.xi 0 < Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some upper))) := by
    have he := (c.originalVerticalClosure_retained_endpoints P Q v hQ true b).1
    simp only [↓reduceIte, originalRowSplitEquiv_selected] at he
    have hpos := P.xi_pos b.val.val.succ
    rw [originalRowSplitEquiv_selected]
    change P.xi 0 < Q.xi (originalVerticalClosureSelectedCopy P Q v hQ true b).val.val.succ
    omega
  have hd : Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some lower))) < P.xi 0 := by
    have he := (c.originalVerticalClosure_retained_endpoints P Q v hQ false d).2
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, originalColSplitEquiv_selected] at he
    have hpos := c.originalFirstCapDistance_gt_top P d
    unfold originalFirstCapDistance at hpos
    have htop := c.top.property
    rw [originalColSplitEquiv_selected]
    change Q.zeta (interiorBlockLast Q
      (originalVerticalClosureSelectedCopy P Q v hQ false d).val.val).castSucc < P.xi 0
    omega
  obtain ⟨i, _, hi⟩ := originalInterval_of_remaining_unit Q upper lower (P.xi 0) j hj hb hd
  refine ⟨i, hi, ?_⟩
  intro k hk
  apply Subtype.ext
  apply Subtype.ext
  exact originalRemaining_private_unit_unique Q (P.xi 0) k.1.1 i.1.1 hk hi

end SelectedCoordinate
end SkewCornerDescent.Matrix
