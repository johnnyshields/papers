/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalHorizontalSplice
import SkewCornerDescent.Matrix.OriginalPrivateUnitVertex
import SkewCornerDescent.Matrix.OriginalClosureRemaining

/-!
# The actual horizontal closure has a private join

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The exact two-copy interior excludes both diagonals adjacent to the join.
Skew convexity then supplies their singleton flags. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Neither copy of the actual source interior meets the two join diagonals. -/
theorem originalHorizontalClosure_join_no_interior {n : ℕ} (P : Profile n) :
    (∀ x ∈ diagramInterior (originalHorizontalClosure P), content x ≠ P.xi 0) ∧
      (∀ x ∈ diagramInterior (originalHorizontalClosure P), content x ≠ P.xi 0 - 1) := by
  have bounds {x : ℤ × ℤ} (hx : x ∈ diagramInterior P.cells) :
      0 < content x ∧ content x < P.xi 0 - 1 := by
    have hb := interior_content_strict P.isConnectedSkew_cells hx
    simpa only [P.minContent_cells, P.maxContent_cells] using hb
  have exclude (k : ℤ) (hk : k = P.xi 0 ∨ k = P.xi 0 - 1) :
      ∀ x ∈ diagramInterior (originalHorizontalClosure P), content x ≠ k := by
    intro x hx heq
    rw [originalHorizontalClosure_interior] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hb := bounds hx
      rcases hk with hk | hk <;> omega
    · have hm := mem_translate.mp hx
      have hb := bounds hm
      have ht : content (x - vH P.cells) = content x - P.xi 0 := by
        have hv := originalHorizontalDisplacement_content P
        rw [P.zeta_last] at hv
        simp only [content, Prod.fst_sub, Prod.snd_sub] at *
        omega
      rcases hk with hk | hk <;> omega
  exact ⟨exclude _ (Or.inl rfl), exclude _ (Or.inr rfl)⟩

/-- The horizontal reference's adjacent join diagonals are actual private
singletons (with the empty-diagonal convention included). -/
theorem originalHorizontalClosure_join_private {n : ℕ} (P : Profile n) :
    diagLo (originalHorizontalClosure P) (P.xi 0) =
        diagHi (originalHorizontalClosure P) (P.xi 0) ∧
      diagLo (originalHorizontalClosure P) (P.xi 0 - 1) =
        diagHi (originalHorizontalClosure P) (P.xi 0 - 1) := by
  have hno := originalHorizontalClosure_join_no_interior P
  exact ⟨private_diagonal_of_no_interior (originalHorizontalClosure_connected P).1 hno.1,
    private_diagonal_of_no_interior (originalHorizontalClosure_connected P).1 hno.2⟩

/-- A canonical profile of the literal closure inherits both actual private
join flags. Its normalization has zero content displacement. -/
theorem originalHorizontalClosure_profile_join_private {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    diagLo Q.cells (P.xi 0) = diagHi Q.cells (P.xi 0) ∧
      diagLo Q.cells (P.xi 0 - 1) = diagHi Q.cells (P.xi 0 - 1) := by
  have hv := (originalHorizontalClosure_profile_rows P Q v hQ).2
  have hno := originalHorizontalClosure_join_no_interior P
  have lift (x : ℤ × ℤ) (hx : x ∈ diagramInterior Q.cells) :
      x + v ∈ diagramInterior (originalHorizontalClosure P) := by
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
    rw [hv]
    simp only [content, Prod.fst_add, Prod.snd_add]
    ring
  exact ⟨private_diagonal_of_no_interior Q.isConnectedSkew_cells.1 (fun x hx he =>
    hno.1 _ (lift x hx) (by rw [hc, he])),
    private_diagonal_of_no_interior Q.isConnectedSkew_cells.1 (fun x hx he =>
    hno.2 _ (lift x hx) (by rw [hc, he]))⟩

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every complete remaining source column has content strictly between its
two exterior boundaries, including a literal unit column. -/
theorem originalResponseCols_strict_bounds {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) :
    0 < originalResponseCols P j ∧ originalResponseCols P j < P.xi 0 := by
  let i := originalRemovedCol (hD := hD) P j.1 j.2
  have hlo := P.zeta_strictAnti (show i.castSucc < Fin.last n by
    change i.val < n
    exact i.isLt)
  rw [P.zeta_last] at hlo
  have hle := P.zeta_strictAnti.antitone (show (0 : Fin (n + 1)) ≤ i.castSucc by
    exact Fin.zero_le _)
  have hspan := P.xi_sub_zeta (0 : Fin (n + 1))
  have hpos := P.r_pos (0 : Fin (n + 1))
  change 0 < P.zeta i.castSucc ∧ P.zeta i.castSucc < P.xi 0
  omega

/-- The complete horizontal closure has no original beta-unit column at the
join. Both whole remaining source copies stay on strict opposite sides. -/
theorem originalHorizontalClosure_join_no_unit {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (j : OriginalRemainingIndices (hD := hD) Q) :
    originalResponseCols Q j ≠ P.xi 0 := by
  obtain ⟨i, rfl⟩ := (originalClosureRemainingEquiv P Q v hQ).surjective j
  rcases i with i | i
  · rw [originalClosureRemainingEquiv_upper]
    have he := (originalHorizontalClosure_remaining_endpoints P Q v hQ true i).2
    have hb := originalResponseCols_strict_bounds P i
    simp only [originalClosureBlockDisplacement, ↓reduceIte] at he
    omega
  · rw [originalClosureRemainingEquiv_lower]
    have he := (originalHorizontalClosure_remaining_endpoints P Q v hQ false i).2
    have hb := originalResponseCols_strict_bounds P i
    simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte] at he
    omega

end SelectedCoordinate

end SkewCornerDescent.Matrix
