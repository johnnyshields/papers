/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowGapAssembly

/-!
# Complete original row endpoints under literal window translation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
Equality of complete row fibers identifies both original Jacobi--Trudi endpoints.
Whole selected occurrences supply their retained endpoints separately. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Equality of complete translated row fibers preserves both original endpoints. -/
theorem originalProfile_row_fiber_endpoints {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i : Fin (n + 1)) (j : Fin (m + 1)) (v : ℤ × ℤ)
    (hrow : (j : ℤ) = (i : ℤ) + v.1)
    (hcell : ∀ b : ℤ, ((i : ℤ), b) ∈ P.cells ↔ ((j : ℤ), b + v.2) ∈ Q.cells) :
    Q.xi j = P.xi i + content v ∧ Q.zeta j = P.zeta i + content v := by
  have hp := P.xi_sub_zeta i
  have hq := Q.xi_sub_zeta j
  have hp0 := P.r_pos i
  have hq0 := Q.r_pos j
  have hlo := (Q.mem_cells_fin j _).mp ((hcell (P.zeta i + i)).mp
    ((P.mem_cells_fin i _).mpr (by omega)))
  have hhi := (Q.mem_cells_fin j _).mp ((hcell (P.xi i + i - 1)).mp
    ((P.mem_cells_fin i _).mpr (by omega)))
  have hlo' := (P.mem_cells_fin i _).mp ((hcell (Q.zeta j + j - v.2)).mpr
    (by rw [sub_add_cancel]; exact (Q.mem_cells_fin j _).mpr (by omega)))
  have hhi' := (P.mem_cells_fin i _).mp ((hcell (Q.xi j + j - 1 - v.2)).mpr
    (by rw [sub_add_cancel]; exact (Q.mem_cells_fin j _).mpr (by omega)))
  unfold content
  omega

/-- Complete equal content windows identify the fibers of any whole row in both bands. -/
theorem originalWindow_row_fiber {n : ℕ} (P : Profile n) (lo hi q : ℤ) (v : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (i j : Fin (n + 1)) (hrow : (j : ℤ) = (i : ℤ) + v.1)
    (hiBounds : lo ≤ P.zeta i ∧ P.xi i ≤ hi)
    (hjBounds : lo + q ≤ P.zeta j ∧ P.xi j ≤ hi + q) :
    ∀ b : ℤ, ((i : ℤ), b) ∈ P.cells ↔ ((j : ℤ), b + v.2) ∈ P.cells := by
  intro b
  have hc : content ((i : ℤ), b) = b - i := rfl
  have hc' : content ((j : ℤ), b + v.2) = b + v.2 - j := rfl
  have he : ((j : ℤ), b + v.2) - v = ((i : ℤ), b) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
  have hband : ((i : ℤ), b) ∈ P.cells ↔
      ((i : ℤ), b) ∈ P.cells.filter (fun x => lo ≤ content x ∧ content x < hi) := by
    rw [Finset.mem_filter]
    constructor
    · intro h
      have hb := (P.mem_cells_fin i b).mp h
      exact ⟨h, by rw [hc]; omega⟩
    · exact And.left
  have hband' : ((j : ℤ), b + v.2) ∈ P.cells ↔
      ((j : ℤ), b + v.2) ∈ P.cells.filter
        (fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    rw [Finset.mem_filter]
    constructor
    · intro h
      have hb := (P.mem_cells_fin j _).mp h
      exact ⟨h, by rw [hc']; omega⟩
    · exact And.left
  rw [hband, hband', hwindow, mem_translate, he]

/-- Literal complete window fibers supply their actual row and column endpoint translations. -/
theorem originalWindow_row_endpoints {n : ℕ} (P : Profile n) (lo hi q : ℤ)
    (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (i j : Fin (n + 1)) (hrow : (j : ℤ) = (i : ℤ) + v.1)
    (hiBounds : lo ≤ P.zeta i ∧ P.xi i ≤ hi)
    (hjBounds : lo + q ≤ P.zeta j ∧ P.xi j ≤ hi + q) :
    P.xi j = P.xi i + q ∧ P.zeta j = P.zeta i + q := by
  simpa only [hv] using originalProfile_row_fiber_endpoints P P i j v hrow
    (originalWindow_row_fiber P lo hi q v hwindow i j hrow hiBounds hjBounds)

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

include c in
/-- Translation of whole actual selected components preserves both retained endpoints. -/
theorem originalSelected_translated_endpoints {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : OriginalSelectedBlocks (hD := hD) P) (d : OriginalSelectedBlocks (hD := hD) Q)
    (v : ℤ × ℤ) (hcell : translate v (interiorBlockCells P b.val.val) =
      interiorBlockCells Q d.val.val) :
    Q.xi d.val.val.succ = P.xi b.val.val.succ + content v ∧
      Q.zeta (interiorBlockLast Q d.val.val).castSucc =
        P.zeta (interiorBlockLast P b.val.val).castSucc + content v := by
  have he := congrArg minContent hcell
  rw [minContent_translate
    ((interiorBlockCells_connected P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)).2.1),
    interiorBlockCells_minContent P b.val.val
      (originalBlockSelected_nonempty P b.val b.property),
    interiorBlockCells_minContent Q d.val.val
      (originalBlockSelected_nonempty Q d.val d.property)] at he
  have hp := c.originalSelected_endpoint_distance P b
  have hq := c.originalSelected_endpoint_distance Q d
  omega

end SelectedCoordinate
end SkewCornerDescent.Matrix
