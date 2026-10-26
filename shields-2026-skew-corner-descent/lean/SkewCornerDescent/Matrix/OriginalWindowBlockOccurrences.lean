/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowBlockMatrices

/-!
# All nonempty original block occurrences in literal equal windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
The complete geometric component inventory supplies the matching of every nonempty
original block, selected or not. Repeated equal functions are not identified. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Every whole geometric component has a canonical nonempty original block representative. -/
theorem exists_originalBlock_of_component {n : ℕ} (P : Profile n) (C : Diagram)
    (hC : C ∈ edgeComponents (diagramInterior P.cells)) :
    ∃ b : OriginalBlocks P, P.zeta b.val.castSucc < P.xi b.val.succ ∧
      interiorBlockCells P b.val = C := by
  obtain ⟨i, hi, he⟩ := (interior_components_eq_blocks P C).mp hC
  let b : OriginalBlocks P := ⟨interiorBlockFirst P i, interiorBlockFirst_idem P i⟩
  have hl : interiorBlock P b.val = interiorBlock P i :=
    (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)
  exact ⟨b, interior_block_row_nonempty P hi hl,
    (interiorBlockCells_eq_of_label_eq P hl).trans he.symm⟩

/-- A complete nonempty occurrence has only one canonical original block representative. -/
theorem originalBlock_nonempty_cells_unique {n : ℕ} (P : Profile n)
    (b d : OriginalBlocks P) (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : P.zeta d.val.castSucc < P.xi d.val.succ)
    (he : interiorBlockCells P b.val = interiorBlockCells P d.val) : b = d := by
  have h := (interiorBlockCells_translated_row_extremes P P b.val d.val hb hd 0
    (by simpa only [SkewGluing.translate_zero] using he)).1
  rw [b.property, d.property] at h
  change (d.val : ℤ) = (b.val : ℤ) + 0 at h
  exact Subtype.ext (Fin.ext (by omega))

/-- Complete equal end windows match every nonempty block, with no selection assumption. -/
theorem originalWindow_nonempty_block_occurrence {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (b : OriginalBlocks P) (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hband : ∀ x ∈ interiorBlockCells P b.val, lo ≤ content x ∧ content x < hi - q) :
    ∃! d : {d : OriginalBlocks P // P.zeta d.val.castSucc < P.xi d.val.succ},
      interiorBlockCells P d.val.val = translate v (interiorBlockCells P b.val) := by
  classical
  have hc : interiorBlockCells P b.val ∈
      edgeComponents (diagramInterior (P.cells.filter
        fun x => lo ≤ content x ∧ content x < hi - q)) := by
    rw [interior_content_filter P.cells (fun k => lo ≤ k ∧ k < hi - q),
      edgeComponents_interval_of_gaps lo (hi - q) hlo hhiq, Finset.mem_filter]
    exact ⟨interiorBlockCells_mem_components P b.val hb, hband⟩
  have hct : translate v (interiorBlockCells P b.val) ∈
      edgeComponents (diagramInterior (P.cells.filter
        fun x => lo + q ≤ content x ∧ content x < hi)) := by
    rw [hwindow, interior_translate, edgeComponents_translate]
    exact Finset.mem_image.mpr ⟨_, hc, rfl⟩
  rw [interior_content_filter P.cells (fun k => lo + q ≤ k ∧ k < hi),
    edgeComponents_interval_of_gaps (lo + q) hi hloq hhi, Finset.mem_filter] at hct
  obtain ⟨d, hd, he⟩ := exists_originalBlock_of_component P _ hct.1
  refine ⟨⟨d, hd⟩, he, ?_⟩
  intro e he'
  apply Subtype.ext
  exact originalBlock_nonempty_cells_unique P e.val d e.property hd (he'.trans he.symm)

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Matching whole block occurrences preserve actual divisibility selection in both directions. -/
theorem originalBlockSelected_translated_iff {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : OriginalBlocks P) (d : OriginalBlocks Q)
    (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hd : Q.zeta d.val.castSucc < Q.xi d.val.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b.val) = interiorBlockCells Q d.val) :
    originalBlockSelected (hD := hD) P b ↔ originalBlockSelected (hD := hD) Q d := by
  rw [originalBlockSelected, originalBlockSelected,
    dvd_originalBlock_iff (hD := hD) P b.val hb,
    dvd_originalBlock_iff (hD := hD) Q d.val hd]
  have hs := cellSchur_translate (interiorBlockCells P b.val)
    (interiorBlockCells_connected P b.val hb).1 v
  have hfun : cellSchur (interiorBlockCells P b.val)
      (interiorBlockCells_connected P b.val hb).1 =
    cellSchur (interiorBlockCells Q d.val) (interiorBlockCells_connected Q d.val hd).1 := by
    simpa only [he] using hs.symm
  rw [hfun]

end SelectedCoordinate
end SkewCornerDescent.Matrix
