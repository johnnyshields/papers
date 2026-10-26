/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowUnitBlocks

/-!
# Complete remaining occurrences in literal source windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete windows
produce every remaining fiber of a whole nonempty block or an actual empty unit block.
Divisibility selects proper minors; it is not an independent matching assumption. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Complete nonempty components and the actual empty pivots internal to a content window. -/
def originalBlockInWindow {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (b : OriginalBlocks P) : Prop :=
  (P.zeta b.val.castSucc < P.xi b.val.succ ∧
    ∀ x ∈ interiorBlockCells P b.val, lo ≤ content x ∧ content x < hi) ∨
  (P.xi b.val.succ = P.zeta b.val.castSucc ∧
    lo < P.zeta b.val.castSucc ∧ P.xi b.val.succ < hi)

/-- Every whole source-window occurrence has a unique actual target block and a full
remaining-index equivalence, including boundary proper minors and empty unit blocks. -/
theorem originalWindow_remaining_occurrence {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (b : OriginalBlocks P)
    (hband : originalBlockInWindow P lo (hi - q) b) :
    ∃! d : OriginalBlocks P, originalBlockInWindow P (lo + q) hi d ∧
      (d.val : ℤ) = (b.val : ℤ) + v.1 ∧
      ∃ e : Fin (originalRemovedSize (hD := hD) P b) ≃
          Fin (originalRemovedSize (hD := hD) P d),
        ∀ k, originalResponseRows P ⟨d, e k⟩ = originalResponseRows P ⟨b, k⟩ + q ∧
          originalResponseCols P ⟨d, e k⟩ = originalResponseCols P ⟨b, k⟩ + q := by
  classical
  have hprod : ∃ d : OriginalBlocks P, originalBlockInWindow P (lo + q) hi d ∧
      (d.val : ℤ) = (b.val : ℤ) + v.1 ∧
      ∃ e : Fin (originalRemovedSize (hD := hD) P b) ≃
          Fin (originalRemovedSize (hD := hD) P d),
        ∀ k, originalResponseRows P ⟨d, e k⟩ = originalResponseRows P ⟨b, k⟩ + q ∧
          originalResponseCols P ⟨d, e k⟩ = originalResponseCols P ⟨b, k⟩ + q := by
    rcases hband with ⟨hb, hband⟩ | ⟨hb, hl, hh⟩
    · obtain ⟨d, he, _⟩ := originalWindow_nonempty_block_occurrence P lo hi q v
        hwindow hlo hloq hhiq hhi b hb hband
      have hr := (interiorBlockCells_translated_row_extremes P P b.val d.val.val
        hb d.property v he.symm).1
      rw [b.property, d.val.property] at hr
      have hdt : originalBlockInWindow P (lo + q) hi d.val := by
        refine Or.inl ⟨d.property, ?_⟩
        intro x hx
        rw [he] at hx
        have hmem := mem_translate.mp hx
        have hxband := hband (x - v) hmem
        have hct : content (x - v) = content x - q := by
          dsimp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
          omega
        rw [hct] at hxband
        omega
      refine ⟨d.val, hdt, hr, originalTranslatedRemovedIndexEquiv (hD := hD)
        P P b d.val hb d.property v he.symm, ?_⟩
      intro k
      simpa only [hv] using originalTranslatedBlock_removed_endpoints (hD := hD)
        P P b d.val hb d.property v he.symm k
    · have htop : hi - q + q = hi := by omega
      have hw : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi - q + q) =
          translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q) := by
        simpa only [htop] using hwindow
      obtain ⟨j, hj, hx, hz⟩ := originalWindow_complementary_position P lo (hi - q) q
        v hv hw b.val hl hh
      have he : P.xi j.succ = P.zeta j.castSucc := by rw [hx, hz, hb]
      let d : OriginalBlocks P := ⟨j, (interior_empty_block_extremes P j he).1⟩
      obtain ⟨e, hend⟩ := originalEmptyBlock_translated_endpoints (hD := hD)
        P P b d hb he q hx hz
      have hdt : originalBlockInWindow P (lo + q) hi d := by
        refine Or.inr ⟨he, ?_, ?_⟩
        · change lo + q < P.zeta j.castSucc
          rw [hz]
          omega
        · change P.xi j.succ < hi
          rw [hx]
          omega
      exact ⟨d, hdt, hj, e, hend⟩
  obtain ⟨d, hd⟩ := hprod
  refine ⟨d, hd, ?_⟩
  intro a ha
  apply Subtype.ext
  apply Fin.ext
  have hr := hd.2.1
  have hr' := ha.2.1
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
