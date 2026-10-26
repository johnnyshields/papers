/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowOccurrences
import SkewCornerDescent.Matrix.OriginalWindowUnitBlocks
import SkewCornerDescent.Matrix.OriginalWindowRemainingOccurrences

/-!
# Complete actual remaining fibers between literal profile windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Every complete
block occurrence has a uniquely produced counterpart, with all actual remaining rows and
columns translated, including selected proper minors and empty unit blocks. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Literal windows in two profiles identify all actual whole remaining fibers. -/
theorem originalLiteralWindow_remaining_occurrence {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhiq : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (b : OriginalBlocks P) (hband : originalBlockInWindow P lo hi b) :
    ∃! d : OriginalBlocks Q, originalBlockInWindow Q (lo + q) (hi + q) d ∧
      (d.val : ℤ) = (b.val : ℤ) + v.1 ∧
      ∃ e : Fin (originalRemovedSize (hD := hD) P b) ≃
          Fin (originalRemovedSize (hD := hD) Q d),
        ∀ k, originalResponseRows Q ⟨d, e k⟩ = originalResponseRows P ⟨b, k⟩ + q ∧
          originalResponseCols Q ⟨d, e k⟩ = originalResponseCols P ⟨b, k⟩ + q := by
  classical
  have hprod : ∃ d : OriginalBlocks Q, originalBlockInWindow Q (lo + q) (hi + q) d ∧
      (d.val : ℤ) = (b.val : ℤ) + v.1 ∧
      ∃ e : Fin (originalRemovedSize (hD := hD) P b) ≃
          Fin (originalRemovedSize (hD := hD) Q d),
        ∀ k, originalResponseRows Q ⟨d, e k⟩ = originalResponseRows P ⟨b, k⟩ + q ∧
          originalResponseCols Q ⟨d, e k⟩ = originalResponseCols P ⟨b, k⟩ + q := by
    rcases hband with ⟨hb, hband⟩ | ⟨hb, hl, hh⟩
    · obtain ⟨d, he, _⟩ := originalLiteralWindow_nonempty_block_occurrence P Q lo hi q v
        hwindow hlo hloq hhi hhiq b hb hband
      have hr := (interiorBlockCells_translated_row_extremes P Q b.val d.val.val
        hb d.property v he.symm).1
      rw [b.property, d.val.property] at hr
      have hdt : originalBlockInWindow Q (lo + q) (hi + q) d.val := by
        refine Or.inl ⟨d.property, ?_⟩
        intro x hx
        rw [he] at hx
        have hxband := hband (x - v) (mem_translate.mp hx)
        have hct : content (x - v) = content x - q := by
          dsimp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
          omega
        rw [hct] at hxband
        omega
      refine ⟨d.val, hdt, hr, originalTranslatedRemovedIndexEquiv (hD := hD)
        P Q b d.val hb d.property v he.symm, ?_⟩
      intro k
      simpa only [hv] using originalTranslatedBlock_removed_endpoints (hD := hD)
        P Q b d.val hb d.property v he.symm k
    · obtain ⟨j, hj, hx, hz⟩ := originalLiteralWindow_complementary_position P Q lo hi q
        v hv hwindow b.val hl hh
      have he : Q.xi j.succ = Q.zeta j.castSucc := by rw [hx, hz, hb]
      let d : OriginalBlocks Q := ⟨j, (interior_empty_block_extremes Q j he).1⟩
      obtain ⟨e, hend⟩ := originalEmptyBlock_translated_endpoints (hD := hD)
        P Q b d hb he q hx hz
      have hdt : originalBlockInWindow Q (lo + q) (hi + q) d := by
        refine Or.inr ⟨he, ?_, ?_⟩
        · change lo + q < Q.zeta j.castSucc
          rw [hz]
          omega
        · change Q.xi j.succ < hi + q
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
