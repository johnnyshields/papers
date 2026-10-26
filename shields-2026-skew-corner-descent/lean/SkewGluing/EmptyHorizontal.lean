/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.RowNormalization

/-!
# The horizontal empty mark

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Sorry-free.
-/

namespace SkewGluing

-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/MarkLocality.lean, horizontal empty mark.
/-- The empty mark with the horizontal edge reading. -/
def emptyMarkH (E : Diagram) : MarkedInner where
  E := E
  W := ∅
  v := vH E
  case := .a

-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/MarkLocality.lean, empty-mark legality.
/-- The empty mark on `E` (horizontal edge reading) is legal for a connected skew diagram `E`. -/
theorem emptyMarkH_isLegal {E : Diagram} (hE : IsConnectedSkew E) : (emptyMarkH E).IsLegal := by
  have hne := hE.2.1
  have hper : (emptyMarkH E).period = (span E : ℤ) := by
    change content (vH E) = (span E : ℤ)
    unfold vH
    rw [content_add, MarkedInner.content_sub, content_ne hne, content_sw hne,
        span_eq_of_isConnectedSkew hE]
    simp [content]
  have hw : (emptyMarkH E).width = 0 := by
    simp [MarkedInner.width, emptyMarkH, span, contents]
  have hspan : 0 < span E := Finset.card_pos.mpr (hne.image _)
  have hW : (emptyMarkH E).W = ∅ := rfl
  have hup : (emptyMarkH E).upper = ∅ := by
    simp [MarkedInner.upper, emptyMarkH, translate]
  refine ⟨⟨hE, Or.inl ⟨rfl, rfl, rfl⟩⟩, MarkedInner.isMaximal_of_empty hW, ?_, ⟨?_, ?_⟩,
    MarkedInner.noHatAdjacency_of_empty hW⟩
  · refine ⟨by simp [hw], ?_⟩
    rw [hper, hw]
    simpa using hspan
  · change IsConnectedSkew (E \ ∅)
    simpa using hE
  · rw [hup, Finset.sdiff_empty]
    exact hE

end SkewGluing
