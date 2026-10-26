/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.HorizontalRow

/-!
# Empty-mark row erosion

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:erosion-union`).  Distinct empty-mark copies have disjoint
content blocks.  The full row erosion identity includes both empty and nonempty marks.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- Distinct empty-mark copies cannot occupy a common content diagonal. -/
theorem IsLegal.empty_rowCopies_eq_index (h : ω.IsLegal) (hW : ω.W = ∅)
    (i j k : ℤ) (hi : k ∈ contents (translate (i • ω.v) ω.E))
    (hj : k ∈ contents (translate (j • ω.v) ω.E)) : i = j := by
  have hw : ω.width = 0 := by simp only [width, span, contents, hW, Finset.image_empty,
    Finset.card_empty]
  have hp : 0 < ω.period := by have := h.2.2.1.2; omega
  have hs := h.1.span_eq
  have hsp := span_eq_of_isConnectedSkew h.1.1
  have hm : maxContent ω.E = minContent ω.E + ω.period - 1 := by omega
  have hi' := mem_contents_translate.mp hi
  have hj' := mem_contents_translate.mp hj
  rw [content_smul] at hi' hj'
  change k - i * ω.period ∈ contents ω.E at hi'
  change k - j * ω.period ∈ contents ω.E at hj'
  have hiL := minContent_le hi'
  have hiU := le_maxContent hi'
  have hjL := minContent_le hj'
  have hjU := le_maxContent hj'
  have hij : i ≤ j := by
    by_contra hh
    have hh' : 1 ≤ i - j := by omega
    have hmul := mul_le_mul_of_nonneg_right hh' (le_of_lt hp)
    nlinarith
  have hji : j ≤ i := by
    by_contra hh
    have hh' : 1 ≤ j - i := by omega
    have hmul := mul_le_mul_of_nonneg_right hh' (le_of_lt hp)
    nlinarith
  omega

/-- The arbitrary row-union erosion formula for every legal mark, including the empty mark. -/
theorem IsLegal.interior_rowCopies_all (h : ω.IsLegal) (m : ℕ) :
    diagramInterior (ω.rowCopies m) =
      (Finset.range m).biUnion fun j => translate ((j : ℤ) • ω.v) (diagramInterior ω.E) := by
  by_cases hW : ω.W.Nonempty
  · exact h.interior_rowCopies hW m
  · have he : ω.W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    unfold rowCopies
    rw [interior_biUnion_of_overlap (Finset.range m)
      (fun j : ℕ => translate ((j : ℤ) • ω.v) ω.E)
      (fun _ _ => isSkew_translate _ h.1.1.1) ?_]
    · simp only [interior_translate]
    · intro i _ j _ k hi hj
      have hij := h.empty_rowCopies_eq_index he i j k hi hj
      have hij' : i = j := by omega
      subst hij'
      simpa only [Finset.inter_self] using hi

/-- The paper's erosion formula for the actual composition,
without an extra nonempty-mark binder. -/
theorem IsLegal.interior_compose_horizontalRow_all (h : ω.IsLegal) {m : ℕ} (hm : 1 ≤ m) :
    diagramInterior (ω.compose (horizontalRow m)) =
      (Finset.range m).biUnion fun j => translate ((j : ℤ) • ω.v) (diagramInterior ω.E) := by
  rw [ω.compose_horizontalRow hm]
  exact h.interior_rowCopies_all m

end SkewGluing.MarkedInner
