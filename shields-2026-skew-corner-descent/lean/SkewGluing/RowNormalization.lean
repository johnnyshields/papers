/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.RowSchur
import SkewGluing.EmptyRowSchur

/-!
# Row normalization for every legal mark

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:normalization`, `eq:normalization-bounds`, `eq:row-cofactor`).
The empty-mark convention is `A = B = Θ = 1` and `C = s_(E⁻)`.  Every row coefficient
and generator bound is supplied by the actual geometric constructions.

Sorry-free.
-/

namespace SkewGluing.MarkedInner
open SkewCornerDescent.Matrix
variable (ω : MarkedInner)

/-- The actual lower-mark function, with the paper's empty-mark convention. -/
noncomputable def normalA (h : ω.IsLegal) : Lambda :=
  if hW : ω.W.Nonempty then ω.markA h hW else 1

/-- The actual periodic hatted-mark function, with the empty-mark convention. -/
noncomputable def normalB (h : ω.IsLegal) : Lambda :=
  if hW : ω.W.Nonempty then ω.hatMarkB h hW else 1

/-- The actual finite end-cap product, with the empty-mark convention. -/
noncomputable def normalTheta (h : ω.IsLegal) : Lambda :=
  if hW : ω.W.Nonempty then ω.capTheta h hW else 1

/-- The middle cofactor, equal to the full single-inner cofactor for an empty mark. -/
noncomputable def normalC (h : ω.IsLegal) : Lambda :=
  if hW : ω.W.Nonempty then ω.middleCofactor h hW
    else cellSchur (diagramInterior ω.E) h.1.1.1.interior

variable {ω}

/-- The actual row cofactor identity for every legal mark and every positive row length. -/
theorem IsLegal.interiorSchur_row_normalization (h : ω.IsLegal) {m : ℕ} (hm : 1 ≤ m) :
    cellSchur (diagramInterior (ω.rowCopies m)) (h.isConnectedSkew_rowCopies_all hm).1.interior =
      ω.normalTheta h * ω.normalC h ^ m * ω.normalB h ^ (m - 1) := by
  by_cases hW : ω.W.Nonempty
  · simpa only [normalTheta, normalC, normalB, dite_eq_left hW] using
      h.interiorSchur_rowCopies hW hm
  · simpa only [normalTheta, normalC, normalB, dite_eq_right hW, one_pow, one_mul, mul_one] using
      h.interiorSchur_rowCopies_empty (Finset.not_nonempty_iff_eq_empty.mp hW) hm

/-- The displayed cofactor formula holds for the actual four-case row composition. -/
theorem IsLegal.interiorSchur_compose_row_normalization (h : ω.IsLegal)
    {m : ℕ} (hm : 1 ≤ m) :
    cellSchur (diagramInterior (ω.compose (horizontalRow m)))
        (h.isConnectedSkew_compose_horizontalRow_all hm).1.interior =
      ω.normalTheta h * ω.normalC h ^ m * ω.normalB h ^ (m - 1) := by
  simpa only [ω.compose_horizontalRow hm] using h.interiorSchur_row_normalization hm

/-- Both mark normalization functions have span at most the mark width. -/
theorem IsLegal.normal_mark_spans (h : ω.IsLegal) :
    (polynomialSpan (ω.normalA h) : ℤ) ≤ ω.width ∧
      (polynomialSpan (ω.normalB h) : ℤ) ≤ ω.width := by
  by_cases hW : ω.W.Nonempty
  · simp only [normalA, normalB, dite_eq_left hW]
    constructor
    · exact_mod_cast h.markA_span_le hW
    · exact_mod_cast h.hatMarkB_span_le hW
  · simp only [normalA, normalB, dite_eq_right hW]
    simp [polynomialSpan]

/-- The finite cap normalization has the stated span, including width zero. -/
theorem IsLegal.normalTheta_span_le (h : ω.IsLegal) :
    (polynomialSpan (ω.normalTheta h) : ℤ) ≤ max 0 ((ω.width : ℤ) - 1) := by
  by_cases hW : ω.W.Nonempty
  · simpa only [normalTheta, dite_eq_left hW] using h.capTheta_span_le hW
  · simp [normalTheta, hW, polynomialSpan]

/-- Empty-mark inner erosion occupies at most `max (0, p - 2)` generators. -/
theorem IsLegal.empty_cofactor_span_le (h : ω.IsLegal) (hW : ω.W = ∅) :
    (polynomialSpan (cellSchur (diagramInterior ω.E) h.1.1.1.interior) : ℤ) ≤
      max 0 (ω.period - 2) := by
  have hm : maxContent ω.E = minContent ω.E + ω.period - 1 := by
    have hs := span_eq_of_isConnectedSkew h.1.1
    have hp := IsLegalEmpty.span_eq ⟨h, hW⟩
    omega
  have hg := span_le_of_content_Ioo (minContent ω.E) (minContent ω.E + ω.period - 1)
    (fun x hx => by simpa only [hm] using interior_content_strict h.1.1 hx)
  have hp := polynomialSpan_cellSchur_le (diagramInterior ω.E) h.1.1.1.interior
  have hpZ : (polynomialSpan (cellSchur (diagramInterior ω.E) h.1.1.1.interior) : ℤ) ≤
      span (diagramInterior ω.E) := by exact_mod_cast hp
  have he : minContent ω.E + ω.period - 1 - minContent ω.E - 1 = ω.period - 2 := by ring
  rw [he] at hg
  exact hpZ.trans hg

/-- The middle normalization has its strict period gap, including the empty mark. -/
theorem IsLegal.normalC_span_le (h : ω.IsLegal) :
    (polynomialSpan (ω.normalC h) : ℤ) ≤ max 0 (ω.period - ω.width - 2) := by
  by_cases hW : ω.W.Nonempty
  · simpa only [normalC, dite_eq_left hW] using h.middleCofactor_span_le hW
  · have he := Finset.not_nonempty_iff_eq_empty.mp hW
    have hw : (ω.width : ℤ) = 0 := IsLegalEmpty.width_zero ⟨h, he⟩
    simpa only [normalC, dite_eq_right hW, hw, sub_zero] using h.empty_cofactor_span_le he

/-- The hatted-middle set is exactly the southeast interior, with no representation seam. -/
theorem hatMiddle_eq_interior (D : Diagram) :
    hatMiddle D = (diagramInterior D : Set (ℤ × ℤ)) := by
  ext x
  simp only [hatMiddle, Set.mem_ofPred_eq, Finset.mem_coe, diagramInterior, Finset.mem_filter]

/-- The first actual row is the original marked inner. -/
theorem rowCopies_one : ω.rowCopies 1 = ω.E := by
  simp [rowCopies, translate_zero]

/-- The single-inner cofactor is the finite cap factor times the middle factor. -/
theorem IsLegal.interiorSchur_single_normalization (h : ω.IsLegal) :
    cellSchur (diagramInterior ω.E) h.1.1.1.interior =
      ω.normalTheta h * ω.normalC h := by
  simpa only [rowCopies_one, pow_one, Nat.sub_self, pow_zero, mul_one] using
    h.interiorSchur_row_normalization (m := 1) (by omega)

/-- All four normalization factors are nonzero actual skew functions or products. -/
theorem IsLegal.normal_factors_ne_zero (h : ω.IsLegal) :
    ω.normalA h ≠ 0 ∧ ω.normalB h ≠ 0 ∧ ω.normalC h ≠ 0 ∧ ω.normalTheta h ≠ 0 := by
  by_cases hW : ω.W.Nonempty
  · simp only [normalA, normalB, normalC, normalTheta, dite_eq_left hW,
      markA, hatMarkB, middleCofactor, capTheta]
    exact ⟨cellSchur_ne_zero _ _, cellSchur_ne_zero _ _, cellSchur_ne_zero _ _,
      mul_ne_zero (cellSchur_ne_zero _ _) (cellSchur_ne_zero _ _)⟩
  · simp only [normalA, normalB, normalC, normalTheta, dite_eq_right hW]
    exact ⟨one_ne_zero, one_ne_zero, cellSchur_ne_zero _ _, one_ne_zero⟩

/-- The normalized displayed lower cap is the translation-invariant geometric cap. -/
theorem IsLegal.lowerCap_eq_normalized (h : ω.IsLegal) (hc : minContent ω.E = 0) :
    ω.lowerCap = (diagramInterior ω.E).filter (fun x => 0 ≤ content x ∧ content x < ω.width) := by
  ext x
  simp only [lowerCap, Finset.mem_filter, hc, zero_add]
  constructor
  · rintro ⟨hx, hb⟩
    have hl := (interior_content_strict h.1.1 hx).1
    exact ⟨hx, by omega, hb⟩
  · rintro ⟨hx, _, hb⟩
    exact ⟨hx, hb⟩

/-- The normalized displayed upper cap is the translation-invariant geometric cap. -/
theorem IsLegal.upperCap_eq_normalized (h : ω.IsLegal) (hc : minContent ω.E = 0) :
    ω.upperCap = (diagramInterior ω.E).filter
      (fun x => ω.period ≤ content x ∧ content x < ω.period + ω.width) := by
  ext x
  simp only [upperCap, Finset.mem_filter, hc, zero_add]
  have he : maxContent ω.E = ω.period + ω.width - 1 := by
    have hs := span_eq_of_isConnectedSkew h.1.1
    have hp := h.1.span_eq
    omega
  constructor
  · rintro ⟨hx, hb⟩
    have hu := (interior_content_strict h.1.1 hx).2
    exact ⟨hx, by omega, by omega⟩
  · rintro ⟨hx, hb, _⟩
    exact ⟨hx, by omega⟩

end SkewGluing.MarkedInner
