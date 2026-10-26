/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.FiniteCaps
import SkewGluing.PolynomialSupport
import SkewGluing.DisconnectedTableau

/-!
# Schur factorization over finite end caps

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`sec:marks`, `eq:normalization`, `eq:row-cofactor`, `eq:normalization-bounds`).

An unoccupied content diagonal splits a skew Schur function into a product. Applying the
two private gaps gives the finite-cap factorization of the interior of one marked inner.

Sorry-free.
-/

namespace SkewGluing

open SkewCornerDescent.Matrix

/-- An empty diagonal separates two skew component products. -/
theorem cellSchur_split_gap {D : Diagram} (hs : IsSkew D) (k : ℤ)
    (hg : ∀ x ∈ D, content x ≠ k) :
    cellSchur D hs =
      cellSchur (D.filter fun x => content x < k) (hs.filter_content_lt_of_gap k hg) *
      cellSchur (D.filter fun x => k < content x) (hs.filter_content_gt_of_gap k hg) := by
  let A := D.filter fun x => content x < k
  let B := D.filter fun x => k < content x
  have he : A ∪ B = D := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · tauto
    · intro hx
      have := hg x hx
      rcases lt_or_gt_of_ne this with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hu : IsSkew (A ∪ B) := he.symm ▸ hs
  rw [← cellSchur_congr he hu hs]
  apply cellSchur_union
  · exact Finset.disjoint_left.mpr (by
      intro x hxA hxB
      have hA := (Finset.mem_filter.mp hxA).2
      have hB := (Finset.mem_filter.mp hxB).2
      omega)
  · intro a ha b hb hadj
    have hA := (Finset.mem_filter.mp ha).2
    have hB := (Finset.mem_filter.mp hb).2
    rw [cellAdj_iff] at hadj
    simp only [content] at hA hB
    omega

namespace MarkedInner

variable {ω : MarkedInner}

/-- The finite normalization factor is the product of the actual two cap functions. -/
noncomputable def capTheta (ω : MarkedInner) (h : ω.IsLegal) (hW : ω.W.Nonempty) : Lambda :=
  cellSchur ω.lowerCap (h.isSkew_lowerCap hW) * cellSchur ω.upperCap (h.isSkew_upperCap hW)

/-- The middle normalization factor is its actual southeast interior function. -/
noncomputable def middleCofactor (ω : MarkedInner) (h : ω.IsLegal) (hW : ω.W.Nonempty) : Lambda :=
  cellSchur (diagramInterior ω.middle) (h.middle_connected hW).1.interior

/-- The corner cofactor of one marked inner is the finite-cap factor times the middle factor. -/
theorem IsLegal.interiorSchur_eq_caps (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    cellSchur (diagramInterior ω.E) h.1.1.1.interior =
      ω.capTheta h hW * ω.middleCofactor h hW := by
  let I := diagramInterior ω.E
  let a : ℤ := minContent ω.E + ω.width
  let b : ℤ := minContent ω.E + ω.period - 1
  let T := I.filter fun x => a < content x
  have hI : IsSkew I := h.1.1.1.interior
  have hgA : ∀ x ∈ I, content x ≠ a := fun _ hx => (h.interior_private_gaps hW hx).1
  have hgB : ∀ x ∈ I, content x ≠ b := fun _ hx => (h.interior_private_gaps hW hx).2
  have hT := hI.filter_content_gt_of_gap a hgA
  have hgT : ∀ x ∈ T, content x ≠ b := fun _ hx => hgB _ (Finset.mem_filter.mp hx).1
  have hmiddle : (T.filter fun x => content x < b) = diagramInterior ω.middle := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT, hxb⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxI, hxa⟩ := Finset.mem_filter.mp hxT
      change x ∈ diagramInterior ω.E at hxI
      change minContent ω.E + ω.width < content x at hxa
      change content x < minContent ω.E + ω.period - 1 at hxb
      have he := h.interior_eq_caps hW
      rw [he, Finset.mem_union, Finset.mem_union] at hxI
      rcases hxI with (hx | hx) | hx
      · have := (Finset.mem_filter.mp hx).2
        omega
      · exact hx
      · have := (Finset.mem_filter.mp hx).2
        omega
    · intro hx
      have hc := h.middleInterior_content hW hx
      obtain ⟨hxO, hxeO⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨(mem_middle.mp hxO).1, (mem_middle.mp hxeO).1⟩, hc.1⟩, hc.2⟩
  have hupper : (T.filter fun x => b < content x) = ω.upperCap := by
    ext x
    simp only [T, upperCap, Finset.mem_filter]
    have hwq := h.2.2.1.2
    change ((x ∈ I ∧ a < content x) ∧ b < content x) ↔ x ∈ I ∧ b < content x
    have hab : a ≤ b := by dsimp [a, b]; omega
    constructor
    · rintro ⟨⟨hx, _⟩, hxb⟩
      exact ⟨hx, hxb⟩
    · rintro ⟨hx, hxb⟩
      exact ⟨⟨hx, hab.trans_lt hxb⟩, hxb⟩
  have hsplit := cellSchur_split_gap hI a hgA
  have hsplitT := cellSchur_split_gap hT b hgT
  rw [cellSchur_congr hmiddle _ (h.middle_connected hW).1.interior,
    cellSchur_congr hupper _ (h.isSkew_upperCap hW)] at hsplitT
  have heq : cellSchur I hI = cellSchur ω.lowerCap (h.isSkew_lowerCap hW) *
      (cellSchur (diagramInterior ω.middle) (h.middle_connected hW).1.interior *
        cellSchur ω.upperCap (h.isSkew_upperCap hW)) :=
    hsplit.trans (congrArg (fun f => cellSchur ω.lowerCap (h.isSkew_lowerCap hW) * f) hsplitT)
  refine heq.trans ?_
  dsimp only [capTheta, middleCofactor]
  rw [mul_assoc, mul_comm (cellSchur ω.upperCap (h.isSkew_upperCap hW))]

/-- The finite normalization factor has generator span at most `max (0, w - 1)`. -/
theorem IsLegal.capTheta_span_le (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    (polynomialSpan (ω.capTheta h hW) : ℤ) ≤ max 0 ((ω.width : ℤ) - 1) := by
  have hL := polynomialSpan_cellSchur_le ω.lowerCap (h.isSkew_lowerCap hW)
  have hU := polynomialSpan_cellSchur_le ω.upperCap (h.isSkew_upperCap hW)
  have hLZ : (polynomialSpan (cellSchur ω.lowerCap (h.isSkew_lowerCap hW)) : ℤ) ≤
      span ω.lowerCap := by exact_mod_cast hL
  have hUZ : (polynomialSpan (cellSchur ω.upperCap (h.isSkew_upperCap hW)) : ℤ) ≤
      span ω.upperCap := by exact_mod_cast hU
  rw [capTheta, polynomialSpan_mul _ _
    (cellSchur_ne_zero _ _) (cellSchur_ne_zero _ _), Nat.cast_max]
  exact max_le (hLZ.trans h.lowerCap_span_le) (hUZ.trans (h.upperCap_span_le hW))

/-- The middle normalization factor has generator span at most `max (0, p - w - 2)`. -/
theorem IsLegal.middleCofactor_span_le (h : ω.IsLegal) (hW : ω.W.Nonempty) :
    (polynomialSpan (ω.middleCofactor h hW) : ℤ) ≤ max 0 (ω.period - ω.width - 2) := by
  have hs := polynomialSpan_cellSchur_le (diagramInterior ω.middle)
    (h.middle_connected hW).1.interior
  have hsZ : (polynomialSpan (ω.middleCofactor h hW) : ℤ) ≤
      span (diagramInterior ω.middle) := by exact_mod_cast hs
  exact hsZ.trans (h.middleInterior_span_le hW)

end MarkedInner

end SkewGluing
