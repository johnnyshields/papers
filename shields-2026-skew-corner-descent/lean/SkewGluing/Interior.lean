/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.Diagram

/-!
# Southeast interiors

Formalizes the southeast-interior convention and its endpoint content bound from
`shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores» (`sec:corner`,
`lem:interior-bounds`).

Sorry-free.
-/

namespace SkewGluing

/-- The southeast interior \(D^-\), consisting of cells whose southeast neighbor is in \(D\). -/
def diagramInterior (D : Diagram) : Diagram :=
  D.filter fun x => x + eCell ∈ D

/-- The interior of a connected skew diagram avoids both extreme content diagonals.

This is the geometric endpoint exclusion used in `lem:interior-bounds`. -/
theorem interior_content_strict {D : Diagram} (h : IsConnectedSkew D)
    {x : ℤ × ℤ} (hx : x ∈ diagramInterior D) :
    minContent D < content x ∧ content x < maxContent D := by
  have hshape := isConnectedSkew_iff_diagonal.mp h
  have hx' : x ∈ D ∧ x + eCell ∈ D := Finset.mem_filter.mp hx
  have hk := content_mem_contents hx'.1
  have hmin : diagLo D (minContent D) = diagHi D (minContent D) :=
    hshape.2.2.2.2 _ (minContent_mem hshape.1)
      (Or.inl (fun hm => by have := minContent_le hm; omega))
  have hmax : diagLo D (maxContent D) = diagHi D (maxContent D) :=
    hshape.2.2.2.2 _ (maxContent_mem hshape.1)
      (Or.inr (fun hm => by have := le_maxContent hm; omega))
  constructor
  · by_contra hnot
    have heq : content x = minContent D := by
      have := minContent_le hk
      omega
    have hxlo := diagLo_le (D := D) (k := minContent D) hx'.1
      (by simpa [content] using heq)
    have hnexthi := le_diagHi (D := D) (k := minContent D) hx'.2
      (by simpa [content, eCell] using heq)
    have : x.1 + 1 ≤ x.1 := by
      calc
        x.1 + 1 ≤ diagHi D (minContent D) := by simpa [eCell] using hnexthi
        _ = diagLo D (minContent D) := hmin.symm
        _ ≤ x.1 := hxlo
    omega
  · by_contra hnot
    have heq : content x = maxContent D := by
      have := le_maxContent hk
      omega
    have hxlo := diagLo_le (D := D) (k := maxContent D) hx'.1
      (by simpa [content] using heq)
    have hnexthi := le_diagHi (D := D) (k := maxContent D) hx'.2
      (by simpa [content, eCell] using heq)
    have : x.1 + 1 ≤ x.1 := by
      calc
        x.1 + 1 ≤ diagHi D (maxContent D) := by simpa [eCell] using hnexthi
        _ = diagLo D (maxContent D) := hmax.symm
        _ ≤ x.1 := hxlo
    omega

/-- The southeast interior uses at most `span D - 2` content diagonals when `D` has at least
two content diagonals. This is the content-count part of `lem:interior-bounds`. -/
theorem interior_span_le {D : Diagram} (h : IsConnectedSkew D) (hspan : 2 ≤ span D) :
    (span (diagramInterior D) : ℤ) ≤ (span D : ℤ) - 2 := by
  have hsubset : contents (diagramInterior D) ⊆
      Finset.Ioo (minContent D) (maxContent D) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
    exact Finset.mem_Ioo.mpr (interior_content_strict h hx)
  have hcard := Finset.card_le_card hsubset
  have hconnected := span_eq_of_isConnectedSkew h
  have hspanZ : (2 : ℤ) ≤ (span D : ℤ) := by exact_mod_cast hspan
  rw [hconnected] at hspanZ
  have hminmax : minContent D < maxContent D := by omega
  have hinterval : (Finset.Ioo (minContent D) (maxContent D)).card =
      maxContent D - minContent D - 1 := by
    rw [Int.card_Ioo]
    omega
  have hcardZ : ((contents (diagramInterior D)).card : ℤ) ≤
      ((Finset.Ioo (minContent D) (maxContent D)).card : ℤ) := by exact_mod_cast hcard
  rw [hinterval] at hcardZ
  change ((contents (diagramInterior D)).card : ℤ) ≤ (span D : ℤ) - 2
  rw [hconnected]
  omega
/-- A connected skew diagram with at least two cells occupies at least two content diagonals. -/
theorem two_le_span_of_two_le_card {D : Diagram} (h : IsConnectedSkew D)
    (hcard : 2 ≤ D.card) : 2 ≤ span D := by
  have hDne : D.Nonempty := h.2.1
  have hspanpos : 0 < span D := by
    unfold span
    exact Finset.card_pos.mpr (Finset.image_nonempty.mpr hDne)
  by_contra hsmall
  have hspanone : span D = 1 := by omega
  have hspanEq := span_eq_of_isConnectedSkew h
  have hminmax : minContent D = maxContent D := by
    rw [hspanone] at hspanEq
    omega
  have hcontent : ∀ {x : ℤ × ℤ}, x ∈ D → content x = minContent D := by
    intro x hx
    have hk := content_mem_contents hx
    have h1 := minContent_le hk
    have h2 := le_maxContent hk
    omega
  have hpair : ∀ x ∈ D, ∀ y ∈ D, x = y := by
    intro x hx y hy
    have hpath := h.2.2 x hx y hy
    have key : ∀ z, Relation.ReflTransGen
        (fun a b => a ∈ D ∧ b ∈ D ∧ CellAdj a b) x z → z = x := by
      intro z hz
      induction hz with
      | refl => rfl
      | @tail b c hxb hbc ih =>
        have hsame : content b = content c := by
          rw [hcontent hbc.1, hcontent hbc.2.1]
        have hadj := content_adj hbc.2.2
        have : False := by omega
        exact this.elim
    exact (key y hpath).symm
  have hDcard : D.card ≤ 1 := Finset.card_le_one.mpr hpair
  omega

/-- The content-count interior bound follows from the paper's two-cell hypothesis. -/
theorem interior_span_le_of_two_le_card {D : Diagram} (h : IsConnectedSkew D)
    (hcard : 2 ≤ D.card) :
    (span (diagramInterior D) : ℤ) ≤ (span D : ℤ) - 2 :=
  interior_span_le h (two_le_span_of_two_le_card h hcard)

end SkewGluing
