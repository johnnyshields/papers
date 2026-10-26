/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FullWindowBands
import SkewCornerDescent.EmptyColumn

/-!
# Literal empty root at the ordinary full-window boundary

Supports `shields-2026-skew-corner-descent.tex`, «The full-window boundary»
(`lem:boundary-full-window`).

Complete equal cell windows and their inherited singleton ordinary joining edge
produce a connected skew first band and an actual empty row or column composition.
The joining displacement is derived from adjacency, not assumed to be a root displacement.

Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- The first band has precisely the normalized endpoint contents. -/
theorem firstContentBand_extreme_contents {D : Diagram} (δ : ℤ) (hδ : 0 < δ)
    (hsmall : ∀ k, 0 ≤ k → k < δ → k ∈ contents D) :
    minContent (firstContentBand D δ) = 0 ∧
      maxContent (firstContentBand D δ) = δ - 1 := by
  have he := firstContentBand_contents δ hsmall
  constructor
  · apply minContent_eq_of
    · rw [he, Finset.mem_Ico]
      exact ⟨le_refl _, hδ⟩
    · intro k hk
      rw [he, Finset.mem_Ico] at hk
      exact hk.1
  · apply maxContent_eq_of
    · rw [he, Finset.mem_Ico]
      constructor <;> omega
    · intro k hk
      rw [he, Finset.mem_Ico] at hk
      omega

/-- An ordinary joining edge determines exactly the horizontal or vertical empty displacement. -/
theorem adjacent_empty_displacement {E : Diagram} (hE : E.Nonempty)
    {δ : ℤ} {v : ℤ × ℤ} (hlo : minContent E = 0) (hhi : maxContent E = δ - 1)
    (hv : content v = δ) (hjoin : CellAdj (ne E) (sw E + v)) :
    v = vH E ∨ v = vH E - eCell := by
  have hstep : content (sw E + v) = content (ne E) + 1 := by
    rw [content_add, content_sw hE, content_ne hE, hlo, hhi, hv]
    omega
  rw [cellAdj_iff] at hjoin
  simp only [content, Prod.fst_add, Prod.snd_add] at hstep
  rcases hjoin with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · left
    simp only [Prod.fst_add, Prod.snd_add] at hrow hcol
    apply Prod.ext
    · simp only [vH, Prod.fst_add, Prod.fst_sub, add_zero]
      omega
    · change v.2 = (ne E).2 - (sw E).2 + 1
      omega
  · right
    simp only [Prod.fst_add, Prod.snd_add] at hrow hcol
    apply Prod.ext
    · simp only [vH, eCell, Prod.fst_add, Prod.fst_sub, add_zero]
      omega
    · simp only [vH, eCell, Prod.snd_add, Prod.snd_sub]
      omega

/-- A nonempty southeast interior gives a nonempty actual first-band interior. -/
theorem fullWindow_firstBand_interior_nonempty {D : Diagram} {b : ℕ} {δ : ℤ}
    {v : ℤ × ℤ} (hb : 0 < b) (hδ : 0 < δ) (hv : content v = δ)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < (b : ℤ) * δ)
    (hwindow : upperFullWindow D b δ = translate v (lowerFullWindow D b δ))
    (hinterior : (diagramInterior D).Nonempty) :
    (diagramInterior (firstContentBand D δ)).Nonempty := by
  obtain ⟨x, hx⟩ := hinterior
  obtain ⟨hxD, hxe⟩ := Finset.mem_filter.mp hx
  have hcopies := fullWindow_cells_eq_copies hb hδ hv hbound hwindow
  rw [hcopies] at hxD
  obtain ⟨j, hj, hxy⟩ := Finset.mem_biUnion.mp hxD
  have hy := mem_translate.mp hxy
  obtain ⟨hyD, hy0, hyδ⟩ := Finset.mem_filter.mp hy
  let y := x - (j : ℤ) • v
  have hce : content (y + eCell) = content y := by
    rw [content_add]
    simp only [eCell, content, sub_self, add_zero]
  have hyeD : y + eCell ∈ D := by
    apply (fullWindow_iterate hδ hv hwindow (y + eCell)
      (by rw [hce]; exact ⟨hy0, hyδ⟩) j (Finset.mem_range.mp hj)).mp
    have he : y + eCell + (j : ℤ) • v = x + eCell := by dsimp [y]; abel
    rwa [he]
  exact ⟨y, Finset.mem_filter.mpr ⟨hy, Finset.mem_filter.mpr
    ⟨hyeD, by rw [hce]; exact ⟨hy0, hyδ⟩⟩⟩⟩

/-- The complete ordinary full-window boundary has an actual empty row or column root. -/
theorem fullWindow_boundary_root {D : Diagram} (hD : IsConnectedSkew D)
    (b : ℕ) (hb : 2 ≤ b) (δ : ℤ) (hδ : 0 < δ) (v : ℤ × ℤ)
    (hv : content v = δ) (hmin : minContent D = 0)
    (hmax : maxContent D = (b : ℤ) * δ - 1)
    (hwindow : upperFullWindow D b δ = translate v (lowerFullWindow D b δ))
    (hcut : diagLo D (δ - 1) = diagHi D (δ - 1))
    (hjoin : CellAdj (ne (firstContentBand D δ)) (sw (firstContentBand D δ) + v)) :
    ∃ E : Diagram, IsConnectedSkew E ∧ span E = δ.toNat ∧
      (emptyMarkH E).IsLegal ∧
      (D = (emptyMarkH E).compose (horizontalRow b) ∨
        D = (emptyMarkH E).compose (verticalColumn b)) ∧
      ((diagramInterior D).Nonempty → (diagramInterior E).Nonempty) := by
  have hsmall : ∀ k, 0 ≤ k → k < δ → k ∈ contents D := by
    intro k hk0 hkδ
    apply (isConnectedSkew_iff_diagonal.mp hD).mem_contents_iff.mpr
    rw [hmin, hmax]
    have hbcast : (2 : ℤ) ≤ b := by exact_mod_cast hb
    constructor <;> nlinarith
  have hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < (b : ℤ) * δ := by
    intro x hx
    have hlo := minContent_le (content_mem_contents hx)
    have hhi := le_maxContent (content_mem_contents hx)
    rw [hmin] at hlo
    rw [hmax] at hhi
    exact ⟨hlo, by omega⟩
  let E := firstContentBand D δ
  have hE := firstContentBand_isConnectedSkew hD δ hδ hsmall hmin hcut
  have hend := firstContentBand_extreme_contents δ hδ hsmall
  have hdisplacement := adjacent_empty_displacement hE.2.1 hend.1 hend.2 hv hjoin
  have hcopies := fullWindow_cells_eq_copies (by omega : 0 < b) hδ hv hbound hwindow
  refine ⟨E, hE, firstContentBand_span δ hsmall, emptyMarkH_isLegal hE, ?_, ?_⟩
  · rcases hdisplacement with hvh | hvv
    · left
      rw [(emptyMarkH E).compose_horizontalRow (by omega : 1 ≤ b)]
      simpa only [MarkedInner.rowCopies, emptyMarkH, hvh] using hcopies
    · right
      rw [compose_empty_verticalColumn E (by omega : 1 ≤ b)]
      simpa only [hvv] using hcopies
  · exact fullWindow_firstBand_interior_nonempty (by omega) hδ hv hbound hwindow

end SkewCornerDescent
