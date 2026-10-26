/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.PeriodicHat

/-!
# Erosion of arbitrary finite rows of inner copies

Formalizes `shields-2026-skew-corner-descent.tex`, «Marked inners and finite end caps»
(`lem:row-amalgamation`, `eq:erosion-union`).  Only equal or consecutive translated copies
can share a content diagonal.  On consecutive copies the common diagonal meets the actual mark.

Sorry-free.
-/

namespace SkewGluing.MarkedInner

variable {ω : MarkedInner}

/-- The cell union of a row of `m` translated inner copies. -/
def rowCopies (ω : MarkedInner) (m : ℕ) : Diagram :=
  (Finset.range m).biUnion fun j => translate ((j : ℤ) • ω.v) ω.E

/-- Any common content diagonal of two row copies has a common cell. -/
theorem IsLegal.rowCopies_diagonal_overlap (h : ω.IsLegal) (hW : ω.W.Nonempty)
    (i j : ℤ) (k : ℤ)
    (hi : k ∈ contents (translate (i • ω.v) ω.E))
    (hj : k ∈ contents (translate (j • ω.v) ω.E)) :
    k ∈ contents (translate (i • ω.v) ω.E ∩ translate (j • ω.v) ω.E) := by
  have hn := h.isNonemptyMark hW
  have hm := hn.maxContent_E h.1.1
  have hq := h.2.2.1.2
  have hp : 0 < ω.period := by omega
  have hi' := mem_contents_translate.mp hi
  have hj' := mem_contents_translate.mp hj
  rw [content_smul] at hi' hj'
  change k - i * ω.period ∈ contents ω.E at hi'
  change k - j * ω.period ∈ contents ω.E at hj'
  have hiL := minContent_le hi'
  have hiU := le_maxContent hi'
  have hjL := minContent_le hj'
  have hjU := le_maxContent hj'
  have hnear : i = j ∨ i + 1 = j ∨ j + 1 = i := by
    have hij : i - j ≤ 1 := by
      by_contra hh
      have hh' : 2 ≤ i - j := by omega
      have hmul := mul_le_mul_of_nonneg_right hh' (le_of_lt hp)
      nlinarith
    have hji : j - i ≤ 1 := by
      by_contra hh
      have hh' : 2 ≤ j - i := by omega
      have hmul := mul_le_mul_of_nonneg_right hh' (le_of_lt hp)
      nlinarith
    omega
  have consecutive : ∀ a b : ℤ, a + 1 = b →
      k ∈ contents (translate (a • ω.v) ω.E) →
      k ∈ contents (translate (b • ω.v) ω.E) →
      k ∈ contents (translate (a • ω.v) ω.E ∩ translate (b • ω.v) ω.E) := by
    intro a b hab ha hb
    have hb' := mem_contents_translate.mp hb
    have ha' : k - content (b • ω.v) ∈ contents (translate (-ω.v) ω.E) := by
      rw [mem_contents_translate]
      have ha0 := mem_contents_translate.mp ha
      convert ha0 using 1
      rw [content_smul, content_smul]
      simp only [content, Prod.fst_neg, Prod.snd_neg]
      rw [← hab]
      ring
    obtain ⟨z, hz, hcz⟩ := exists_cell_of_mem_contents
      (h.window_diagonal_overlap hW _ hb' ha')
    obtain ⟨hzE, hzT⟩ := Finset.mem_inter.mp hz
    rw [contents, Finset.mem_image]
    refine ⟨z + b • ω.v, ?_, ?_⟩
    · apply Finset.mem_inter.mpr
      constructor
      · rw [mem_translate] at hzT ⊢
        rw [← hab]
        convert hzT using 1
        module
      · rw [mem_translate]
        simpa only [add_sub_cancel_right] using hzE
    · rw [content_add, hcz]
      omega
  rcases hnear with rfl | hij | hji
  · simpa only [Finset.inter_self] using hi
  · exact consecutive i j hij hi hj
  · rw [Finset.inter_comm]
    exact consecutive j i hji hj hi

/-- Southeast erosion commutes with the entire row union for every finite row length. -/
theorem IsLegal.interior_rowCopies (h : ω.IsLegal) (hW : ω.W.Nonempty) (m : ℕ) :
    diagramInterior (ω.rowCopies m) =
      (Finset.range m).biUnion fun j => translate ((j : ℤ) • ω.v) (diagramInterior ω.E) := by
  unfold rowCopies
  rw [interior_biUnion_of_overlap (Finset.range m)
    (fun j : ℕ => translate ((j : ℤ) • ω.v) ω.E)
    (fun _ _ => isSkew_translate _ h.1.1.1)
    (fun i _ j _ k hi hj => h.rowCopies_diagonal_overlap hW i j k hi hj)]
  simp only [interior_translate]

end SkewGluing.MarkedInner
