/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.EmptyHorizontal
import SkewGluing.ProfileStatistics

/-!
# Literal empty line copies and their original area

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Distinct outer contents place whole inner copies in disjoint content bands.
Translation acts on the actual cell union. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing
open scoped BigOperators

/-- Translation preserves every actual cell, hence the area. -/
theorem original_card_translate (v : ℤ × ℤ) (E : Diagram) :
    (translate v E).card = E.card := by
  rw [SkewGluing.translate, Finset.card_image_of_injective _ (add_left_injective v)]

/-- Empty attachment has no supplemental copy or deleted original cell. -/
theorem empty_compose_eq_union (E D : Diagram) (hD : D.Nonempty) :
    (emptyMarkH E).compose D =
      D.biUnion (fun d => translate ((emptyMarkH E).origin D d) E) := by
  simp [MarkedInner.compose, emptyMarkH, MarkedInner.SameRibbon, MarkedInner.upper,
    SkewGluing.translate, hD.ne_empty]

/-- The actual empty displacement is independent of the inner's translation. -/
theorem original_vH_translate (E : Diagram) (hE : E.Nonempty) (v : ℤ × ℤ) :
    vH (translate v E) = vH E := by
  unfold vH
  rw [ne_translate hE, sw_translate hE]
  abel

/-- Whole empty-copy compositions transport by exactly the inner translation. -/
theorem empty_compose_translate (E D : Diagram) (hE : E.Nonempty) (v : ℤ × ℤ) :
    (emptyMarkH (translate v E)).compose D = translate v ((emptyMarkH E).compose D) := by
  classical
  by_cases hD : D.Nonempty
  · rw [empty_compose_eq_union _ _ hD, empty_compose_eq_union _ _ hD]
    have ho (d) : (emptyMarkH (translate v E)).origin D d = (emptyMarkH E).origin D d := by
      simp [MarkedInner.origin, emptyMarkH, original_vH_translate E hE v]
    simp_rw [ho, translate_translate]
    ext x
    simp only [Finset.mem_biUnion, mem_translate]
    constructor
    · rintro ⟨d, hd, hx⟩
      refine ⟨d, hd, ?_⟩
      have he : x - (emptyMarkH E).origin D d - v = x - v - (emptyMarkH E).origin D d := by
        abel
      simpa only [sub_add_eq_sub_sub, he] using hx
    · rintro ⟨d, hd, hx⟩
      refine ⟨d, hd, ?_⟩
      have he : x - (emptyMarkH E).origin D d - v = x - v - (emptyMarkH E).origin D d := by
        abel
      simpa only [sub_add_eq_sub_sub, he] using hx
  · have hz : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    subst D
    simp [MarkedInner.compose, emptyMarkH, SkewGluing.translate]

/-- Distinct outer contents retain disjoint complete original copy bands. -/
theorem empty_compose_card (E : Diagram) (hE : IsConnectedSkew E)
    (D : Diagram) (hD : D.Nonempty) (hinj : Set.InjOn content (D : Set (ℤ × ℤ))) :
    ((emptyMarkH E).compose D).card = D.card * E.card := by
  have hperiod : (emptyMarkH E).period = (span E : ℤ) := by
    have hs := (emptyMarkH_isLegal hE).1.span_eq
    have hw : (emptyMarkH E).width = 0 := by simp [MarkedInner.width, emptyMarkH, span, contents]
    simp only [hw, Nat.cast_zero, add_zero] at hs
    exact hs.symm
  have hspan := span_eq_of_isConnectedSkew hE
  have hpos : 0 < (span E : ℤ) := by
    have hn : 0 < span E := Finset.card_pos.mpr (hE.2.1.image content)
    exact_mod_cast hn
  rw [empty_compose_eq_union E D hD, Finset.card_biUnion]
  · simp [original_card_translate]
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    have hca := (emptyMarkH E).content_origin D a
    have hcb := (emptyMarkH E).content_origin D b
    rw [hperiod] at hca hcb
    have hxa' := mem_translate.mp hxa
    have hxb' := mem_translate.mp hxb
    have haC : content (x - (emptyMarkH E).origin D a) ∈ contents E :=
      Finset.mem_image.mpr ⟨_, hxa', rfl⟩
    have hbC : content (x - (emptyMarkH E).origin D b) ∈ contents E :=
      Finset.mem_image.mpr ⟨_, hxb', rfl⟩
    have haLo := minContent_le haC
    have haHi := le_maxContent haC
    have hbLo := minContent_le hbC
    have hbHi := le_maxContent hbC
    simp only [MarkedInner.content_sub, hca, hcb] at haLo haHi hbLo hbHi
    have hcne : content a ≠ content b := fun he => hab (hinj ha hb he)
    rcases lt_or_gt_of_ne hcne with h | h
    · have hh : content a + 1 ≤ content b := by omega
      nlinarith
    · have hh : content b + 1 ≤ content a := by omega
      nlinarith

end SkewCornerDescent
