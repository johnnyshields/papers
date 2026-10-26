/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewGluing.Composition

/-!
# Affine laws for ordinary marked composition

The union and translation laws used to identify the literal chart in
`lem:subthreshold-transport` of `shields-2026-skew-class-inflation.tex`.
The nonempty hypotheses retain the composition's empty-outer convention.
Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing

/-- In case (a), the copy origin is an additive map of the outer cell coordinates. -/
theorem ordinary_origin_add (ω : MarkedInner) (hω : ω.case = .a)
    (D E : Diagram) (x y : ℤ × ℤ) :
    ω.origin D (x + y) = ω.origin E x + ω.origin E y := by
  simp only [MarkedInner.origin, hω, content_add, Prod.fst_add, add_zsmul]
  abel

/-- Ordinary composition distributes over a union of nonempty outer cell sets. -/
theorem ordinary_compose_union (ω : MarkedInner) (hω : ω.case = .a)
    (D E : Diagram) (hD : D.Nonempty) (hE : E.Nonempty) :
    ω.compose (D ∪ E) = ω.compose D ∪ ω.compose E := by
  have hm : ¬ ω.case.IsMixed := by rw [hω]; decide
  ext x
  simp only [MarkedInner.compose_of_ordinary (Finset.Nonempty.inl hD) hm,
    Finset.mem_union, MarkedInner.compose_of_ordinary hD hm,
    MarkedInner.compose_of_ordinary hE hm]
  have ho : ∀ d, ω.origin (D ∪ E) d = ω.origin D d ∧ ω.origin E d = ω.origin D d := by
    intro d
    simp only [MarkedInner.origin, hω, and_self]
  constructor
  · rintro ⟨d, hd | hd, hx⟩
    · exact Or.inl ⟨d, hd, by simpa only [(ho d).1] using hx⟩
    · exact Or.inr ⟨d, hd, by simpa only [(ho d).1, (ho d).2] using hx⟩
  · rintro (⟨d, hd, hx⟩ | ⟨d, hd, hx⟩)
    · exact ⟨d, Or.inl hd, by simpa only [(ho d).1] using hx⟩
    · exact ⟨d, Or.inr hd, by simpa only [(ho d).1, (ho d).2] using hx⟩

/-- Translating the outer translates its ordinary composite by the induced copy origin. -/
theorem ordinary_compose_translate (ω : MarkedInner) (hω : ω.case = .a)
    (D : Diagram) (hD : D.Nonempty) (v : ℤ × ℤ) :
    ω.compose (translate v D) = translate (ω.origin D v) (ω.compose D) := by
  have hm : ¬ ω.case.IsMixed := by rw [hω]; decide
  have ht : (translate v D).Nonempty := hD.image _
  ext x
  rw [MarkedInner.compose_of_ordinary ht hm, mem_translate,
    MarkedInner.compose_of_ordinary hD hm]
  constructor
  · rintro ⟨d, hd, hx⟩
    have hd' := mem_translate.mp hd
    refine ⟨d - v, hd', ?_⟩
    have ho : ω.origin (translate v D) d = ω.origin D (d - v) + ω.origin D v := by
      simpa only [sub_add_cancel] using ordinary_origin_add ω hω (translate v D) D (d - v) v
    rw [mem_translate] at hx ⊢
    rw [ho] at hx
    convert hx using 1
    abel
  · rintro ⟨d, hd, hx⟩
    refine ⟨d + v, ?_, ?_⟩
    · rw [mem_translate]
      simpa only [add_sub_cancel_right] using hd
    · rw [mem_translate] at hx ⊢
      rw [ordinary_origin_add ω hω (translate v D) D d v]
      convert hx using 1
      abel

end SkewClassInflation
