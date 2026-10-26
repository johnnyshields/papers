/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/EsDiff/Step.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.EsDiff.Relative

/-!
# Removing the key ribbon of one cell

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Lemma 5.4.3
(`OlsonHarris2024HopfApplications`) for one cell.

For a cell `b` of a skew diagram `X` with no cell of `X` to its northwest and a legal mark of
case (a), the union of the copies at the cells of `X` is the union of the copies at the cells of
`X \ b` and the copy at `b`; removing the key ribbon of `b` leaves the copies at `X \ b` together
with the cells of `E` at `b` lying in the pieces of the missing neighbors (`step_sdiff`), which
touch none of the other copies (`step_nonAdjacent`) and have Schur function
`s_W^{[no east]} s_{\overline W}^{[no south]} s_{\overline O}^{[no southeast]}`
(`cellSchur_absent`).

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

namespace EsDiff

open scoped Classical

open SkewMarkedFactor.Gluing.MarkedInner

variable {ω : MarkedInner} {X : Diagram} {b : ℤ × ℤ}

theorem mem_copies_org (hc : ω.case = .a) {D : Diagram} {z : ℤ × ℤ} :
    z ∈ Plan.MarkedInner.copies ω D ↔ ∃ d ∈ D, z ∈ translate (org ω d) ω.E := by
  rw [Plan.MarkedInner.mem_copies]
  simp only [origin_eq hc]

/-- The cells of the pieces of `E` whose neighbor, east, south or southeast of `b`, is missing
from `X`, as a union of the three pieces. -/
noncomputable def absentCells (ω : MarkedInner) (X : Diagram) (b : ℤ × ℤ) : Diagram :=
  ((if (b.1 + 1, b.2) ∈ X then ∅ else pieceS ω) ∪
      (if (b.1 + 1, b.2 + 1) ∈ X then ∅ else pieceSE ω)) ∪
    (if (b.1, b.2 + 1) ∈ X then ∅ else pieceE ω)

theorem mem_absentCells {z : ℤ × ℤ} : z ∈ absentCells ω X b ↔ AbsentPiece ω X b z := by
  unfold absentCells AbsentPiece
  by_cases h1 : (b.1 + 1, b.2) ∈ X <;> by_cases h2 : (b.1 + 1, b.2 + 1) ∈ X <;>
    by_cases h3 : (b.1, b.2 + 1) ∈ X <;> simp [h1, h2, h3] <;> tauto

theorem copies_insert (hc : ω.case = .a) (hb : b ∈ X) :
    Plan.MarkedInner.copies ω X =
      Plan.MarkedInner.copies ω (X.erase b) ∪ translate (org ω b) ω.E := by
  ext z
  rw [Finset.mem_union, mem_copies_org hc, mem_copies_org hc]
  constructor
  · rintro ⟨d, hd, hz⟩
    by_cases hdb : d = b
    · subst hdb; exact Or.inr hz
    · exact Or.inl ⟨d, Finset.mem_erase.mpr ⟨hdb, hd⟩, hz⟩
  · rintro (⟨d, hd, hz⟩ | hz)
    · exact ⟨d, (Finset.mem_erase.mp hd).2, hz⟩
    · exact ⟨b, hb, hz⟩

/-- **Removing the key ribbon at `b` from the union of the copies leaves the copies at `X \ b`
and the pieces of the missing neighbors.** -/
theorem step_sdiff (hω : ω.IsLegal) (hc : ω.case = .a) (hX : IsSkew X) (hb : b ∈ X)
    (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) :
    (translate (org ω b) ω.E \ translate (org ω b) (keyRibbon ω)) \
      Plan.MarkedInner.copies ω (X.erase b) = translate (org ω b) (absentCells ω X b) := by
  have hL := edgeLocal hω hc
  ext z
  rw [Finset.mem_sdiff, Finset.mem_sdiff, mem_translate, mem_translate, mem_translate,
    mem_copies_org hc, mem_absentCells]
  simp only [mem_translate_org (b := b)]
  have key := fun hzE hzK => not_covered_iff hω hL hX hb hmin (z := z - org ω b) hzE hzK
  constructor
  · rintro ⟨⟨hzE, hzK⟩, hzC⟩
    refine (key hzE hzK).mp fun d hd hmem => hzC ⟨d, hd, hmem⟩
  · intro hab
    have hzE : z - org ω b ∈ ω.E := by
      rcases hab with ⟨hP, -⟩ | ⟨hP, -⟩ | ⟨hP, -⟩
      · exact hL.pieceE_sub _ hP
      · exact hL.pieceS_sub _ hP
      · exact hL.pieceSE_sub _ hP
    have hzK : z - org ω b ∉ keyRibbon ω := by
      intro hk
      have := hL.key_disj _ hk
      rcases hab with ⟨hP, -⟩ | ⟨hP, -⟩ | ⟨hP, -⟩
      · exact this.1 hP
      · exact this.2.1 hP
      · exact this.2.2 hP
    refine ⟨⟨hzE, hzK⟩, fun ⟨d, hd, hmem⟩ => ?_⟩
    exact (key hzE hzK).mpr hab d hd hmem

/-- The key ribbon of `b` meets no other copy. -/
theorem step_key_disjoint (hω : ω.IsLegal) (hc : ω.case = .a) (hX : IsSkew X) (hb : b ∈ X)
    (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) :
    Disjoint (translate (org ω b) (keyRibbon ω)) (Plan.MarkedInner.copies ω (X.erase b)) := by
  have hL := edgeLocal hω hc
  rw [Finset.disjoint_left]
  intro z hzK hzC
  rw [mem_translate] at hzK
  obtain ⟨d, hd, hmem⟩ := (mem_copies_org hc).mp hzC
  rw [mem_translate_org (b := b)] at hmem
  exact key_avoid hω hL hX hb hmin hzK d hd hmem

/-- No cell of the pieces of the missing neighbors touches another copy. -/
theorem step_nonAdjacent (hω : ω.IsLegal) (hc : ω.case = .a) (hX : IsSkew X) (hb : b ∈ X)
    (hmin : ∀ x ∈ X, x.1 ≤ b.1 → x.2 ≤ b.2 → x = b) :
    NonAdjacent (translate (org ω b) (absentCells ω X b))
      (Plan.MarkedInner.copies ω (X.erase b)) := by
  have hL := edgeLocal hω hc
  intro x hx y hy hadj
  rw [mem_translate, mem_absentCells] at hx
  obtain ⟨d, hd, hmem⟩ := (mem_copies_org hc).mp hy
  rw [mem_translate_org (b := b)] at hmem
  exact not_adjacent hω hL hX hb hmin hx hd hmem (cellAdj_sub (org ω b) hadj)

end EsDiff

end Plan

end SkewMarkedFactor.Gluing
