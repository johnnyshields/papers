/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/Counts.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase.Pieces

/-!
# Counting cells of a skew diagram without a neighbor

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.4 (`OlsonHarris2024HopfApplications`), proof of
Lemma 5.4.6.  For a skew diagram `X`, `|X| - row X` is the number of cells with a cell of `X` to
the east, `|X| - col X` the number with a cell to the south and `|X| - dia X` the number with a
cell to the southeast.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace SkewMarkedFactor.Gluing

namespace Plan

open scoped Classical

/-- The number of cells of `X` with a cell of `X` to the east. -/
def countE (X : Diagram) : ℕ := (X.filter fun x => x + (0, 1) ∈ X).card

/-- The number of cells of `X` with a cell of `X` to the south. -/
def countS (X : Diagram) : ℕ := (X.filter fun x => x + (1, 0) ∈ X).card

/-- The number of cells of `X` with a cell of `X` to the southeast. -/
def countSE (X : Diagram) : ℕ := (X.filter fun x => x + eCell ∈ X).card

theorem card_filter_not_succ {X : Diagram} (f : ℤ × ℤ → ℤ) (u : ℤ × ℤ)
    (hinj : ∀ x ∈ X, ∀ y ∈ X, f x = f y → x = y ∨ x + u ∈ X ∨ y + u ∈ X)
    (hsurj : ∀ x ∈ X, ∃ y ∈ X, f y = f x ∧ y + u ∉ X) :
    (X.filter fun x => x + u ∉ X).card = (X.image f).card := by
  have himg : (X.filter fun x => x + u ∉ X).image f = X.image f := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨hx, -⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hfy, hyu⟩ := hsurj x hx
      exact ⟨y, ⟨hy, hyu⟩, hfy⟩
  rw [← himg]
  refine (Finset.card_image_of_injOn ?_).symm
  intro x hx y hy hxy
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
  rcases hinj x hx.1 y hy.1 hxy with h | h | h
  · exact h
  · exact absurd h hx.2
  · exact absurd h hy.2

theorem card_eq_numRows_add_countE {X : Diagram} (hX : IsSkew X) :
    X.card = numRows X + countE X := by
  have h := Finset.card_filter_add_card_filter_not (s := X) (fun x => x + (0, 1) ∈ X)
  have h2 : (X.filter fun x => x + (0, 1) ∉ X).card = numRows X := by
    refine (card_filter_not_succ (X := X) Prod.fst (0, 1) ?_ ?_).trans rfl
    · intro x hx y hy hxy
      obtain ⟨a, b⟩ := x
      obtain ⟨a', b'⟩ := y
      simp only at hxy
      subst hxy
      rcases lt_trichotomy b b' with h | h | h
      · right; left
        have := hX.mem (i := a) (j := b + 1) hx hy le_rfl h.le le_rfl le_rfl (by omega) (by omega)
        simpa using this
      · left; rw [h]
      · right; right
        have := hX.mem (i := a) (j := b' + 1) hy hx le_rfl h.le le_rfl le_rfl (by omega) (by omega)
        simpa using this
    · intro x hx
      obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (X.filter fun z => z.1 = x.1) Prod.snd
        ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      obtain ⟨hyX, hy1⟩ := Finset.mem_filter.mp hy
      refine ⟨y, hyX, hy1, fun hmem => ?_⟩
      have := hmax (y + (0, 1)) (Finset.mem_filter.mpr ⟨hmem, by simpa using hy1⟩)
      simp at this
  unfold countE
  omega

theorem card_eq_numCols_add_countS {X : Diagram} (hX : IsSkew X) :
    X.card = numCols X + countS X := by
  have h := Finset.card_filter_add_card_filter_not (s := X) (fun x => x + (1, 0) ∈ X)
  have h2 : (X.filter fun x => x + (1, 0) ∉ X).card = numCols X := by
    rw [numCols_eq_card_image_snd]
    refine card_filter_not_succ (X := X) Prod.snd (1, 0) ?_ ?_
    · intro x hx y hy hxy
      obtain ⟨a, b⟩ := x
      obtain ⟨a', b'⟩ := y
      simp only at hxy
      subst hxy
      rcases lt_trichotomy a a' with h | h | h
      · right; left
        have := hX.mem (i := a + 1) (j := b) hx hy h.le le_rfl (by omega) (by omega) le_rfl le_rfl
        simpa using this
      · left; rw [h]
      · right; right
        have := hX.mem (i := a' + 1) (j := b) hy hx h.le le_rfl (by omega) (by omega) le_rfl le_rfl
        simpa using this
    · intro x hx
      obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (X.filter fun z => z.2 = x.2) Prod.fst
        ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      obtain ⟨hyX, hy1⟩ := Finset.mem_filter.mp hy
      refine ⟨y, hyX, hy1, fun hmem => ?_⟩
      have := hmax (y + (1, 0)) (Finset.mem_filter.mpr ⟨hmem, by simpa using hy1⟩)
      simp at this
  unfold countS
  omega

theorem card_eq_span_add_countSE {X : Diagram} (hX : IsSkew X) :
    X.card = span X + countSE X := by
  have h := Finset.card_filter_add_card_filter_not (s := X) (fun x => x + eCell ∈ X)
  have h2 : (X.filter fun x => x + eCell ∉ X).card = span X := by
    refine card_filter_not_succ (X := X) content eCell ?_ ?_
    · intro x hx y hy hxy
      obtain ⟨a, b⟩ := x
      obtain ⟨a', b'⟩ := y
      simp only [content] at hxy
      rcases lt_trichotomy a a' with h | h | h
      · right; left
        have := hX.mem (i := a + 1) (j := b + 1) hx hy h.le (by omega) (by omega) (by omega)
          (by omega) (by omega)
        simpa [eCell] using this
      · left
        have : b = b' := by omega
        rw [h, this]
      · right; right
        have := hX.mem (i := a' + 1) (j := b' + 1) hy hx h.le (by omega) (by omega) (by omega)
          (by omega) (by omega)
        simpa [eCell] using this
    · intro x hx
      obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (X.filter fun z => content z = content x)
        Prod.fst ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      obtain ⟨hyX, hy1⟩ := Finset.mem_filter.mp hy
      refine ⟨y, hyX, hy1, fun hmem => ?_⟩
      have := hmax (y + eCell) (Finset.mem_filter.mpr ⟨hmem, by
        rw [MarkedInner.content_eCell_add]; exact hy1⟩)
      simp [eCell] at this
  unfold countSE
  have : span X = (X.image content).card := rfl
  omega

end Plan

end SkewMarkedFactor.Gluing
