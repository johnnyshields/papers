/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.UnitCore

/-!
# A diagram is determined by its zero-free core and its common betas

Formalizes the first sentence of the final step of the unit case in `sc:positive-power` of
`shields-2026-skew-coframe-rigidity.tex`: if the original unit masks agree and the cores agree,
the original diagrams are equal.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity.UnitRestoration

/-- Two strictly antitone integer sequences on `Fin n` with the same range are equal. -/
theorem eq_of_strictAnti_range_eq {n : ℕ} {f g : Fin n → ℤ} (hf : StrictAnti f)
    (hg : StrictAnti g) (h : Set.range f = Set.range g) : f = g := by
  classical
  have hf' : StrictMono (f ∘ Fin.rev) := fun a b hab => hf (Fin.rev_strictAnti hab)
  have hg' : StrictMono (g ∘ Fin.rev) := fun a b hab => hg (Fin.rev_strictAnti hab)
  set s : Finset ℤ := Finset.univ.image f with hs
  have hcard : s.card = n := by
    rw [hs, Finset.card_image_of_injective _ hf.injective]; simp
  have hgs : ∀ x, g x ∈ s := by
    intro x
    have : g x ∈ Set.range f := h ▸ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := this
    simp [hs, ← hy]
  have e1 := Finset.orderEmbOfFin_unique hcard (f := f ∘ Fin.rev)
    (fun x => by simp [hs]) hf'
  have e2 := Finset.orderEmbOfFin_unique hcard (f := g ∘ Fin.rev)
    (fun x => hgs _) hg'
  funext x
  have := congrFun (e1.trans e2.symm) (Fin.rev x)
  simpa using this

theorem eq_of_core_and_units {n : ℕ} (D E : BetaDiagram n)
    (hrow : ∀ b : ℤ, (∃ i, i ∉ unitRows D.row D.col ∧ D.row i = b) ↔
      (∃ i, i ∉ unitRows E.row E.col ∧ E.row i = b))
    (hcol : ∀ b : ℤ, (∃ j, j ∉ unitCols D.row D.col ∧ D.col j = b) ↔
      (∃ j, j ∉ unitCols E.row E.col ∧ E.col j = b))
    (hunit : ∀ b : ℤ, (∃ i j, D.row i = b ∧ D.col j = b) ↔ (∃ i j, E.row i = b ∧ E.col j = b)) :
    D = E := by
  have key : ∀ (D E : BetaDiagram n) (b : ℤ), (∃ i, i ∉ unitRows D.row D.col ∧ D.row i = b) ∨
      (∃ i j, D.row i = b ∧ D.col j = b) ↔ b ∈ Set.range D.row := by
    intro D E b
    constructor
    · rintro (⟨i, -, h⟩ | ⟨i, j, h, -⟩)
      · exact ⟨i, h⟩
      · exact ⟨i, h⟩
    · rintro ⟨i, h⟩
      by_cases hi : i ∈ unitRows D.row D.col
      · obtain ⟨j, hj⟩ := hi
        exact Or.inr ⟨i, j, h, h ▸ hj.symm⟩
      · exact Or.inl ⟨i, hi, h⟩
  have key' : ∀ (D : BetaDiagram n) (b : ℤ), (∃ j, j ∉ unitCols D.row D.col ∧ D.col j = b) ∨
      (∃ i j, D.row i = b ∧ D.col j = b) ↔ b ∈ Set.range D.col := by
    intro D b
    constructor
    · rintro (⟨i, -, h⟩ | ⟨i, j, -, h⟩)
      · exact ⟨i, h⟩
      · exact ⟨j, h⟩
    · rintro ⟨j, h⟩
      by_cases hj : j ∈ unitCols D.row D.col
      · obtain ⟨i, hi⟩ := hj
        exact Or.inr ⟨i, j, hi.trans h, h⟩
      · exact Or.inl ⟨j, hj, h⟩
  have hr : D.row = E.row := by
    refine eq_of_strictAnti_range_eq D.row_strictAnti E.row_strictAnti (Set.ext fun b => ?_)
    rw [← key D E, ← key E D, hrow b, hunit b]
  have hc : D.col = E.col := by
    refine eq_of_strictAnti_range_eq D.col_strictAnti E.col_strictAnti (Set.ext fun b => ?_)
    rw [← key' D, ← key' E, hcol b, hunit b]
  cases D; cases E; simp_all

end SkewCoframeRigidity.UnitCase
