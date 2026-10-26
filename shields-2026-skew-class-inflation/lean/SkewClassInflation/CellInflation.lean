/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CellProfiles
import SkewGluing.Composition

/-!
# Inflation on cells and its distribution over marked composition

Formalizes the cell-level part of `lem:inflate-chart` in
`shields-2026-skew-class-inflation.tex`.  Inflation extends every row of a diagram by one
cell to the east, so on cells it is \(D\mapsto D\cup(D+(0,1))\).  It is the cell realization of
profile inflation, it distributes over unions and translations, and therefore over the full copy
union of a marked composition, supplemental copies included, when the displacement and the
attachment case are kept.  The legality of the inflated mark is not part of this module.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative
open SkewGluing (Diagram MarkedInner IsConnectedSkew)

/-- One-step inflation on cells: every row gains one cell on its east end. -/
def inflateCells (D : Diagram) : Diagram := D ∪ SkewGluing.translate (0, 1) D

theorem inflateCells_empty : inflateCells ∅ = ∅ := by
  simp [inflateCells, SkewGluing.translate]

theorem inflateCells_union (A B : Diagram) :
    inflateCells (A ∪ B) = inflateCells A ∪ inflateCells B := by
  unfold inflateCells SkewGluing.translate
  rw [Finset.image_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem inflateCells_translate (v : ℤ × ℤ) (D : Diagram) :
    inflateCells (SkewGluing.translate v D) = SkewGluing.translate v (inflateCells D) := by
  unfold inflateCells SkewGluing.translate
  rw [Finset.image_union, Finset.image_image, Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro x _
  simp only [Function.comp]
  exact add_right_comm _ _ _

theorem inflateCells_biUnion {ι : Type*} (s : Finset ι) (f : ι → Diagram) :
    inflateCells (s.biUnion f) = s.biUnion fun i => inflateCells (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inflateCells_empty]
  | insert a s ha ih => rw [Finset.biUnion_insert, inflateCells_union, ih, Finset.biUnion_insert]

/-- Cell inflation of a profile diagram is the diagram of the inflated profile. -/
theorem inflateCells_profileCells {n : ℕ} (P : Profile n) :
    inflateCells (profileCells P) = profileCells (Profile.inflate 1 P) := by
  ext ⟨a, b⟩
  unfold inflateCells
  rw [Finset.mem_union, mem_profileCells, mem_profileCells]
  simp only [SkewGluing.translate, Finset.mem_image, Prod.exists, mem_profileCells, Profile.xi_inflate,
    Profile.zeta_inflate, Prod.mk_add_mk, Prod.mk.injEq]
  constructor
  · rintro (⟨i, hi, h1, h2⟩ | ⟨a', b', ⟨i, hi, h1, h2⟩, rfl, rfl⟩)
    · exact ⟨i, hi, h1, by push_cast; omega⟩
    · exact ⟨i, by omega, by omega, by push_cast; omega⟩
  · rintro ⟨i, hi, h1, h2⟩
    by_cases hb : b < P.xi i + i.val
    · exact Or.inl ⟨i, hi, h1, hb⟩
    · refine Or.inr ⟨a, b - 1, ⟨i, hi, ?_, ?_⟩, by omega, by omega⟩
      · have := P.r_pos i
        have := P.xi_sub_zeta i
        omega
      · push_cast at h2; omega

/-- The cell inflation of a connected diagram is a connected skew diagram. -/
theorem isConnectedSkew_inflateCells_profileCells {n : ℕ} (P : Profile n) :
    IsConnectedSkew (inflateCells (profileCells P)) := by
  rw [inflateCells_profileCells]
  exact profileCells_connected _


/-- Inflate the inner and the mark, keeping the displacement and the attachment case. -/
def inflateMarked (ω : MarkedInner) : MarkedInner where
  E := inflateCells ω.E
  W := inflateCells ω.W
  v := ω.v
  case := ω.case

theorem origin_inflateMarked (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) :
    (inflateMarked ω).origin D d = ω.origin D d := rfl

theorem sameRibbon_inflateMarked (ω : MarkedInner) (D : Diagram) (d : ℤ × ℤ) :
    (inflateMarked ω).SameRibbon D d ↔ ω.SameRibbon D d := Iff.rfl

theorem upper_inflateMarked (ω : MarkedInner) :
    (inflateMarked ω).upper = inflateCells ω.upper := by
  unfold SkewGluing.MarkedInner.upper inflateMarked
  exact (inflateCells_translate _ _).symm

theorem supplementalShift_inflateMarked (ω : MarkedInner) :
    (inflateMarked ω).supplementalShift = ω.supplementalShift := rfl

/-- Inflation of the complete marked composition, supplemental copies included, is the
composition with the inflated inner and mark. -/
theorem compose_inflateMarked (ω : MarkedInner) (D : Diagram) (hD : D.Nonempty) :
    (inflateMarked ω).compose D = inflateCells (ω.compose D) := by
  have hne : D ≠ ∅ := hD.ne_empty
  unfold SkewGluing.MarkedInner.compose
  simp only [hne, ↓reduceIte]
  rw [inflateCells_union, inflateCells_biUnion, inflateCells_biUnion]
  congr 1
  · apply Finset.biUnion_congr rfl
    intro d _
    rw [inflateCells_translate]
    rfl
  · apply Finset.biUnion_congr rfl
    intro d _
    rw [inflateCells_translate, upper_inflateMarked]
    rfl

/-- The empty outer convention is compatible with inflation of the mark. -/
theorem compose_empty_inflateMarked (ω : MarkedInner) :
    (inflateMarked ω).compose ∅ = inflateCells (ω.compose ∅) := by
  simp [SkewGluing.MarkedInner.compose, inflateMarked]



end SkewClassInflation
