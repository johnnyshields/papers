/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.ProfileGeometry
import SkewGluing.InteriorBounds

/-!
# The geometric shape of the deleted profile minor

Formalizes `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:minor-shape`).  Deleting the top beta row and last beta column gives exactly
the southeast interior's row intervals, with zero-length rows retained as empty intervals.
Identifying its determinant with the product of the interior-component Schur functions is a
separate obligation.

Sorry-free.
-/

namespace SkewGluing
namespace Profile
variable {n : ℕ}

/-- The cell diagram represented by the complementary beta lists, allowing empty rows. -/
def minorCells (P : Profile n) : Diagram :=
  Finset.univ.biUnion fun i : Fin n =>
    (Finset.Ico (P.zeta i.castSucc + i) (P.xi i.succ + i)).image fun b => ((i : ℤ), b)

/-- The row intervals of the southeast interior are the complementary beta intervals. -/
theorem mem_interior_cells (P : Profile n) (a b : ℤ) :
    (a, b) ∈ diagramInterior P.cells ↔ ∃ i : Fin n, (i : ℤ) = a ∧
      P.zeta i.castSucc + i ≤ b ∧ b < P.xi i.succ + i := by
  rw [diagramInterior, Finset.mem_filter]
  change ((a, b) ∈ P.cells ∧ (a + 1, b + 1) ∈ P.cells) ↔ _
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨i, hi, hlo, hhi⟩ := mem_cells.mp h0
    obtain ⟨j, hj, hlo', hhi'⟩ := mem_cells.mp h1
    have hin : (i : ℕ) < n := by have := j.isLt; omega
    let k : Fin n := ⟨i, hin⟩
    have hkc : k.castSucc = i := Fin.ext rfl
    have hks : k.succ = j := Fin.ext (by change (i : ℕ) + 1 = (j : ℕ); omega)
    refine ⟨k, hi, ?_, ?_⟩
    · simpa only [hkc] using hlo
    · rw [hks]
      change b < P.xi j + (i : ℤ)
      omega
  · rintro ⟨i, rfl, hlo, hhi⟩
    have hx := P.xi_add_antitone (Fin.castSucc_le_succ i)
    have hz := P.zeta_add_antitone (Fin.castSucc_le_succ i)
    dsimp only at hx hz
    have his : ((i.succ : ℕ) : ℤ) = (i : ℤ) + 1 := by simp
    constructor
    · change (((i.castSucc : ℕ) : ℤ), b) ∈ P.cells
      rw [mem_cells_fin]
      simp only [Fin.val_castSucc] at hx hz ⊢
      omega
    · rw [← his, mem_cells_fin]
      simp only [Fin.val_castSucc] at hx hz
      omega

/-- The deleted-minor shape is the actual southeast interior, including empty rows. -/
theorem interior_cells_eq_minorCells (P : Profile n) :
    diagramInterior P.cells = P.minorCells := by
  ext ⟨a, b⟩
  rw [mem_interior_cells]
  simp only [minorCells, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨i, rfl, h⟩
    exact ⟨i, b, h, rfl, rfl⟩
  · rintro ⟨i, j, h, rfl, rfl⟩
    exact ⟨i, rfl, h⟩

end Profile

/-- Southeast interiors commute with translation. -/
theorem interior_translate (D : Diagram) (v : ℤ × ℤ) :
    diagramInterior (translate v D) = translate v (diagramInterior D) := by
  ext x
  simp only [diagramInterior, Finset.mem_filter, mem_translate]
  rw [show x + eCell - v = x - v + eCell by abel]

/-- The geometric minor-shape identification for every connected diagram presentation. -/
theorem interior_eq_translate_minorCells {D : Diagram} {n : ℕ} (P : Profile n)
    (v : ℤ × ℤ) (h : D = translate v P.cells) :
    diagramInterior D = translate v P.minorCells := by
  rw [h, interior_translate, Profile.interior_cells_eq_minorCells]

end SkewGluing
