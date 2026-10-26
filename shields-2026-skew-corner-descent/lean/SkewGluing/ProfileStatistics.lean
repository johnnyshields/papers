/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.ProfileGeometry
import SkewGluing.RowInvariants

/-!
# Profile row count and content span

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `lem:cofactor`, `eq:outer-statistics`). The top generator index and row
sign in the determinant are the actual geometric content span and row count. Sorry-free.
-/

namespace SkewGluing
namespace Profile
variable {n : ℕ}

/-- All normalized profile contents lie between zero and the top beta index minus one. -/
theorem content_bounds_cells (P : Profile n) {x : ℤ × ℤ} (hx : x ∈ P.cells) :
    0 ≤ content x ∧ content x < P.xi 0 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨i, rfl, hlo, hhi⟩ := mem_cells.mp hx
  have hz := P.zeta_nonneg i
  have hxi := P.xi_strictAnti.antitone (Fin.zero_le i)
  simp only [content]
  omega

/-- The last row's left endpoint has content zero. -/
theorem minContent_cells (P : Profile n) : minContent P.cells = 0 := by
  apply minContent_eq_of
  · have h := content_mem_contents (P.row_left_mem_cells (Fin.last n))
    simpa only [content, add_sub_cancel_right, P.zeta_last] using h
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact (P.content_bounds_cells hx).1

/-- The first row's right endpoint realizes the greatest content. -/
theorem maxContent_cells (P : Profile n) : maxContent P.cells = P.xi 0 - 1 := by
  apply maxContent_eq_of
  · have h := content_mem_contents (P.row_right_mem_cells 0)
    simpa only [content, Fin.val_zero, Nat.cast_zero, add_zero, sub_zero] using h
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    have := (P.content_bounds_cells hx).2
    omega

/-- The profile's top variable is the number of occupied geometric contents. -/
theorem span_cells_eq_topVar (P : Profile n) : span P.cells = (P.topVar : ℕ) := by
  have h := span_eq_of_isConnectedSkew P.isConnectedSkew_cells
  rw [P.minContent_cells, P.maxContent_cells] at h
  have ht := P.topVar_coe
  omega

/-- Every indexed profile row occurs, and no additional row occurs. -/
theorem rows_cells (P : Profile n) :
    P.cells.image Prod.fst = Finset.univ.image (fun i : Fin (n + 1) => (i : ℤ)) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    obtain ⟨i, hi, _⟩ := mem_cells.mp hx
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, P.row_left_mem_cells i, rfl⟩

/-- A profile with `n + 1` rows has that actual geometric row count. -/
theorem rowCount_cells (P : Profile n) : (P.cells.image Prod.fst).card = n + 1 := by
  rw [P.rows_cells, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    change ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) at hij
    apply Fin.ext
    exact_mod_cast hij

end Profile

/-- Translation preserves the actual number of occupied rows. -/
theorem rowCount_translate (D : Diagram) (v : ℤ × ℤ) :
    ((translate v D).image Prod.fst).card = (D.image Prod.fst).card := by
  have he : (translate v D).image Prod.fst =
      (D.image Prod.fst).image (fun a => a + v.1) := by
    simp only [translate, Finset.image_image]
    rfl
  rw [he, Finset.card_image_of_injective _ (add_left_injective _)]

end SkewGluing
