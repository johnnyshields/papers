/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.ProfileCells

/-!
# Uniqueness of a diagram's profile

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:jt`).  Normalized profile cell diagrams determine both row lengths and overlaps.
This identifies the profile Jacobi--Trudi value independently of the chosen presentation.

Sorry-free.
-/

namespace SkewGluing
namespace Profile

variable {n m : ℕ}

theorem row_bounds_of_mem_cells (P : Profile n) {a b : ℤ} (h : (a, b) ∈ P.cells) :
    0 ≤ a ∧ a ≤ n := by
  obtain ⟨i, rfl, _⟩ := mem_cells.mp h
  have := i.isLt
  omega

theorem row_left_mem_cells (P : Profile n) (i : Fin (n + 1)) :
    ((i : ℤ), P.zeta i + i) ∈ P.cells := by
  rw [mem_cells_fin]
  have := P.xi_sub_zeta i
  have := P.r_pos i
  omega

theorem row_right_mem_cells (P : Profile n) (i : Fin (n + 1)) :
    ((i : ℤ), P.xi i + i - 1) ∈ P.cells := by
  rw [mem_cells_fin]
  have := P.xi_sub_zeta i
  have := P.r_pos i
  omega

/-- Normalized cell diagrams recover the beta lists and hence the profile. -/
theorem cells_injective {P Q : Profile n} (h : P.cells = Q.cells) : P = Q := by
  have hz : P.zeta = Q.zeta := by
    funext i
    have hp := P.row_left_mem_cells i
    have hq := Q.row_left_mem_cells i
    rw [h, mem_cells_fin] at hp
    rw [← h, mem_cells_fin] at hq
    omega
  have hx : P.xi = Q.xi := by
    funext i
    have hp := P.row_right_mem_cells i
    have hq := Q.row_right_mem_cells i
    rw [h, mem_cells_fin] at hp
    rw [← h, mem_cells_fin] at hq
    omega
  apply Profile.ext
  · funext i
    have hp := P.xi_sub_zeta i
    have hq := Q.xi_sub_zeta i
    rw [hx, hz] at hp
    omega
  · funext j
    have hp := P.xi_succ_sub_zeta_castSucc j
    have hq := Q.xi_succ_sub_zeta_castSucc j
    rw [hx, hz] at hp
    omega

/-- A translated profile diagram has precisely the rows from `v.1` to `v.1 + n`. -/
theorem translated_row_bounds (P : Profile n) (v : ℤ × ℤ) {x : ℤ × ℤ}
    (h : x ∈ translate v P.cells) : v.1 ≤ x.1 ∧ x.1 ≤ v.1 + n := by
  have hb := P.row_bounds_of_mem_cells (mem_translate.mp h)
  omega

theorem translated_row_left_mem (P : Profile n) (v : ℤ × ℤ) (i : Fin (n + 1)) :
    ((i : ℤ) + v.1, P.zeta i + i + v.2) ∈ translate v P.cells := by
  rw [mem_translate]
  change ((i : ℤ) + v.1 - v.1, P.zeta i + i + v.2 - v.2) ∈ P.cells
  simpa only [add_sub_cancel_right] using P.row_left_mem_cells i

/-- Every profile presentation of a diagram has the same row count and translation. -/
theorem presentation_coordinates {P : Profile n} {Q : Profile m} {v w : ℤ × ℤ}
    (h : translate v P.cells = translate w Q.cells) : n = m ∧ v = w := by
  have hp0 := P.translated_row_left_mem v 0
  have hq0 := Q.translated_row_left_mem w 0
  rw [h] at hp0
  rw [← h] at hq0
  have bp0 := Q.translated_row_bounds w hp0
  have bq0 := P.translated_row_bounds v hq0
  simp only [Fin.val_zero, Int.natCast_zero, zero_add] at bp0 bq0
  have hv : v.1 = w.1 := by omega
  have hpn := P.translated_row_left_mem v (Fin.last n)
  have hqm := Q.translated_row_left_mem w (Fin.last m)
  rw [h] at hpn
  rw [← h] at hqm
  have bpn := Q.translated_row_bounds w hpn
  have bqm := P.translated_row_bounds v hqm
  simp only [Fin.val_last] at bpn bqm
  have hnm : n = m := by omega
  subst m
  have hpl := P.translated_row_left_mem v (Fin.last n)
  have hql := Q.translated_row_left_mem w (Fin.last n)
  rw [h, mem_translate] at hpl
  rw [← h, mem_translate] at hql
  simp only [Fin.val_last, zeta_last, zero_add] at hpl hql
  change ((n : ℤ) + v.1 - w.1, (n : ℤ) + v.2 - w.2) ∈ Q.cells at hpl
  change ((n : ℤ) + w.1 - v.1, (n : ℤ) + w.2 - v.2) ∈ P.cells at hql
  have erow : (n : ℤ) + v.1 - w.1 = (n : ℤ) := by omega
  have erow' : (n : ℤ) + w.1 - v.1 = (n : ℤ) := by omega
  rw [erow, ← show ((Fin.last n : Fin (n + 1)) : ℤ) = (n : ℤ) by rfl,
    mem_cells_fin] at hpl
  rw [erow', ← show ((Fin.last n : Fin (n + 1)) : ℤ) = (n : ℤ) by rfl,
    mem_cells_fin] at hql
  simp only [zeta_last, Fin.val_last, zero_add] at hpl hql
  exact ⟨rfl, Prod.ext hv (by omega)⟩

/-- Equal translates have equal profiles, including their dependent row index. -/
theorem presentation_unique {P : Profile n} {Q : Profile m} {v w : ℤ × ℤ}
    (h : translate v P.cells = translate w Q.cells) : HEq P Q := by
  obtain ⟨hnm, hvw⟩ := presentation_coordinates h
  subst m
  subst w
  exact heq_of_eq (cells_injective (translate_injective v h))

/-- The dependent profile itself is unique, not just its row count. -/
theorem presentation_sigma_unique {P : Profile n} {Q : Profile m} {v w : ℤ × ℤ}
    (h : translate v P.cells = translate w Q.cells) :
    (⟨n, P⟩ : Σ k, Profile k) = ⟨m, Q⟩ := by
  obtain ⟨hnm, hvw⟩ := presentation_coordinates h
  subst m
  subst w
  have hpq := cells_injective (translate_injective v h)
  subst Q
  rfl

end Profile
end SkewGluing
