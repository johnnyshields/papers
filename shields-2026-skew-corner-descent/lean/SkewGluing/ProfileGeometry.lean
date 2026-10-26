/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewGluing.ProfileInvariant
import SkewGluing.SkewComponents

/-!
# Geometry of normalized profile diagrams

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `eq:jt`, `eq:minor-shape`).  Each valid profile realizes a connected skew diagram.

TODO-COPIED: the skew-convexity and row-connectivity arguments are adapted from
`skew-factor-gluing/lean/SkewGluing/CellProfile.lean`.

Sorry-free.
-/

namespace SkewGluing

/-- Cells sharing a row of a skew diagram are joined within that row. -/
theorem IsSkew.reach_row {D : Diagram} (hs : IsSkew D) {a b c : ℤ}
    (hb : (a, b) ∈ D) (hc : (a, c) ∈ D) : DiagReach D (a, b) (a, c) := by
  rcases le_total b c with h | h
  · exact hs.reach_of_le hb hc le_rfl h
  · exact (hs.reach_of_le hc hb le_rfl h).symm

namespace Profile
variable {n : ℕ}

theorem xi_add_antitone (P : Profile n) : Antitone (fun i : Fin (n + 1) => P.xi i + i) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  have hz := P.zeta_castSucc j
  have hg := P.g_lt_castSucc j
  simp only [xi, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at *
  omega

theorem zeta_add_antitone (P : Profile n) : Antitone (fun i : Fin (n + 1) => P.zeta i + i) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  have hz := P.zeta_castSucc j
  have hg := P.g_lt_succ j
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at *
  omega

/-- Normalized profile cells satisfy northwest-to-southeast rectangle convexity. -/
theorem isSkew_cells (P : Profile n) : IsSkew P.cells := by
  intro x hx y hy hxy1 hxy2 i hi j hj
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  obtain ⟨i₁, hi₁, hb₁, hb₂⟩ := mem_cells.mp hx
  obtain ⟨i₂, hi₂, hd₁, hd₂⟩ := mem_cells.mp hy
  simp only [Finset.mem_Icc] at hi hj hxy1 hxy2
  have hi₀ : 0 ≤ i := by omega
  have hin : i.toNat < n + 1 := by have := i₂.isLt; omega
  set k : Fin (n + 1) := ⟨i.toNat, hin⟩ with hk
  have hkv : ((k : ℕ) : ℤ) = i := by simp [hk]; omega
  have h1 : i₁ ≤ k := by rw [Fin.le_def]; simp only [hk]; omega
  have h2 : k ≤ i₂ := by rw [Fin.le_def]; simp only [hk]; omega
  have e1 := P.zeta_add_antitone h1
  have e2 := P.xi_add_antitone h2
  dsimp only at e1 e2
  rw [← hkv, mem_cells_fin]
  omega

/-- Adjacent rows have a vertically adjacent cell pair at the upper row's left endpoint. -/
theorem mem_cells_vertical (P : Profile n) (j : Fin n) :
    (((j.castSucc : ℕ) : ℤ), P.zeta j.castSucc + (j.castSucc : ℕ)) ∈ P.cells ∧
    (((j.succ : ℕ) : ℤ), P.zeta j.castSucc + (j.castSucc : ℕ)) ∈ P.cells := by
  have hz := P.zeta_strictAnti (Fin.castSucc_lt_succ (i := j))
  have hg := P.xi_succ_sub_zeta_castSucc j
  have hr := P.xi_sub_zeta j.castSucc
  have hr' := P.r_pos j.castSucc
  have hjs : ((j.succ : ℕ) : ℤ) = (j.castSucc : ℕ) + 1 := by simp
  constructor
  · rw [mem_cells_fin]; omega
  · rw [mem_cells_fin]; omega

/-- Profile cells are edge-connected, including the one-row boundary case. -/
theorem isEdgeConnected_cells (P : Profile n) : IsEdgeConnected P.cells := by
  have hbase : ∀ m : ℕ, ∀ hm : m < n + 1, ∀ b : ℤ, ((m : ℤ), b) ∈ P.cells →
      DiagReach P.cells (0, P.zeta 0) ((m : ℤ), b) := by
    intro m
    induction m with
    | zero =>
      intro hm b hb
      have h0 : ((0 : ℤ), P.zeta 0) ∈ P.cells := by simpa using P.row_left_mem_cells 0
      exact P.isSkew_cells.reach_row h0 (by simpa using hb)
    | succ m ih =>
      intro hm b hb
      have hmn : m < n := by omega
      set j : Fin n := ⟨m, hmn⟩ with hj
      obtain ⟨hv1, hv2⟩ := P.mem_cells_vertical j
      have hjc : ((j.castSucc : ℕ) : ℤ) = m := by simp [hj]
      have hjs : ((j.succ : ℕ) : ℤ) = (m : ℤ) + 1 := by simp [hj]
      rw [hjc] at hv1
      rw [hjs] at hv2
      have hr1 := ih (by omega) _ hv1
      have hstep : DiagReach P.cells (m, P.zeta j.castSucc + (j.castSucc : ℕ))
          ((m : ℤ) + 1, P.zeta j.castSucc + (j.castSucc : ℕ)) :=
        Relation.ReflTransGen.single ⟨hv1, hv2, by rw [cellAdj_iff]; simp⟩
      have hrow := P.isSkew_cells.reach_row hv2 (show (((m + 1 : ℕ) : ℤ), b) ∈ P.cells from hb)
      have he : (((m + 1 : ℕ) : ℤ), b) = ((m : ℤ) + 1, b) := by simp
      rw [he]
      exact (hr1.trans hstep).trans hrow
  have h0 : ((0 : ℤ), P.zeta 0) ∈ P.cells := by simpa using P.row_left_mem_cells 0
  have hr : ∀ x ∈ P.cells, DiagReach P.cells (0, P.zeta 0) x := by
    rintro ⟨a, b⟩ hx
    obtain ⟨i, hi, _⟩ := mem_cells.mp hx
    have h := hbase i i.isLt b (by rw [hi]; exact hx)
    rw [hi] at h
    exact h
  exact ⟨⟨_, h0⟩, fun x hx y hy => (hr x hx).symm.trans (hr y hy)⟩

/-- Every valid profile is a faithful connected skew cell diagram. -/
theorem isConnectedSkew_cells (P : Profile n) : IsConnectedSkew P.cells :=
  ⟨P.isSkew_cells, P.isEdgeConnected_cells⟩

end Profile
end SkewGluing
