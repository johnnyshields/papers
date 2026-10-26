/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowRows

/-!
# Original complementary source positions inside complete equal windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
Literal membership and nonmembership at all four row endpoints determine the
actual copied complementary position, including a zero-length interior unit pivot.
No interior cell witness is needed for the unit case. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Complete equal windows transport membership and nonmembership at every band cell. -/
theorem originalWindow_cell_translation {n : ℕ} (P : Profile n) (lo hi q : ℤ)
    (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (x : ℤ × ℤ) (hband : lo ≤ content x ∧ content x < hi) :
    x ∈ P.cells ↔ x + v ∈ P.cells := by
  have hband' : lo + q ≤ content (x + v) ∧ content (x + v) < hi + q := by
    rw [content_add, hv]
    omega
  have hsource : x ∈ P.cells ↔
      x ∈ P.cells.filter (fun x => lo ≤ content x ∧ content x < hi) := by
    simp only [Finset.mem_filter, hband, and_true]
  have htarget : x + v ∈ P.cells ↔
      x + v ∈ P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    simp only [Finset.mem_filter, hband', and_true]
  rw [hsource, htarget, hwindow, mem_translate, add_sub_cancel_right]

/-- A complete original complementary position inside the band has a produced translated
position and both translated endpoints. Equality of the endpoints, hence a unit pivot,
is permitted rather than excluded by a nonempty-component hypothesis. -/
theorem originalWindow_complementary_position {n : ℕ} (P : Profile n) (lo hi q : ℤ)
    (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (i : Fin n) (hlo : lo < P.zeta i.castSucc) (hhi : P.xi i.succ < hi) :
    ∃ j : Fin n, (j : ℤ) = (i : ℤ) + v.1 ∧
      P.xi j.succ = P.xi i.succ + q ∧ P.zeta j.castSucc = P.zeta i.castSucc + q := by
  have hg := P.zeta_le_xi_succ i
  have hl0 := P.xi_sub_zeta i.castSucc
  have hl1 := P.xi_sub_zeta i.succ
  have hr0 := P.r_pos i.castSucc
  have hr1 := P.r_pos i.succ
  let a : ℤ × ℤ := ((i : ℤ), P.zeta i.castSucc + i)
  let b : ℤ × ℤ := ((i : ℤ), P.zeta i.castSucc + i - 1)
  let c : ℤ × ℤ := ((i : ℤ) + 1, P.xi i.succ + i - 1 + 1)
  let d : ℤ × ℤ := ((i : ℤ) + 1, P.xi i.succ + i + 1)
  have ha : a ∈ P.cells := (P.mem_cells_fin i.castSucc _).mpr
    ⟨le_rfl, by simp only [Fin.val_castSucc]; omega⟩
  have hb : b ∉ P.cells := by
    intro h
    have hh := (P.mem_cells_fin i.castSucc _).mp h
    simp only [Fin.val_castSucc] at hh
    omega
  have hc : c ∈ P.cells := by
    have hh := (P.mem_cells_fin i.succ (P.xi i.succ + i)).mpr
      (by simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]; omega)
    simpa only [c, sub_add_cancel, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hh
  have hd : d ∉ P.cells := by
    intro h
    have hh := (P.mem_cells_fin i.succ _).mp
      (show ((i.succ : ℤ), P.xi i.succ + i + 1) ∈ P.cells from
        by simpa only [d, Fin.val_succ, Nat.cast_add, Nat.cast_one] using h)
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at hh
    omega
  have ht (x : ℤ × ℤ) (h : lo ≤ content x ∧ content x < hi) :=
    originalWindow_cell_translation P lo hi q v hv hwindow x h
  have hat := (ht a (by dsimp only [a, content]; omega)).mp ha
  have hbt := mt (ht b (by dsimp only [b, content]; omega)).mpr hb
  have hct := (ht c (by dsimp only [c, content]; omega)).mp hc
  have hdt := mt (ht d (by dsimp only [d, content]; omega)).mpr hd
  obtain ⟨j0, hj0, _, _⟩ := P.mem_cells.mp hat
  obtain ⟨j1, hj1, _, _⟩ := P.mem_cells.mp hct
  simp only [a, c] at hj0 hj1
  have hj01 : j0.val + 1 = j1.val := by omega
  let j : Fin n := ⟨j0.val, by have hh := j1.isLt; omega⟩
  have hrow : (j : ℤ) = (i : ℤ) + v.1 := hj0
  have hat' := (P.mem_cells_fin j.castSucc (P.zeta i.castSucc + i + v.2)).mp
    (by
      have he : a + v = ((j : ℤ), P.zeta i.castSucc + i + v.2) := by
        apply Prod.ext
        · exact hrow.symm
        · rfl
      rw [he] at hat
      exact hat)
  have hct' := (P.mem_cells_fin j.succ (P.xi i.succ + i + v.2)).mp
    (by
      have he : c + v = ((j.succ : ℤ), P.xi i.succ + i + v.2) := by
        ext <;> simp only [c, Prod.fst_add, Prod.snd_add,
          Fin.val_succ, Nat.cast_add, Nat.cast_one] <;> omega
      rw [he] at hct
      exact hct)
  have hz : P.zeta j.castSucc = P.zeta i.castSucc + q := by
    have hn : ¬ (P.zeta j.castSucc + j ≤ P.zeta i.castSucc + i - 1 + v.2 ∧
        P.zeta i.castSucc + i - 1 + v.2 < P.xi j.castSucc + j) := by
      intro hh
      apply hbt
      have hm := (P.mem_cells_fin j.castSucc _).mpr hh
      have he : b + v = ((j.castSucc : ℤ), P.zeta i.castSucc + i - 1 + v.2) := by
        apply Prod.ext
        · exact hrow.symm
        · rfl
      rw [he]
      exact hm
    unfold content at hv
    simp only [Fin.val_castSucc] at hat'
    omega
  have hx : P.xi j.succ = P.xi i.succ + q := by
    have hn : ¬ (P.zeta j.succ + j.succ ≤ P.xi i.succ + i + 1 + v.2 ∧
        P.xi i.succ + i + 1 + v.2 < P.xi j.succ + j.succ) := by
      intro hh
      apply hdt
      have hm := (P.mem_cells_fin j.succ _).mpr hh
      have he : d + v = ((j.succ : ℤ), P.xi i.succ + i + 1 + v.2) := by
        apply Prod.ext
        · change (i : ℤ) + 1 + v.1 = (j : ℤ) + 1
          omega
        · rfl
      rw [he]
      exact hm
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at hct' hn
    unfold content at hv
    omega
  exact ⟨j, hrow, hx, hz⟩

/-- A copied unit pivot is an actual unique source position, not an empty cell witness. -/
theorem originalWindow_unit_pivot {n : ℕ} (P : Profile n) (lo hi q : ℤ)
    (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (i : Fin n) (hlo : lo < P.zeta i.castSucc) (hhi : P.xi i.succ < hi)
    (hunit : P.xi i.succ = P.zeta i.castSucc) :
    ∃! j : Fin n, (j : ℤ) = (i : ℤ) + v.1 ∧
      P.xi j.succ = P.zeta j.castSucc ∧
      P.zeta j.castSucc = P.zeta i.castSucc + q := by
  obtain ⟨j, hj, hx, hz⟩ :=
    originalWindow_complementary_position P lo hi q v hv hwindow i hlo hhi
  refine ⟨j, ⟨hj, by omega, hz⟩, ?_⟩
  intro k hk
  apply Fin.ext
  have he : (k : ℤ) = (j : ℤ) := hk.1.trans hj.symm
  exact_mod_cast he

end SkewCornerDescent.Matrix
