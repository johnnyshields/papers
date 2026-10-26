/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowRows

/-!
# Literal row positions and full endpoint lists of translated interior blocks

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
Whole component equality determines both extreme original row positions and both
endpoints of every complete nonempty complementary row. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A whole nonempty block contains every row of its original interval. -/
theorem interiorBlockCells_row_exists {n : ℕ} (P : Profile n) (b i : Fin n)
    (hne : P.zeta b.castSucc < P.xi b.succ)
    (hi : interiorBlock P i = interiorBlock P b) :
    ∃ s : ℤ, ((i : ℤ), s) ∈ interiorBlockCells P b := by
  have hp := interior_block_row_nonempty P hne hi
  exact ⟨P.zeta i.castSucc + i,
    (mem_interiorBlockCells P b _ _).mpr ⟨i, hi, rfl, le_rfl, by omega⟩⟩

/-- Every cell records a row between the actual first and last complementary indices. -/
theorem interiorBlockCells_row_bounds {n : ℕ} (P : Profile n) (b : Fin n)
    {x : ℤ × ℤ} (hx : x ∈ interiorBlockCells P b) :
    (interiorBlockFirst P b : ℤ) ≤ x.1 ∧ x.1 ≤ (interiorBlockLast P b : ℤ) := by
  obtain ⟨r, s⟩ := x
  obtain ⟨i, hi, hr, _, _⟩ := (mem_interiorBlockCells P b r s).mp hx
  have hb := (mem_interiorBlockFiber_iff P b i).mp
    ((mem_interiorBlockFiber P b i).mpr hi)
  have hlo := Fin.le_def.mp hb.1
  have hhi := Fin.le_def.mp hb.2
  dsimp only
  omega

/-- Equality of complete translated blocks fixes the actual first and last source rows. -/
theorem interiorBlockCells_translated_row_extremes {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b : Fin n) (d : Fin m) (hb : P.zeta b.castSucc < P.xi b.succ)
    (hd : Q.zeta d.castSucc < Q.xi d.succ) (v : ℤ × ℤ)
    (he : translate v (interiorBlockCells P b) = interiorBlockCells Q d) :
    (interiorBlockFirst Q d : ℤ) = (interiorBlockFirst P b : ℤ) + v.1 ∧
      (interiorBlockLast Q d : ℤ) = (interiorBlockLast P b : ℤ) + v.1 := by
  obtain ⟨s, hs⟩ := interiorBlockCells_row_exists P b (interiorBlockFirst P b) hb
    ((mem_interiorBlockFiber P b _).mp (interiorBlockFirst_mem P b))
  obtain ⟨t, ht⟩ := interiorBlockCells_row_exists P b (interiorBlockLast P b) hb
    ((mem_interiorBlockFiber P b _).mp (interiorBlockLast_mem P b))
  obtain ⟨u, hu⟩ := interiorBlockCells_row_exists Q d (interiorBlockFirst Q d) hd
    ((mem_interiorBlockFiber Q d _).mp (interiorBlockFirst_mem Q d))
  obtain ⟨w, hw⟩ := interiorBlockCells_row_exists Q d (interiorBlockLast Q d) hd
    ((mem_interiorBlockFiber Q d _).mp (interiorBlockLast_mem Q d))
  have hs' : ((interiorBlockFirst P b : ℤ), s) + v ∈ interiorBlockCells Q d := by
    rw [← he, mem_translate, add_sub_cancel_right]
    exact hs
  have ht' : ((interiorBlockLast P b : ℤ), t) + v ∈ interiorBlockCells Q d := by
    rw [← he, mem_translate, add_sub_cancel_right]
    exact ht
  rw [← he, mem_translate] at hu hw
  have ha := interiorBlockCells_row_bounds Q d hs'
  have hz := interiorBlockCells_row_bounds Q d ht'
  have ha' := interiorBlockCells_row_bounds P b hu
  have hz' := interiorBlockCells_row_bounds P b hw
  simp only [Prod.fst_add, Prod.fst_sub] at ha hz ha' hz'
  omega

/-- Every complete row of a translated nonempty block has the same original endpoints. -/
theorem interiorBlockCells_translated_row_endpoints {n m : ℕ} (P : Profile n)
    (Q : Profile m) (b i : Fin n) (d j : Fin m)
    (hb : P.zeta b.castSucc < P.xi b.succ)
    (hd : Q.zeta d.castSucc < Q.xi d.succ)
    (hi : interiorBlock P i = interiorBlock P b)
    (hj : interiorBlock Q j = interiorBlock Q d)
    (v : ℤ × ℤ) (hrow : (j : ℤ) = (i : ℤ) + v.1)
    (he : translate v (interiorBlockCells P b) = interiorBlockCells Q d) :
    Q.xi j.succ = P.xi i.succ + content v ∧
      Q.zeta j.castSucc = P.zeta i.castSucc + content v := by
  have hp := interior_block_row_nonempty P hb hi
  have hq := interior_block_row_nonempty Q hd hj
  have hcell (s : ℤ) :
      P.zeta i.castSucc + i ≤ s ∧ s < P.xi i.succ + i ↔
        Q.zeta j.castSucc + j ≤ s + v.2 ∧ s + v.2 < Q.xi j.succ + j := by
    constructor
    · intro hs
      have hx : ((i : ℤ), s) + v ∈ interiorBlockCells Q d := by
        rw [← he, mem_translate, add_sub_cancel_right]
        exact (mem_interiorBlockCells P b _ _).mpr ⟨i, hi, rfl, hs⟩
      obtain ⟨k, _, hr, hlo, hhi⟩ := (mem_interiorBlockCells Q d _ _).mp hx
      have hk : k = j := Fin.ext (by exact_mod_cast hr.trans hrow.symm)
      subst k
      exact ⟨hlo, hhi⟩
    · intro hs
      have hx : ((j : ℤ), s + v.2) ∈ translate v (interiorBlockCells P b) := by
        rw [he]
        exact (mem_interiorBlockCells Q d _ _).mpr ⟨j, hj, rfl, hs⟩
      rw [mem_translate] at hx
      obtain ⟨k, _, hr, hlo, hhi⟩ := (mem_interiorBlockCells P b _ _).mp hx
      have hk : k = i := Fin.ext (by
        have hh : (k : ℤ) = (i : ℤ) := by dsimp only at hr; omega
        exact_mod_cast hh)
      subst k
      simp only [add_sub_cancel_right] at hlo hhi
      exact ⟨hlo, hhi⟩
  have hlo := (hcell (P.zeta i.castSucc + i)).mp ⟨le_rfl, by omega⟩
  have hhi := (hcell (P.xi i.succ + i - 1)).mp ⟨by omega, by omega⟩
  have hlo' := (hcell (Q.zeta j.castSucc + j - v.2)).mpr ⟨by omega, by omega⟩
  have hhi' := (hcell (Q.xi j.succ + j - 1 - v.2)).mpr ⟨by omega, by omega⟩
  unfold content
  omega

end SkewCornerDescent.Matrix
