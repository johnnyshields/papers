/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.InteriorBlockProfiles

/-!
# Canonical intervals of interior blocks

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Each actual block fiber has canonical first
and last indices. Its complete interval supplies the connected profile, without a partition
or connectivity hypothesis supplied by the caller. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- All original complementary indices in the block containing `i`. -/
def interiorBlockFiber {n : ℕ} (P : Profile n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => interiorBlock P j = interiorBlock P i

@[simp] theorem mem_interiorBlockFiber {n : ℕ} (P : Profile n) (i j : Fin n) :
    j ∈ interiorBlockFiber P i ↔ interiorBlock P j = interiorBlock P i := by
  simp [interiorBlockFiber]

theorem interiorBlockFiber_nonempty {n : ℕ} (P : Profile n) (i : Fin n) :
    (interiorBlockFiber P i).Nonempty := ⟨i, by simp⟩

/-- First original row index in the produced block. -/
def interiorBlockFirst {n : ℕ} (P : Profile n) (i : Fin n) : Fin n :=
  (interiorBlockFiber P i).min' (interiorBlockFiber_nonempty P i)

/-- Last original row index in the produced block. -/
def interiorBlockLast {n : ℕ} (P : Profile n) (i : Fin n) : Fin n :=
  (interiorBlockFiber P i).max' (interiorBlockFiber_nonempty P i)

theorem interiorBlockFirst_mem {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorBlockFirst P i ∈ interiorBlockFiber P i :=
  Finset.min'_mem _ _

theorem interiorBlockLast_mem {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorBlockLast P i ∈ interiorBlockFiber P i :=
  Finset.max'_mem _ _

/-- A fiber is exactly the closed interval between its produced endpoints. -/
theorem mem_interiorBlockFiber_iff {n : ℕ} (P : Profile n) (i j : Fin n) :
    j ∈ interiorBlockFiber P i ↔ interiorBlockFirst P i ≤ j ∧
      j ≤ interiorBlockLast P i := by
  constructor
  · intro hj
    exact ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩
  · rintro ⟨ha, hb⟩
    have hf := mem_interiorBlockFiber P i (interiorBlockFirst P i) |>.mp
      (interiorBlockFirst_mem P i)
    have hl := mem_interiorBlockFiber P i (interiorBlockLast P i) |>.mp
      (interiorBlockLast_mem P i)
    exact (mem_interiorBlockFiber P i j).mpr
      ((interiorBlock_interval P ha hb (hf.trans hl.symm)).trans hf)

/-- Number of successive overlaps in the block. -/
def interiorBlockLength {n : ℕ} (P : Profile n) (i : Fin n) : ℕ :=
  (interiorBlockLast P i).val - (interiorBlockFirst P i).val

theorem interiorBlockFirst_le_last {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorBlockFirst P i ≤ interiorBlockLast P i :=
  Finset.min'_le _ _ (interiorBlockLast_mem P i)

theorem interiorBlock_interval_bound {n : ℕ} (P : Profile n) (i : Fin n) :
    (interiorBlockFirst P i).val + interiorBlockLength P i < n := by
  have h := Fin.le_def.mp (interiorBlockFirst_le_last P i)
  have hn := (interiorBlockLast P i).isLt
  unfold interiorBlockLength
  omega

/-- The complete produced interval stays in the original block. -/
theorem interiorBlock_slice_same {n : ℕ} (P : Profile n) (i : Fin n)
    (j : Fin (interiorBlockLength P i + 1)) :
    interiorBlock P (interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) j) =
    interiorBlock P (interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) 0) := by
  have hfirst : interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) 0 =
      interiorBlockFirst P i := by apply Fin.ext; simp [interiorSliceIndex]
  rw [hfirst]
  have hb := Fin.le_def.mp (interiorBlockFirst_le_last P i)
  have hj := j.isLt
  have hm : interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) j ∈
      interiorBlockFiber P i := by
    apply (mem_interiorBlockFiber_iff P i _).mpr
    constructor
    · change (interiorBlockFirst P i).val ≤ (interiorBlockFirst P i).val + j.val
      omega
    · change (interiorBlockFirst P i).val + j.val ≤ (interiorBlockLast P i).val
      unfold interiorBlockLength at hj
      omega
  exact ((mem_interiorBlockFiber P i _).mp hm).trans
    ((mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)).symm

/-- Nonemptiness of any row supplies the first row's strict inequality. -/
theorem interiorBlock_first_nonempty {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    P.zeta (interiorSliceIndex (interiorBlockFirst P i).val (interiorBlockLength P i)
      (interiorBlock_interval_bound P i) 0).castSucc <
    P.xi (interiorSliceIndex (interiorBlockFirst P i).val (interiorBlockLength P i)
      (interiorBlock_interval_bound P i) 0).succ := by
  have hfirst : interiorSliceIndex (interiorBlockFirst P i).val
      (interiorBlockLength P i) (interiorBlock_interval_bound P i) 0 =
      interiorBlockFirst P i := by apply Fin.ext; simp [interiorSliceIndex]
  rw [hfirst]
  exact interior_block_row_nonempty P hi
    ((mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i))

/-- Connected profile of the entire actual nonempty block, produced from its original endpoints. -/
def interiorBlockProfile {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) : Profile (interiorBlockLength P i) :=
  interiorSliceProfile P (interiorBlockFirst P i).val (interiorBlockLength P i)
    (interiorBlock_interval_bound P i) (interiorBlock_slice_same P i)
    (interiorBlock_first_nonempty P i hi)

/-- Equal produced labels give the same complete row fiber. -/
theorem interiorBlockFiber_eq_of_label_eq {n : ℕ} (P : Profile n) {i j : Fin n}
    (h : interiorBlock P i = interiorBlock P j) :
    interiorBlockFiber P i = interiorBlockFiber P j := by
  ext k
  simp only [mem_interiorBlockFiber, h]

/-- The canonical first row is independent of the representative within its block. -/
theorem interiorBlockFirst_eq_of_label_eq {n : ℕ} (P : Profile n) {i j : Fin n}
    (h : interiorBlock P i = interiorBlock P j) :
    interiorBlockFirst P i = interiorBlockFirst P j := by
  unfold interiorBlockFirst
  congr 1
  exact interiorBlockFiber_eq_of_label_eq P h

/-- Taking the first row again does not duplicate a block. -/
theorem interiorBlockFirst_idem {n : ℕ} (P : Profile n) (i : Fin n) :
    interiorBlockFirst P (interiorBlockFirst P i) = interiorBlockFirst P i :=
  interiorBlockFirst_eq_of_label_eq P
    ((mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i))

end SkewCornerDescent.Matrix
