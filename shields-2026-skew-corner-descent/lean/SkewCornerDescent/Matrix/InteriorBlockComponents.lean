/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.InteriorBlockCells

/-!
# Interior block components

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Actual adjacency cannot cross a produced
block cut. Empty rows stay outside the cell components while retaining their unit pivots.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Cells separated by a produced cut cannot share an edge. -/
theorem interior_block_not_adjacent {n : ℕ} (P : Profile n) (i j : Fin n) (b c : ℤ)
    (hi : P.zeta i.castSucc + i ≤ b ∧ b < P.xi i.succ + i)
    (hj : P.zeta j.castSucc + j ≤ c ∧ c < P.xi j.succ + j)
    (hblock : interiorBlock P j < interiorBlock P i) :
    ¬ CellAdj ((i : ℤ), b) ((j : ℤ), c) := by
  obtain ⟨k, hk, hjk, hki⟩ := exists_interiorCut_of_block_lt P i j hblock
  have hcut := (Finset.mem_filter.mp hk).2.2
  have hr := P.xi_strictAnti.antitone (show k.succ ≤ i.succ by
    change k.val + 1 ≤ i.val + 1
    exact Nat.add_le_add_right (Fin.le_def.mp hki) 1)
  have hc := P.zeta_strictAnti.antitone
    (show j.castSucc ≤ (previousIndex k).castSucc by
      change j.val ≤ k.val - 1
      have h := Fin.lt_def.mp hjk
      omega)
  have hji : j.val < i.val := (Fin.lt_def.mp hjk).trans_le (Fin.le_def.mp hki)
  have hendpoint : P.xi i.succ < P.zeta j.castSucc := by omega
  intro hadj
  rw [cellAdj_iff] at hadj
  dsimp only at hadj
  omega

/-- Adjacent actual interior cells have the same produced block label. -/
theorem interior_adjacent_same_block {n : ℕ} (P : Profile n) (i j : Fin n) (b c : ℤ)
    (hi : P.zeta i.castSucc + i ≤ b ∧ b < P.xi i.succ + i)
    (hj : P.zeta j.castSucc + j ≤ c ∧ c < P.xi j.succ + j)
    (hadj : CellAdj ((i : ℤ), b) ((j : ℤ), c)) :
    interiorBlock P i = interiorBlock P j := by
  rcases lt_trichotomy (interiorBlock P i) (interiorBlock P j) with h | h | h
  · exact False.elim (interior_block_not_adjacent P j i c b hj hi h hadj.symm')
  · exact h
  · exact False.elim (interior_block_not_adjacent P i j b c hi hj h hadj)

/-- The complete actual cell fiber of one produced interior block. -/
def interiorBlockCells {n : ℕ} (P : Profile n) (i : Fin n) : Diagram :=
  interiorSliceCells P (interiorBlockFirst P i).val (interiorBlockLength P i)
    (interiorBlock_interval_bound P i)

/-- Membership records an original row index and its produced block, including all cells. -/
theorem mem_interiorBlockCells {n : ℕ} (P : Profile n) (i : Fin n) (r b : ℤ) :
    (r, b) ∈ interiorBlockCells P i ↔ ∃ j : Fin n,
      interiorBlock P j = interiorBlock P i ∧ (j : ℤ) = r ∧
      P.zeta j.castSucc + j ≤ b ∧ b < P.xi j.succ + j := by
  unfold interiorBlockCells
  rw [interiorSliceCells_eq_filter, Finset.mem_filter, P.mem_interior_cells]
  constructor
  · rintro ⟨⟨j, hr, hlo, hhi⟩, ha, hb⟩
    have hends := Fin.le_def.mp (interiorBlockFirst_le_last P i)
    have hja : interiorBlockFirst P i ≤ j := by change _ ≤ j.val; omega
    have hjb : j ≤ interiorBlockLast P i := by
      change j.val ≤ _
      unfold interiorBlockLength at hb
      omega
    exact ⟨j, (mem_interiorBlockFiber P i j).mp
      ((mem_interiorBlockFiber_iff P i j).mpr ⟨hja, hjb⟩), hr, hlo, hhi⟩
  · rintro ⟨j, hj, hr, hlo, hhi⟩
    obtain ⟨ha, hb⟩ := (mem_interiorBlockFiber_iff P i j).mp
      ((mem_interiorBlockFiber P i j).mpr hj)
    have hends := Fin.le_def.mp (interiorBlockFirst_le_last P i)
    have ha' := Fin.le_def.mp ha
    have hb' := Fin.le_def.mp hb
    refine ⟨⟨j, hr, hlo, hhi⟩, ?_, ?_⟩
    · dsimp only
      omega
    · dsimp only
      unfold interiorBlockLength
      omega

/-- Adjacency in the original interior preserves membership in its actual block cells. -/
theorem interior_adjacent_mem_block {n : ℕ} (P : Profile n) (i : Fin n)
    {x y : ℤ × ℤ} (hx : x ∈ interiorBlockCells P i)
    (hy : y ∈ diagramInterior P.cells) (hadj : CellAdj x y) :
    y ∈ interiorBlockCells P i := by
  obtain ⟨r, b⟩ := x
  obtain ⟨s, c⟩ := y
  obtain ⟨j, hj, hr, hlo, hhi⟩ := (mem_interiorBlockCells P i r b).mp hx
  obtain ⟨k, hs, klo, khi⟩ := (P.mem_interior_cells s c).mp hy
  rw [← hr, ← hs] at hadj
  have he := interior_adjacent_same_block P j k b c ⟨hlo, hhi⟩ ⟨klo, khi⟩ hadj
  exact (mem_interiorBlockCells P i s c).mpr ⟨k, he.symm.trans hj, hs, klo, khi⟩

/-- Every actual interior path stays inside the produced block containing its initial cell. -/
theorem interior_reach_mem_block {n : ℕ} (P : Profile n) (i : Fin n)
    {x y : ℤ × ℤ} (hx : x ∈ interiorBlockCells P i)
    (hr : DiagReach (diagramInterior P.cells) x y) : y ∈ interiorBlockCells P i := by
  induction hr with
  | refl => exact hx
  | tail _ hab ih => exact interior_adjacent_mem_block P i ih hab.2.1 hab.2.2

/-- The actual cells in a nonempty produced block are connected and skew. -/
theorem interiorBlockCells_connected {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) : IsConnectedSkew (interiorBlockCells P i) :=
  interiorSliceCells_connected P _ _ _ (interiorBlock_slice_same P i)
    (interiorBlock_first_nonempty P i hi)

/-- Every nonempty produced block is one entire geometric interior component. -/
theorem interiorBlockCells_mem_components {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    interiorBlockCells P i ∈ edgeComponents (diagramInterior P.cells) := by
  classical
  have hc := interiorBlockCells_connected P i hi
  have hsub : interiorBlockCells P i ⊆ diagramInterior P.cells :=
    interiorSliceCells_subset P _ _ _
  obtain ⟨x, hx⟩ := hc.2.1
  apply mem_edgeComponents.mpr
  refine ⟨x, hsub hx, ?_⟩
  ext y
  rw [Finset.mem_filter]
  constructor
  · intro hy
    refine ⟨hsub hy, ?_⟩
    exact Relation.ReflTransGen.mono
      (fun _ _ hab => ⟨hsub hab.1, hsub hab.2.1, hab.2.2⟩) x y (hc.2.2 x hx y hy)
  · rintro ⟨_, hr⟩
    exact interior_reach_mem_block P i hx hr

/-- Conversely, every geometric interior component is one produced nonempty block. -/
theorem interior_components_eq_blocks {n : ℕ} (P : Profile n) (C : Diagram) :
    C ∈ edgeComponents (diagramInterior P.cells) ↔
      ∃ i : Fin n, P.zeta i.castSucc < P.xi i.succ ∧ C = interiorBlockCells P i := by
  classical
  constructor
  · intro hC
    obtain ⟨x, hx⟩ := (isEdgeConnected_component hC).1
    obtain ⟨r, b⟩ := x
    obtain ⟨i, hr, hlo, hhi⟩ :=
      (P.mem_interior_cells r b).mp (component_subset hC hx)
    have hi : P.zeta i.castSucc < P.xi i.succ := by omega
    have hx' : (r, b) ∈ interiorBlockCells P i :=
      (mem_interiorBlockCells P i r b).mpr ⟨i, rfl, hr, hlo, hhi⟩
    exact ⟨i, hi, (component_eq_of_mem hC hx).trans
      (component_eq_of_mem (interiorBlockCells_mem_components P i hi) hx').symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact interiorBlockCells_mem_components P i hi

/-- The actual block component's Schur function is its complete original matrix determinant. -/
theorem interiorBlockCells_schur {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    cellSchur (interiorBlockCells P i) (interiorBlockCells_connected P i hi).1 =
      (jtMatrix
        (fun j => P.xi (interiorSliceIndex (interiorBlockFirst P i).val
          (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).succ)
        (fun j => P.zeta (interiorSliceIndex (interiorBlockFirst P i).val
          (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).castSucc)).det := by
  rw [interiorSliceProfile_matrix P _ _ _ (interiorBlock_slice_same P i)
    (interiorBlock_first_nonempty P i hi)]
  exact cellSchur_eq_profile (interiorBlockCells_connected P i hi) (interiorBlockProfile P i hi)
    _ (interiorSliceCells_eq_translate P _ _ _ (interiorBlock_slice_same P i)
      (interiorBlock_first_nonempty P i hi))

/-- The entire geometric component inventory is produced from the actual nonempty rows. -/
theorem interior_edgeComponents_eq_image {n : ℕ} (P : Profile n) :
    edgeComponents (diagramInterior P.cells) =
      (Finset.univ.filter (fun i : Fin n => P.zeta i.castSucc < P.xi i.succ)).image
        (interiorBlockCells P) := by
  classical
  ext C
  rw [interior_components_eq_blocks]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hC⟩
    exact ⟨i, hi, hC.symm⟩
  · rintro ⟨i, hi, hC⟩
    exact ⟨i, hi, hC.symm⟩

end SkewCornerDescent.Matrix
