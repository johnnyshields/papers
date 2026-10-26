/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRemovalLayout
import SkewCornerDescent.Matrix.InteriorBlockComponents
import SkewGluing.ProfileStatistics

/-!
# All-row geometric inventories have literal singleton beta blocks

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The actual geometric row-count hypothesis forces every nonempty original
component to have one complementary row. Empty rows remain their isolated
literal unit vertices. No row-selected hypothesis is substituted for the
all-row inventory assumption. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- A complete actual nonempty component has its original beta-fiber row count. -/
theorem interiorBlockCells_row_count {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    ((interiorBlockCells P i).image Prod.fst).card = interiorBlockLength P i + 1 := by
  have hp : ∃ v, interiorBlockCells P i = translate v (interiorBlockProfile P i hi).cells :=
    ⟨_, interiorSliceCells_eq_translate P _ _ _ (interiorBlock_slice_same P i)
      (interiorBlock_first_nonempty P i hi)⟩
  obtain ⟨v, hv⟩ := hp
  rw [hv, rowCount_translate, Profile.rowCount_cells]

/-- If every actual geometric corner component is a row, no two different
original complementary indices belong to the same block. Literal empty
vertices remain, rather than being removed as empty components. -/
theorem interiorBlock_injective_of_all_rows {n : ℕ} (P : Profile n)
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1) :
    Function.Injective (interiorBlock P) := by
  intro i j he
  by_cases hi : P.zeta i.castSucc < P.xi i.succ
  · have hc := hrows (interiorBlockCells P i) (interiorBlockCells_mem_components P i hi)
    rw [interiorBlockCells_row_count P i hi] at hc
    have hm : interiorBlockLength P i = 0 := by omega
    have hfl := interiorBlockFirst_le_last P i
    have hb : (interiorBlockLast P i).val = (interiorBlockFirst P i).val := by
      dsimp only [interiorBlockLength] at hm
      change (interiorBlockFirst P i).val ≤ (interiorBlockLast P i).val at hfl
      omega
    have hip := (mem_interiorBlockFiber_iff P i i).mp (by simp only [mem_interiorBlockFiber])
    have hjp := (mem_interiorBlockFiber_iff P i j).mp ((mem_interiorBlockFiber P i j).mpr he.symm)
    apply Fin.ext
    change (interiorBlockFirst P i).val ≤ i.val ∧ i.val ≤ (interiorBlockLast P i).val at hip
    change (interiorBlockFirst P i).val ≤ j.val ∧ j.val ≤ (interiorBlockLast P i).val at hjp
    omega
  · have hz : P.xi i.succ = P.zeta i.castSucc := by
      have := P.zeta_le_xi_succ i
      omega
    exact (interior_empty_row_isolated P i hz j he.symm).symm

/-- Every complete original block has zero overlap length on an all-row
inventory, including the actual isolated unit vertices. -/
theorem interiorBlockLength_eq_zero_of_all_rows {n : ℕ} (P : Profile n)
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (i : Fin n) : interiorBlockLength P i = 0 := by
  have hfirst := (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)
  have hlast := (mem_interiorBlockFiber P i _).mp (interiorBlockLast_mem P i)
  have hf := interiorBlock_injective_of_all_rows P hrows hfirst
  have hl := interiorBlock_injective_of_all_rows P hrows hlast
  rw [interiorBlockLength, hf, hl, Nat.sub_self]

end SkewCornerDescent.Matrix
