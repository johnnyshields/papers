/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.InteriorBlockComponents

/-!
# Complete original block determinants

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Canonical interval indices reindex the
full diagonal block, and the original complementary determinant factors over its actual
produced blocks. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Canonical consecutive indices enumerate every row of the original block fiber. -/
def interiorBlockIndexEquiv {n : ℕ} (P : Profile n) (i : Fin n) :
    Fin (interiorBlockLength P i + 1) ≃ {j : Fin n // interiorBlock P j = interiorBlock P i} where
  toFun j := ⟨interiorSliceIndex (interiorBlockFirst P i).val (interiorBlockLength P i)
    (interiorBlock_interval_bound P i) j, by
      have hfirst : interiorSliceIndex (interiorBlockFirst P i).val
          (interiorBlockLength P i) (interiorBlock_interval_bound P i) 0 =
          interiorBlockFirst P i := by apply Fin.ext; simp [interiorSliceIndex]
      exact (interiorBlock_slice_same P i j).trans
        (by rw [hfirst]; exact (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i))⟩
  invFun j := ⟨j.val.val - (interiorBlockFirst P i).val, by
    obtain ⟨ha, hb⟩ := (mem_interiorBlockFiber_iff P i j.val).mp
      ((mem_interiorBlockFiber P i j.val).mpr j.property)
    have ha' := Fin.le_def.mp ha
    have hb' := Fin.le_def.mp hb
    unfold interiorBlockLength
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp [interiorSliceIndex]
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have ha := Fin.le_def.mp ((mem_interiorBlockFiber_iff P i j.val).mp
      ((mem_interiorBlockFiber P i j.val).mpr j.property)).1
    simp only [interiorSliceIndex]
    omega

/-- The full complementary polynomial determinant factors over the produced ordered blocks. -/
theorem interior_det_eq_block_product {n : ℕ} (P : Profile n) :
    (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).det =
      ∏ a ∈ Finset.univ.image (interiorBlock P),
        ((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
          (interiorBlock P) a).det :=
  (interior_polynomial_blockTriangular P).det

/-- The complete diagonal block is the actual consecutive interval, including empty-row blocks. -/
theorem interior_block_det_eq_interval {n : ℕ} (P : Profile n) (i : Fin n) :
    ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
      (interiorBlock P) (interiorBlock P i)).det =
      (jtMatrix (fun j => P.xi (interiorSliceIndex (interiorBlockFirst P i).val
          (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).succ)
        (fun j => P.zeta (interiorSliceIndex (interiorBlockFirst P i).val
          (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).castSucc)).det := by
  have he := Matrix.det_reindex_self (interiorBlockIndexEquiv P i).symm
    ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
      (interiorBlock P) (interiorBlock P i))
  rw [← he]
  have hm : Matrix.reindex (interiorBlockIndexEquiv P i).symm
      (interiorBlockIndexEquiv P i).symm
      ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
        (interiorBlock P) (interiorBlock P i)) =
      jtMatrix (fun j => P.xi (interiorSliceIndex (interiorBlockFirst P i).val
          (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).succ)
        (fun j => P.zeta (interiorSliceIndex (interiorBlockFirst P i).val
          (interiorBlockLength P i) (interiorBlock_interval_bound P i) j).castSucc) := by
    apply Matrix.ext
    intro j k
    rfl
  rw [hm]

/-- The full diagonal block and the normalized connected profile have equal determinants. -/
theorem interior_block_det_eq_profile {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.zeta i.castSucc < P.xi i.succ) :
    ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
      (interiorBlock P) (interiorBlock P i)).det = (interiorBlockProfile P i hi).schur := by
  rw [interior_block_det_eq_interval P i,
    interiorSliceProfile_matrix P _ _ _ (interiorBlock_slice_same P i)
      (interiorBlock_first_nonempty P i hi)]
  rfl

/-- The actual empty-row block determinant is one, with its row and column retained. -/
theorem interior_empty_block_det {n : ℕ} (P : Profile n) (i : Fin n)
    (hi : P.xi i.succ = P.zeta i.castSucc) :
    ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
      (interiorBlock P) (interiorBlock P i)).det = 1 := by
  let : Unique {j : Fin n // interiorBlock P j = interiorBlock P i} :=
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext (interior_empty_row_isolated P i hi j.val j.property)⟩
  rw [Matrix.det_unique]
  change hh (P.xi i.succ - P.zeta i.castSucc) = 1
  rw [hi, sub_self, hh_zero]

/-- An actual one-row block has its literal complete-homogeneous determinant. -/
theorem interior_singleton_block_det {n : ℕ} (P : Profile n) (i : Fin n)
    (hlen : interiorBlockLength P i = 0) :
    ((jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).toSquareBlock
      (interiorBlock P) (interiorBlock P i)).det =
        hh (P.xi (interiorBlockFirst P i).succ - P.zeta (interiorBlockFirst P i).castSucc) := by
  let : Unique (Fin (interiorBlockLength P i + 1)) :=
    ⟨⟨0⟩, fun j => Fin.ext (by have hj := j.isLt; change j.val = 0; omega)⟩
  rw [interior_block_det_eq_interval, Matrix.det_unique]
  rfl

end SkewCornerDescent.Matrix
