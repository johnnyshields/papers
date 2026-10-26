/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SharedCore
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Compatible orientations of the single-border condensation identity

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
The two mixed minor orientations have the same permutation sign, so their
product retains the integral Desnanot--Jacobi cross difference. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {n m F : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] [CommRing F]

/-- Independent boundary-first and boundary-last frames give the same full
cross difference when their two mixed orientations are retained together. -/
theorem cross_difference_equiv_frames (e f : n ≃ m)
    (M11 M00 M10 M01 : Matrix m m F) :
    (M11.submatrix e e).det * (M00.submatrix f f).det -
      (M10.submatrix e f).det * (M01.submatrix f e).det =
      M11.det * M00.det - M10.det * M01.det := by
  let σ := f.trans e.symm
  have h10 : M10.submatrix e f = (M10.submatrix e e).submatrix id σ := by
    ext i j
    simp [σ, Matrix.submatrix]
  have h01 : M01.submatrix f e = (M01.submatrix e e).submatrix σ id := by
    ext i j
    simp [σ, Matrix.submatrix]
  rw [h10, h01, Matrix.det_permute', Matrix.det_permute]
  simp only [Matrix.det_submatrix_equiv_self]
  have hs : (Equiv.Perm.sign σ : F) * (Equiv.Perm.sign σ : F) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, Int.cast_one]
  calc
    _ = M11.det * M00.det -
        ((Equiv.Perm.sign σ : F) * (Equiv.Perm.sign σ : F)) *
          (M10.det * M01.det) := by ring
    _ = _ := by rw [hs, one_mul]

section FiniteBorder

variable {c : ℕ}

/-- A complete single border, with its unmatched row and column both first. -/
def singleCoreBorder (C : Matrix (Fin c) (Fin c) F)
    (r s : Fin c → F) (z : F) : Matrix (Fin (c + 1)) (Fin (c + 1)) F :=
  Fin.cases (Fin.cases z r) (fun i => Fin.cases (s i) (C i))

/-- Two independent borders around the same complete central matrix. -/
def doubleCoreBorder (C : Matrix (Fin c) (Fin c) F)
    (r₁ r₂ s₁ s₂ : Fin c → F) (z₁₁ z₁₂ z₂₁ z₂₂ : F) :
    Matrix (Fin (c + 2)) (Fin (c + 2)) F :=
  Fin.cases (Fin.cases z₁₁ (Fin.lastCases z₁₂ r₁))
    (Fin.lastCases (Fin.cases z₂₁ (Fin.lastCases z₂₂ r₂))
      (fun i => Fin.cases (s₁ i) (Fin.lastCases (s₂ i) (C i))))

/-- Moving the trailing border to the first slot leaves the two mixed minor
signs paired. The resulting divisibility retains the complete central determinant. -/
theorem singleCoreBorder_cross_difference_dvd
    (C : Matrix (Fin c) (Fin c) F) (r₁ r₂ s₁ s₂ : Fin c → F)
    (z₁₁ z₁₂ z₂₁ z₂₂ : F) :
    C.det ∣ (singleCoreBorder C r₁ s₁ z₁₁).det *
        (singleCoreBorder C r₂ s₂ z₂₂).det -
      (singleCoreBorder C r₁ s₂ z₁₂).det *
        (singleCoreBorder C r₂ s₁ z₂₁).det := by
  classical
  let D := doubleCoreBorder C r₁ r₂ s₁ s₂ z₁₁ z₁₂ z₂₁ z₂₂
  let f := (finRotate (c + 1)).symm
  have hf0 : f 0 = Fin.last c := by
    apply (finRotate (c + 1)).symm_apply_eq.mpr
    exact finRotate_last.symm
  have hfs (i : Fin c) : f i.succ = i.castSucc := by
    apply (finRotate (c + 1)).symm_apply_eq.mpr
    exact (finRotate_of_lt i.isLt).symm
  have hlast (a : F) (b : Fin (c + 1) → F) :
      Fin.cases a b (Fin.last (c + 1)) = b (Fin.last c) := by
    change Fin.cases a b (Fin.last c).succ = b (Fin.last c)
    rfl
  have h11 : D.submatrix Fin.castSucc Fin.castSucc =
      singleCoreBorder C r₁ s₁ z₁₁ := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [D, doubleCoreBorder, singleCoreBorder, Matrix.submatrix]
  have h00 : (D.submatrix Fin.succ Fin.succ).submatrix f f =
      singleCoreBorder C r₂ s₂ z₂₂ := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [D, doubleCoreBorder, singleCoreBorder, Matrix.submatrix, hf0, hfs, hlast]
  have h10 : (D.submatrix Fin.castSucc Fin.succ).submatrix id f =
      singleCoreBorder C r₁ s₂ z₁₂ := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [D, doubleCoreBorder, singleCoreBorder, Matrix.submatrix, hf0, hfs, hlast]
  have h01 : (D.submatrix Fin.succ Fin.castSucc).submatrix f id =
      singleCoreBorder C r₂ s₁ z₂₁ := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [D, doubleCoreBorder, singleCoreBorder, Matrix.submatrix, hf0, hfs]
  have hc : D.submatrix (fun i : Fin c => i.castSucc.succ)
      (fun j : Fin c => j.castSucc.succ) = C := by
    ext i j
    simp [D, doubleCoreBorder, Matrix.submatrix]
  have he := cross_difference_equiv_frames (Equiv.refl (Fin (c + 1))) f
    (D.submatrix Fin.castSucc Fin.castSucc) (D.submatrix Fin.succ Fin.succ)
    (D.submatrix Fin.castSucc Fin.succ) (D.submatrix Fin.succ Fin.castSucc)
  change (D.submatrix Fin.castSucc Fin.castSucc).det *
      ((D.submatrix Fin.succ Fin.succ).submatrix f f).det -
      ((D.submatrix Fin.castSucc Fin.succ).submatrix id f).det *
      ((D.submatrix Fin.succ Fin.castSucc).submatrix f id).det = _ at he
  rw [h11, h00, h10, h01] at he
  rw [he]
  have hd := commonCore_cross_difference_dvd D
  rw [hc, h11] at hd
  convert hd using 1
  ring

end FiniteBorder

end SkewCornerDescent.Matrix
