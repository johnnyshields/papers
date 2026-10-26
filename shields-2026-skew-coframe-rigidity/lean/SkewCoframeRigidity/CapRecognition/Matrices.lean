/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.CapRecognition.Basic

/-!
# The bordered board of a weak cap

`zMat K e` has the image of `K` above a last row `(z^{e p})`.  Its determinant expands along the
last row into `z`-powers times determinants of `K` with one column deleted.  The cap numerator
`N` is the case `K_{ip} = h_{X_i - Y_p}` with border label `0` appended to the columns, and the
auxiliary `D` omits the first row.  Sorry-free.
-/

namespace SkewCoframeRigidity.CapRecognition

open SkewCofactorIndependence

/-- The image of `K` above a last row of `z`-powers. -/
noncomputable def zMat {n : ℕ} (K : Matrix (Fin n) (Fin (n + 1)) CompleteRing)
    (e : Fin (n + 1) → ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) J :=
  Matrix.of fun i p => Fin.lastCases (zJ ^ e p) (fun i' => ι (K i' p)) i

/-- The bordered Jacobi--Trudi board with row labels `Xr` and column labels `Yc`. -/
noncomputable def Zb {n : ℕ} (Xr : Fin n → ℤ) (Yc : Fin (n + 1) → ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) J :=
  zMat (Matrix.of fun i p => complete (Xr i - Yc p)) fun p => (Yc p).toNat

theorem zMat_det {n : ℕ} (K : Matrix (Fin n) (Fin (n + 1)) CompleteRing)
    (e : Fin (n + 1) → ℕ) :
    (zMat K e).det =
      ∑ p : Fin (n + 1), (-1 : J) ^ (n + (p : ℕ)) * zJ ^ e p *
        ι (K.submatrix id p.succAbove).det := by
  rw [Matrix.det_succ_row _ (Fin.last n)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hM : (zMat K e).submatrix (Fin.last n).succAbove p.succAbove =
      (K.submatrix id p.succAbove).map ι := by
    ext i j
    simp [zMat, Fin.succAbove_last]
  rw [hM, RingHom.map_det]
  simp [zMat]

theorem Zb_det {n : ℕ} (Xr : Fin n → ℤ) (Yc : Fin (n + 1) → ℤ) :
    (Zb Xr Yc).det =
      ∑ p : Fin (n + 1), (-1 : J) ^ (n + (p : ℕ)) * zJ ^ (Yc p).toNat *
        ι (betaBoard Xr (Yc ∘ p.succAbove)).det := by
  unfold Zb
  rw [zMat_det]
  rfl

end SkewCoframeRigidity.CapRecognition
