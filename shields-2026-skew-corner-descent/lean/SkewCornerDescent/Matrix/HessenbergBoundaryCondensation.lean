/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.Hessenberg
import Shields.LinearAlgebra.Matrix.DesnanotJacobi
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Exact endpoint condensation for the complete original Hessenberg matrix

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete endpoint minors satisfy condensation with a full subdiagonal power.
Every cap entry and its normal dependence remains arbitrary. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- The complete first-row/last-column deletion is exactly the selected cost power. -/
theorem hessenberg_bottom_left_minor {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (hA : IsUpperHessenberg A) (t : R)
    (hsub : ∀ i : Fin (n + 1), A i.succ i.castSucc = t) :
    (A.submatrix Fin.succ Fin.castSucc).det = t ^ (n + 1) := by
  have htri : (A.submatrix Fin.succ Fin.castSucc).IsUpperTriangular := by
    intro i j hji
    apply hA
    simp only [Fin.val_castSucc, Fin.val_succ]
    exact Nat.add_lt_add_right (show (j : ℕ) < (i : ℕ) from hji) 1
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [Matrix.submatrix_apply, hsub, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The complete two-cap interaction is divisible by the entire selected cost.
This identity holds before normal substitution and imposes no frozen boundary entry. -/
theorem hessenberg_boundary_condensation {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (hA : IsUpperHessenberg A) (t : R)
    (hsub : ∀ i : Fin (n + 1), A i.succ i.castSucc = t) :
    A.det * (A.submatrix (fun i : Fin n => i.castSucc.succ)
        (fun j : Fin n => j.castSucc.succ)).det -
      (A.submatrix Fin.succ Fin.succ).det *
        (A.submatrix Fin.castSucc Fin.castSucc).det =
      -t ^ (n + 1) * (A.submatrix Fin.castSucc Fin.succ).det := by
  rw [Shields.desnanot_jacobi, hessenberg_bottom_left_minor A hA t hsub]
  ring

/-- The entire complete-cap condensation error starts at the full selected cost.
Boundary entries may contain every generator and every normal jet. -/
theorem hessenberg_boundary_normal_error_dvd {F : Type*} [CommRing F] {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F)
    (hsub : ∀ i : Fin (n + 1), A i.succ i.castSucc = PowerSeries.C a * PowerSeries.X) :
    (PowerSeries.X : PowerSeries F) ^ (n + 1) ∣
      A.det * (A.submatrix (fun i : Fin n => i.castSucc.succ)
          (fun j : Fin n => j.castSucc.succ)).det -
        (A.submatrix Fin.succ Fin.succ).det *
          (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [hessenberg_boundary_condensation A hA (PowerSeries.C a * PowerSeries.X) hsub]
  refine ⟨-PowerSeries.C a ^ (n + 1) * (A.submatrix Fin.castSucc Fin.succ).det, ?_⟩
  rw [mul_pow]
  ring

/-- Every coefficient strictly below the full selected cost satisfies exact
endpoint condensation with the complete original end jets. -/
theorem hessenberg_boundary_normal_coeff {F : Type*} [CommRing F] {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F)
    (hsub : ∀ i : Fin (n + 1), A i.succ i.castSucc = PowerSeries.C a * PowerSeries.X)
    (k : ℕ) (hk : k < n + 1) :
    PowerSeries.coeff k
        (A.det * (A.submatrix (fun i : Fin n => i.castSucc.succ)
          (fun j : Fin n => j.castSucc.succ)).det) =
      PowerSeries.coeff k
        ((A.submatrix Fin.succ Fin.succ).det *
          (A.submatrix Fin.castSucc Fin.castSucc).det) := by
  have h := PowerSeries.X_pow_dvd_iff.mp
    (hessenberg_boundary_normal_error_dvd A hA a hsub)
  have hz := h k hk
  simpa only [map_sub, sub_eq_zero] using hz

end SkewCornerDescent.Matrix
