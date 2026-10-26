/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergBoundaryCondensation
import SkewCornerDescent.Matrix.FormalLogProduct

/-!
# Complete endpoint logarithmic locality below the full selected cost

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Exact condensation and complete logarithmic jet congruence retain all original
cap jets, including entries containing the chosen higher generator. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Complete endpoint logarithms satisfy exact four-minor cancellation below the full cost.

**Differs from the paper's route.** Endpoint condensation replaces the connected
cluster expansion for this interaction; no boundary entry is frozen. -/
theorem hessenberg_boundary_log_coeff {F : Type*} [Field F] [Algebra ℚ F] {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F)
    (hsub : ∀ i : Fin (n + 1), A i.succ i.castSucc = PowerSeries.C a * PowerSeries.X)
    (hfull : PowerSeries.constantCoeff A.det ≠ 0)
    (hmid : PowerSeries.constantCoeff
      (A.submatrix (fun i : Fin n => i.castSucc.succ)
        (fun j : Fin n => j.castSucc.succ)).det ≠ 0)
    (hright : PowerSeries.constantCoeff (A.submatrix Fin.succ Fin.succ).det ≠ 0)
    (hleft : PowerSeries.constantCoeff (A.submatrix Fin.castSucc Fin.castSucc).det ≠ 0)
    (k : ℕ) (hk : k < n + 1) :
    let mid := (A.submatrix (fun i : Fin n => i.castSucc.succ)
      (fun j : Fin n => j.castSucc.succ)).det
    let right := (A.submatrix Fin.succ Fin.succ).det
    let left := (A.submatrix Fin.castSucc Fin.castSucc).det
    PowerSeries.coeff k (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff A.det)⁻¹ * A.det)) +
      PowerSeries.coeff k (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff mid)⁻¹ * mid)) =
    PowerSeries.coeff k (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff right)⁻¹ * right)) +
      PowerSeries.coeff k (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff left)⁻¹ * left)) := by
  let mid := (A.submatrix (fun i : Fin n => i.castSucc.succ)
    (fun j : Fin n => j.castSucc.succ)).det
  let right := (A.submatrix Fin.succ Fin.succ).det
  let left := (A.submatrix Fin.castSucc Fin.castSucc).det
  have hp : PowerSeries.constantCoeff (A.det * mid) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hfull hmid
  have hq : PowerSeries.constantCoeff (right * left) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hright hleft
  have hjet : ∀ j ≤ k, PowerSeries.coeff j (A.det * mid) =
      PowerSeries.coeff j (right * left) := by
    intro j hj
    exact hessenberg_boundary_normal_coeff A hA a hsub j (hj.trans_lt hk)
  have h := normalized_log_coeff_congr (A.det * mid) (right * left) hp hq k hjet k le_rfl
  rw [normalized_log_mul_complete A.det mid hfull hmid,
    normalized_log_mul_complete right left hright hleft, map_add, map_add] at h
  exact h

end SkewCornerDescent.Matrix
