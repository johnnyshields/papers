/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.DesnanotJacobi

/-!
# Common-core divisibility of corner-minor cross differences

Supports `shields-2026-skew-corner-descent.tex`, «Common-core divisibility»
(`sec:corner-data`, `lem:shared-core`).
The identity is integral and holds over every commutative ring, including singular
specializations and the empty central core.

**Differs from the paper's route.** Desnanot--Jacobi proves the single-border
cross difference without a generic rank-one-deficient locus argument.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix
variable {R : Type*} [CommRing R] {m : ℕ}

/-- The central core divides the exact cross difference of the four corner minors. -/
theorem commonCore_cross_difference_dvd (A : Matrix (Fin (m + 2)) (Fin (m + 2)) R) :
    (A.submatrix (fun i : Fin m => i.castSucc.succ)
        (fun j : Fin m => j.castSucc.succ)).det ∣
      (A.submatrix Fin.succ Fin.succ).det *
          (A.submatrix Fin.castSucc Fin.castSucc).det -
        (A.submatrix Fin.succ Fin.castSucc).det *
          (A.submatrix Fin.castSucc Fin.succ).det := by
  rw [← Shields.desnanot_jacobi A]
  exact dvd_mul_left _ _

end SkewCornerDescent.Matrix
