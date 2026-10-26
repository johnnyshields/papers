/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalJacobiTrudi

/-!
# The profile cofactor as an original-matrix minor

Formalizes an algebraic part of `shields-2026-skew-corner-descent.tex`, «Corner descent and
repeated inners in skew Schur compositions», in `lem:cofactor` and `eq:corner-intro`.

The complementary beta determinant of a profile is exactly the determinant of the original
Jacobi--Trudi matrix after deleting its top row and last column. Consequently the top-generator
derivative is the signed determinant of that deleted minor. This is the profile-level cofactor
identity; identifying the minor with the geometric interior `X^-`, proving primitivity, and
proving irreducibility over general fields are not formalized here.

Sorry-free.
-/

open scoped Matrix

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The original profile Jacobi--Trudi matrix with its top row and last column deleted. -/
noncomputable def deletedTopRightOriginalMatrix {n : ℕ} (P : Profile n) :
    Matrix (Fin n) (Fin n) actualField :=
  fun i j => originalMatrix P i.succ j.castSucc

/-- The deleted-minor determinant is the embedded complementary beta determinant. -/
theorem det_deletedTopRightOriginalMatrix {n : ℕ} (P : Profile n) :
    (deletedTopRightOriginalMatrix P).det =
      originalMap (betaDet (fun i : Fin n => P.xi i.succ)
        (fun i : Fin n => P.zeta i.castSucc)) := by
  change (Matrix.of fun i j : Fin n =>
      originalMap (hh (P.xi i.succ - P.zeta j.castSucc))).det =
    originalMap ((Matrix.of fun i j : Fin n =>
      hh (P.xi i.succ - P.zeta j.castSucc)).det)
  exact (RingHom.map_det originalMap _).symm

/-- The top-generator derivative is the signed determinant of the original deleted minor.
This is the algebraic cofactor identity at profile Jacobi--Trudi level. -/
theorem generatorDeriv_originalSchur_top_eq_deletedMinor {n : ℕ} (P : Profile n) :
    generatorDeriv P.topVar (originalMap P.schur) =
      (-1 : actualField) ^ n * (deletedTopRightOriginalMatrix P).det := by
  rw [generatorDeriv_originalSchur_top, map_mul, map_pow, map_neg, map_one,
    det_deletedTopRightOriginalMatrix]

/-- The profile cofactor is nonzero, so the top generator genuinely occurs. -/
theorem generatorDeriv_originalSchur_top_ne_zero {n : ℕ} (P : Profile n) :
    generatorDeriv P.topVar (originalMap P.schur) ≠ 0 := by
  rw [generatorDeriv_originalSchur_top_eq_deletedMinor]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · rw [det_deletedTopRightOriginalMatrix]
    intro hzero
    apply Profile.minor_ne_zero P
    exact originalMap_injective (by simpa using hzero)

end SkewCornerDescent.Matrix
