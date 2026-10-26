/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SchurResponseHessian

/-!
# Dressed endpoint factorization of the full response Hessian

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The eight mixed paths group into two dressed endpoint contractions. Both
orders remain, including the coincident-generator case. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {K m n : Type*} [CommRing K] [Fintype n]

/-- Both orders of the complete inverse Hessian are dressed endpoint
contractions; no matrix entries or off-diagonal paths have been suppressed. -/
theorem schur_hessian_dressed_paths
    (B DB EB : Matrix m n K) (C DC EC : Matrix n m K) (I DP EP : Matrix n n K) :
    -(EB * I * DC) - DB * I * EC + EB * I * DP * I * C +
        DB * I * EP * I * C + B * I * DP * I * EC +
        B * I * EP * I * DC - B * I * DP * I * EP * I * C -
        B * I * EP * I * DP * I * C =
      -(EB - B * I * EP) * I * (DC - DP * I * C) -
        (DB - B * I * DP) * I * (EC - EP * I * C) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul,
    Matrix.mul_assoc]
  abel

end SkewCornerDescent.Matrix
