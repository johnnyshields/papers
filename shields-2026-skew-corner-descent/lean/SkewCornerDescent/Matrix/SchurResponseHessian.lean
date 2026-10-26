/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BlockResponse

/-!
# Complete mixed second derivative of an affine Schur response

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The eight mixed-derivative terms retain both endpoint derivatives, both internal
inverse derivatives, and their two possible orders. No inverse entry is discarded.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {R K m n : Type*} [CommRing R] [CommRing K] [Algebra R K]

/-- The exact mixed second derivative of an affine-entry Schur complement.
The two ordered internal paths remain distinct, including at a coincident
pair of generator derivatives. -/
theorem entryDeriv_retainedResponse_hessian [Fintype n] [DecidableEq n]
    (D E : Derivation R K K) (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n m K) (P : Matrix n n K) [Invertible P]
    (hA : entryDeriv D (entryDeriv E A) = 0)
    (hB : entryDeriv D (entryDeriv E B) = 0)
    (hC : entryDeriv D (entryDeriv E C) = 0)
    (hP : entryDeriv D (entryDeriv E P) = 0) :
    entryDeriv D (entryDeriv E (retainedResponse A B C P)) =
      -(entryDeriv E B * ⅟P * entryDeriv D C) -
        entryDeriv D B * ⅟P * entryDeriv E C +
        entryDeriv E B * ⅟P * entryDeriv D P * ⅟P * C +
        entryDeriv D B * ⅟P * entryDeriv E P * ⅟P * C +
        B * ⅟P * entryDeriv D P * ⅟P * entryDeriv E C +
        B * ⅟P * entryDeriv E P * ⅟P * entryDeriv D C -
        B * ⅟P * entryDeriv D P * ⅟P * entryDeriv E P * ⅟P * C -
        B * ⅟P * entryDeriv E P * ⅟P * entryDeriv D P * ⅟P * C := by
  rw [entryDeriv_retainedResponse]
  simp only [entryDeriv_add, entryDeriv_sub, entryDeriv_mul, entryDeriv_invOf,
    hA, hB, hC, hP, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    zero_sub, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

end SkewCornerDescent.Matrix
