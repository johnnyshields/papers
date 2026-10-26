/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EndpointProfiles
import SkewCornerDescent.Matrix.SchurResponseHessian

/-!
# Actual original-generator Hessian of a full interval response

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The original Jacobi--Trudi entries supply their affine second jets, and the
complete removed inverse supplies all eight mixed paths, including both orders
of its two internal entry derivatives. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Every original Jacobi--Trudi generator entry has zero mixed second jet,
including zero entries, literal unit entries and coincident derivatives. -/
theorem generatorDeriv_hh_second (p q : ℕ+) (i : ℤ) :
    generatorDeriv p (generatorDeriv q (originalMap (SkewGluing.hh i))) = 0 := by
  rw [generatorDeriv_hh]
  split_ifs <;> simp

private theorem interval_entry_second_zero {ι κ : Type*} (p q : ℕ+) (index : ι → κ → ℤ) :
    entryDeriv (generatorDeriv p)
      (entryDeriv (generatorDeriv q) (fun i j => originalMap (SkewGluing.hh (index i j)))) = 0 := by
  ext i j
  exact generatorDeriv_hh_second p q (index i j)

/-- The full original interval's mixed generator derivative is the exact
complete eight-path inverse formula. Its affine-entry hypotheses are supplied
by the actual Jacobi--Trudi entries, not carried as assumptions. -/
theorem generatorDeriv_intervalResponse_hessian {ν : Type*} [Fintype ν] [DecidableEq ν]
    (p q : ℕ+) (x y : ℤ) (row col : ν → ℤ) [Invertible (intervalMatrix row col)] :
    generatorDeriv p (generatorDeriv q (intervalResponse x y row col)) =
      let B := intervalIncoming x col
      let C := intervalOutgoing y row
      let P := intervalMatrix row col
      let DB := entryDeriv (generatorDeriv p) B
      let EB := entryDeriv (generatorDeriv q) B
      let DC := entryDeriv (generatorDeriv p) C
      let EC := entryDeriv (generatorDeriv q) C
      let DP := entryDeriv (generatorDeriv p) P
      let EP := entryDeriv (generatorDeriv q) P
      (-(EB * ⅟P * DC) - DB * ⅟P * EC + EB * ⅟P * DP * ⅟P * C +
        DB * ⅟P * EP * ⅟P * C + B * ⅟P * DP * ⅟P * EC +
        B * ⅟P * EP * ⅟P * DC - B * ⅟P * DP * ⅟P * EP * ⅟P * C -
        B * ⅟P * EP * ⅟P * DP * ⅟P * C) () () := by
  have h := entryDeriv_retainedResponse_hessian (generatorDeriv p) (generatorDeriv q)
    (fun _ _ : Unit => originalMap (SkewGluing.hh (x - y)))
    (intervalIncoming x col) (intervalOutgoing y row) (intervalMatrix row col)
    (interval_entry_second_zero p q (fun _ _ => x - y))
    (interval_entry_second_zero p q (fun _ j => x - col j))
    (interval_entry_second_zero p q (fun i _ => row i - y))
    (interval_entry_second_zero p q (fun i j => row i - col j))
  exact congrFun (congrFun h ()) ()

end SkewCornerDescent.Matrix
