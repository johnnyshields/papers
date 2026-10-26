/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ConsecutiveMatrixWindows
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Complete first-normal finite prefix charge

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every genuine prefix start contributes its full onsite first jet minus its
complete adjacent-pair activity. This is a finite charge expression, not a
definition of a logarithmic coefficient.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The complete first-normal onsite-minus-pair charge at the original prefix
starts. Both diagonal first jets and all adjacent response entries remain. -/
noncomputable def normalFirstPrefixCharge {N : ℕ} {F : Type*} [Field F]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (b : F) (T : ℕ) (hT : T ≤ N - 1) : F :=
  let onsite := fun V : Matrix (Fin 1) (Fin 1) (PowerSeries F) =>
    PowerSeries.coeff 1 (V 0 0) * (PowerSeries.constantCoeff (V 0 0))⁻¹
  let pair := fun V : Matrix (Fin 2) (Fin 2) (PowerSeries F) =>
    PowerSeries.constantCoeff (V 0 (Fin.last 1)) *
      ∏ k, (PowerSeries.constantCoeff (V k k))⁻¹
  (∑ s : Fin T, onsite (contiguousMatrixWindow M 1 ⟨s.val, by have := s.isLt; omega⟩)) -
    b * ∑ s : Fin T, pair (contiguousMatrixWindow M 2 ⟨s.val, by have := s.isLt; omega⟩)

end SkewCornerDescent.Matrix
