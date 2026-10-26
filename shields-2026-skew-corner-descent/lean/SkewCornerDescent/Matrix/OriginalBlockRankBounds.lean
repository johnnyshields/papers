/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalInternalLiteralCopy

/-!
# Actual row-rank bounds for component labels

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The canonical component label inequalities are exactly the bounds between
the component’s actual first and last source indices. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing

/-- A component label lies before an index exactly when its first row does. -/
theorem interiorBlock_label_le_iff_first_le {n : ℕ} (P : Profile n) (i j : Fin n) :
    interiorBlock P i ≤ interiorBlock P j ↔ interiorBlockFirst P i ≤ j := by
  have hf := (mem_interiorBlockFiber P i _).mp (interiorBlockFirst_mem P i)
  constructor
  · intro h
    by_contra hn
    have hj : j ≤ interiorBlockFirst P i := (lt_of_not_ge hn).le
    have hm := interiorBlock_mono P hj
    have he : interiorBlock P j = interiorBlock P i := by omega
    exact hn ((mem_interiorBlockFiber_iff P i j).mp ((mem_interiorBlockFiber P i j).mpr he)).1
  · intro h
    simpa only [hf] using interiorBlock_mono P h

/-- An index label lies before a component exactly when its last row follows. -/
theorem interiorBlock_label_le_iff_le_last {n : ℕ} (P : Profile n) (i j : Fin n) :
    interiorBlock P j ≤ interiorBlock P i ↔ j ≤ interiorBlockLast P i := by
  have hl := (mem_interiorBlockFiber P i _).mp (interiorBlockLast_mem P i)
  constructor
  · intro h
    by_contra hn
    have hj : interiorBlockLast P i ≤ j := (lt_of_not_ge hn).le
    have hm := interiorBlock_mono P hj
    have he : interiorBlock P j = interiorBlock P i := by omega
    exact hn ((mem_interiorBlockFiber_iff P i j).mp ((mem_interiorBlockFiber P i j).mpr he)).2
  · intro h
    simpa only [hl] using interiorBlock_mono P h

end SkewCornerDescent.Matrix
