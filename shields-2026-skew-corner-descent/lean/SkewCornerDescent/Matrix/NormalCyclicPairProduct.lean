/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalPrefixCycles

/-!
# Genuine cyclic inverse pair products

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual successor diagonal and its inverse pair product retain the full overlap word.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The actual successor diagonal transports with the complete overlap period;
uniform inverse-pair products are read on genuine consecutive matrix states. -/
theorem normalDiagonalCycle_inverse_pair {N T B : ℕ} {F : Type*} [Field F]
    [NeZero T] [NeZero B] (M : Matrix (Fin N) (Fin N) (PowerSeries F))
    (hT : T ≤ N - 1)
    (hp : ∀ i j : Fin N, j.val = i.val + T → M i i = M j j)
    (g : ZMod B → F) (hres : ∀ i, PowerSeries.constantCoeff (M i i) = g (i.val : ZMod B))
    (Z : F) (hZ : ∀ s, (g s)⁻¹ * (g (s + 1))⁻¹ = Z) (s : ZMod T) :
    (PowerSeries.constantCoeff (normalDiagonalCycle M (show T ≤ N by omega) s))⁻¹ *
      (PowerSeries.constantCoeff (normalDiagonalCycle M (show T ≤ N by omega) (s + 1)))⁻¹ = Z := by
  let i : Fin N := ⟨s.val, (ZMod.val_lt s).trans_le (by omega)⟩
  let j : Fin N := ⟨s.val + 1, by have := ZMod.val_lt s; omega⟩
  have hi : normalDiagonalCycle M (show T ≤ N by omega) s = M i i := rfl
  have hj : normalDiagonalCycle M (show T ≤ N by omega) (s + 1) = M j j := by
    have he := normalDiagonalCycle_eq M (show T ≤ N by omega) hp j
    simpa only [j, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using he.symm
  rw [hi, hj, hres, hres]
  simpa only [i, j, Nat.cast_add, Nat.cast_one] using hZ (s.val : ZMod B)

end SkewCornerDescent.Matrix
