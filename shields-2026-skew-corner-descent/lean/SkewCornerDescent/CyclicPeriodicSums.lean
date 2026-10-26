/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicGapPeriod

/-!
# Balanced periodic response functionals

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete response phases give their exact additive multiplicities. The actual
b:d prefix balance cancels any periodic response functional, with repeated
wraps retained and without requiring the phase to divide the cycle size.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows
open scoped BigOperators

/-- The actual b:d count balance cancels every periodic self-response
functional, not just a particular derivative or one numerical assignment. -/
theorem balanced_periodic_prefix_sums {B : ℕ} [NeZero B] {R : Type*} [AddCommGroup R]
    (f : ZMod B → R) (r : ℕ) (hp : Function.Periodic f (r : ZMod B)) (b d : ℕ) :
    b • windowSum f 1 (d * r) 0 - d • windowSum f 1 (b * r) 0 = 0 := by
  rw [windowSum_of_zmod_period_multiple f r hp,
    windowSum_of_zmod_period_multiple f r hp, smul_smul, smul_smul, Nat.mul_comm b d, sub_self]

end SkewCornerDescent.CyclicWindows
