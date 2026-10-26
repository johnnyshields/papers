/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FinitePeriodicWords

/-!
# Exact phases in a source prefix followed by its whole word

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A source overlap period dividing the prefix length persists through the full
splice. Every finite position is retained before passing to a period class.
Sorry-free.
-/

namespace SkewCornerDescent

/-- Prefixing a source by a whole number of its overlap periods preserves
that phase at every index of the complete spliced word. -/
theorem finite_spliced_word_phase {α : Type*} {B C T r : ℕ}
    (hC : C = B + T) (hT : T ≤ B) (hr : 0 < r) (hlen : r ≤ B) (hdiv : r ∣ T)
    (f : Fin B → α) (g : Fin C → α)
    (hword : ∀ i, g i = if hi : i.val < T then f ⟨i.val, hi.trans_le hT⟩
      else f ⟨i.val - T, by have := i.isLt; omega⟩)
    (hp : ∀ i j : Fin B, j.val = i.val + r → f i = f j)
    (d : ℕ) (i t : Fin C) (ht : t.val = i.val + d * r) : g t = g i := by
  let : NeZero r := ⟨ne_of_gt hr⟩
  have hcastT : (T : ZMod r) = 0 := by
    obtain ⟨k, hk⟩ := hdiv
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hcycle (j : Fin C) : g j = finiteWordCycle (n := r) f hlen (j.val : ZMod r) := by
    rw [hword j]
    by_cases hj : j.val < T
    · rw [dite_eq_left hj, finiteWordCycle_eq f hlen hp]
    · rw [dite_eq_right hj, finiteWordCycle_eq f hlen hp,
        Nat.cast_sub (le_of_not_gt hj), hcastT, sub_zero]
  rw [hcycle t, hcycle i, ht, Nat.cast_add, Nat.cast_mul,
    ZMod.natCast_self, mul_zero, add_zero]

end SkewCornerDescent
