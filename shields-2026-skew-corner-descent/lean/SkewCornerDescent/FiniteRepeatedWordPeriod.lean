/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FinitePeriodicWords

/-!
# Actual finite phase periods in repeated words

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A finite overlap period dividing the whole source length persists in every
literal repetition, including windows crossing the copy boundary.
Sorry-free.
-/

namespace SkewCornerDescent

/-- A genuine repeated finite word retains every multiple of a source overlap
period dividing the whole source length. The copy-boundary wrap is included. -/
theorem finite_repeated_word_phase {α : Type*} {B C r : ℕ}
    (hB : 0 < B) (hr : 0 < r) (hdiv : r ∣ B)
    (f : Fin B → α) (g : Fin C → α)
    (hrep : ∀ i, g i = f ⟨i.val % B, Nat.mod_lt _ hB⟩)
    (hp : ∀ i j : Fin B, j.val = i.val + r → f i = f j)
    (d : ℕ) (i t : Fin C) (ht : t.val = i.val + d * r) : g t = g i := by
  let : NeZero r := ⟨ne_of_gt hr⟩
  have hlen : r ≤ B := Nat.le_of_dvd hB hdiv
  have hcastB : (B : ZMod r) = 0 := by
    obtain ⟨b, hb⟩ := hdiv
    rw [hb, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hcastmod (k : ℕ) : ((k % B : ℕ) : ZMod r) = (k : ZMod r) := by
    have he := congrArg (fun a : ℕ => (a : ZMod r)) (Nat.mod_add_div k B)
    simp only [Nat.cast_add, Nat.cast_mul, hcastB, zero_mul, add_zero] at he
    exact he
  have hperiod : (t.val : ZMod r) = (i.val : ZMod r) := by
    rw [ht, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
  rw [hrep t, hrep i, finiteWordCycle_eq f hlen hp, finiteWordCycle_eq f hlen hp,
    hcastmod, hcastmod, hperiod]

end SkewCornerDescent
