/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicClosureWindows
import SkewCornerDescent.FinitePeriodicWords

/-!
# The omitted phase at every proper period boundary

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Periodicity of the completed word identifies each proper boundary state with
its actual closure state. The full finite source word is retained. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- Every proper multiple-of-period boundary carries the omitted closure
phase. Positive boundary and strict endpoint bounds exclude truncated subtraction. -/
theorem closureWord_private_boundary {R : Type*} {n : ℕ} [NeZero n]
    (f : ZMod n → R) (S : R) (r b m : ℕ) [NeZero (r * b)]
    (hr : 0 < r) (hm : 0 < m) (hmb : m < b)
    (hp : Function.Periodic (closureWord f S (r * b)) (r : ZMod (r * b))) :
    closureWord f S (r * b) ((r * m - 1 : ℕ) : ZMod (r * b)) = S := by
  have hB : 0 < r * b := Nat.mul_pos hr (by omega)
  have hM : 0 < r * m := Nat.mul_pos hr hm
  have hcast : ((r * m - 1 : ℕ) : ZMod (r * b)) = (m : ZMod (r * b)) * r - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one]
    ring
  have hlast : (-1 : ZMod (r * b)) = ((r * b - 1 : ℕ) : ZMod (r * b)) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self]
    ring
  rw [hcast, hp.nat_mul_sub_eq m, hlast]
  simp only [closureWord, ZMod.val_natCast_of_lt (show r * b - 1 < r * b by omega),
    ↓reduceIte]

/-- A complete source word represented by the actual finite cycle has its
omitted phase at each proper period boundary as well. -/
theorem finiteWord_private_boundary {R : Type*} {n : ℕ} [NeZero n]
    (r b m : ℕ) [NeZero (r * b)] (hr : 0 < r) (hm : 0 < m) (hmb : m < b)
    (word : Fin (r * b - 1) → R) (hlen : n ≤ r * b - 1) (S : R)
    (hword : ∀ i, word i = finiteWordCycle word hlen (i.val : ZMod n))
    (hp : Function.Periodic (closureWord (finiteWordCycle word hlen) S (r * b))
      (r : ZMod (r * b))) :
    word ⟨r * m - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left hmb hr
      have hpos := Nat.mul_pos hr hm
      omega⟩ = S := by
  have hlt := Nat.mul_lt_mul_of_pos_left hmb hr
  have hpos := Nat.mul_pos hr hm
  have hindex : r * m - 1 < r * b - 1 := by omega
  have h := closureWord_private_boundary (finiteWordCycle word hlen) S r b m hr hm hmb hp
  simp only [closureWord, ZMod.val_natCast_of_lt (show r * m - 1 < r * b by omega),
    ite_eq_right (show r * m - 1 ≠ r * b - 1 by omega)] at h
  exact (hword ⟨r * m - 1, hindex⟩).trans h

end SkewCornerDescent.CyclicWindows
