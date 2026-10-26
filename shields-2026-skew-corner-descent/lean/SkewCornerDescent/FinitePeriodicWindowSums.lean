/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FinitePeriodicWords
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite overlap sums with every cyclic occurrence

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual finite overlap periods produce the window multiplicities and full
period powers, including repeated wraps and empty-window boundaries.
Sorry-free.
-/

namespace SkewCornerDescent
open scoped BigOperators

/-- Full finite windows charge every position in one overlap period once per
window position, including repeated wraps and zero-length windows. -/
theorem finite_periodic_window_sum {α R : Type*} [AddCommMonoid R]
    {L T : ℕ} [NeZero T] (word : Fin L → α) (F : α → R)
    (hT : T ≤ L)
    (hp : ∀ i j : Fin L, j.val = i.val + T → word i = word j)
    (n : ℕ) (hbound : T + n ≤ L + 1) :
    (∑ s : Fin T, ∑ k : Fin n,
      F (word ⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩)) =
      n • ∑ s : Fin T, F (word ⟨s.val, s.isLt.trans_le hT⟩) := by
  classical
  have hcast (s : Fin T) : ZMod.finEquiv T s = (s.val : ZMod T) := by
    cases T with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ T =>
      apply Fin.ext
      change s.val = s.val % (T + 1)
      exact (Nat.mod_eq_of_lt s.isLt).symm
  let f := fun z : ZMod T => F (finiteWordCycle word hT z)
  have hbase : (∑ z : ZMod T, f z) =
      ∑ s : Fin T, F (word ⟨s.val, s.isLt.trans_le hT⟩) := by
    symm
    apply Fintype.sum_equiv (ZMod.finEquiv T).toEquiv
    intro s
    change _ = f (ZMod.finEquiv T s)
    simp [f, hcast, finiteWordCycle, Nat.mod_eq_of_lt s.isLt]
  have hshift (k : Fin n) : (∑ s : Fin T,
      F (word ⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩)) =
      ∑ z : ZMod T, f z := by
    calc
      _ = ∑ z : ZMod T, f (z + (k.val : ZMod T)) := by
        apply Fintype.sum_equiv (ZMod.finEquiv T).toEquiv
        intro s
        change _ = f (ZMod.finEquiv T s + (k.val : ZMod T))
        have he := finiteWordCycle_eq word hT hp
          ⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩
        simpa only [f, hcast, Nat.cast_add] using congrArg F he
      _ = _ := Equiv.sum_comp (Equiv.addRight (k.val : ZMod T)) f
  rw [Finset.sum_comm]
  simp_rw [hshift, hbase]
  simp

/-- A fixed shifted position has the same complete cyclic sum, even after
repeated wraps. The supplied finite word is the source of the periodicity. -/
theorem finite_periodic_shift_sum {α R : Type*} [AddCommGroup R]
    {L T : ℕ} [NeZero T] (word : Fin L → α) (F : α → R)
    (hT : T ≤ L)
    (hp : ∀ i j : Fin L, j.val = i.val + T → word i = word j)
    (k : ℕ) (hbound : T + k ≤ L) :
    (∑ s : Fin T, F (word ⟨s.val + k, by have := s.isLt; omega⟩)) =
      ∑ s : Fin T, F (word ⟨s.val, s.isLt.trans_le hT⟩) := by
  have h := finite_periodic_window_sum word F hT hp (k + 1) (by omega)
  have hprev := finite_periodic_window_sum word F hT hp k (by omega)
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    Finset.sum_add_distrib] at h
  rw [hprev, add_nsmul, one_nsmul] at h
  exact add_left_cancel h

end SkewCornerDescent
