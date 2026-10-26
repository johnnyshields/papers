/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicWindows
import Mathlib.Order.Interval.Finset.Fin

/-!
# Literal finite intervals inside cyclic windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The equivalence retains every indexed position, including equal response values.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- The finite cyclic equivalence sends a literal finite index to its residue class. -/
theorem finEquiv_eq_natCast {B : ℕ} [NeZero B] (k : Fin B) :
    ZMod.finEquiv B k = (k.val : ZMod B) := by
  cases B with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ B => exact (Fin.cast_val_eq_self k).symm

/-- A nonwrapping interval is exactly its full cyclic positional window, not a set
of distinct values. Both endpoints occur in the sum. -/
theorem windowSum_finite_interval {B : ℕ} [NeZero B] {R : Type*} [AddCommMonoid R]
    (g : Fin B → R) (i j : Fin B) (hij : i ≤ j) :
    windowSum (fun z => g ((ZMod.finEquiv B).symm z)) 1 (j.val - i.val + 1)
      (i.val : ZMod B) = ∑ k ∈ Finset.Icc i j, g k := by
  classical
  unfold windowSum
  symm
  apply Finset.sum_bij (fun k _ => k.val - i.val)
  · intro k hk
    obtain ⟨hik, hkj⟩ := Finset.mem_Icc.mp hk
    apply Finset.mem_range.mpr
    change i.val ≤ k.val at hik
    change k.val ≤ j.val at hkj
    omega
  · intro k hk l hl he
    obtain ⟨hik, _⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hil, _⟩ := Finset.mem_Icc.mp hl
    apply Fin.ext
    change i.val ≤ k.val at hik
    change i.val ≤ l.val at hil
    omega
  · intro a ha
    have ha' := Finset.mem_range.mp ha
    have hi := i.isLt
    have hj := j.isLt
    change i.val ≤ j.val at hij
    let k : Fin B := ⟨i.val + a, by omega⟩
    refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · change i.val ≤ i.val + a
      omega
    · change i.val + a ≤ j.val
      omega
    · dsimp [k]
      omega
  · intro k hk
    obtain ⟨hik, _⟩ := Finset.mem_Icc.mp hk
    have he : (i.val : ZMod B) + (k.val - i.val) • (1 : ZMod B) =
        ZMod.finEquiv B k := by
      rw [finEquiv_eq_natCast, nsmul_eq_mul, mul_one, ← Nat.cast_add]
      congr 1
      change i.val ≤ k.val at hik
      omega
    rw [he]
    exact congrArg g ((ZMod.finEquiv B).symm_apply_apply k).symm

/-- A window starting at the literal final position includes that occurrence and then
continues at the literal first position. Repeated values are never merged. -/
theorem windowSum_finite_wrap {B : ℕ} [NeZero B] {R : Type*} [AddCommMonoid R]
    (g : Fin B → R) (last : Fin B) (hlast : last.val + 1 = B) (length : ℕ) :
    windowSum (fun z => g ((ZMod.finEquiv B).symm z)) 1 (length + 1)
      (last.val : ZMod B) = g last +
        windowSum (fun z => g ((ZMod.finEquiv B).symm z)) 1 length 0 := by
  have hwrap : (last.val : ZMod B) + 1 = 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add, hlast, ZMod.natCast_self]
  have hfirst : windowSum (fun z => g ((ZMod.finEquiv B).symm z)) 1 1
      (last.val : ZMod B) = g last := by
    unfold windowSum
    simp only [Finset.range_one, Finset.sum_singleton, zero_nsmul, add_zero]
    rw [← finEquiv_eq_natCast, RingEquiv.symm_apply_apply]
  rw [Nat.add_comm length 1, windowSum_add, hfirst]
  simp only [one_nsmul, hwrap]

end SkewCornerDescent.CyclicWindows
