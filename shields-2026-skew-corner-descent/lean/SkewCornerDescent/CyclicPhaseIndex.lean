/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicWindows
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Genuine mixed-radix response-phase indexing

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The standard finite product equivalence retains every cyclic occurrence.
The original shift acts inside each phase by a finite permutation, without
requiring coprimality or reversing directed pairs. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows
open scoped BigOperators

private theorem phase_fin_equiv_cast {B : ℕ} [NeZero B] (i : Fin B) :
    ZMod.finEquiv B i = (i.val : ZMod B) := by
  cases B with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ B =>
    apply Fin.ext
    change i.val = i.val % (B + 1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

private theorem phase_fin_equiv_symm_val {B : ℕ} [NeZero B] (i : ZMod B) :
    ((ZMod.finEquiv B).symm i).val = i.val := by
  cases B with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ B => rfl

/-- The standard mixed-radix indexing separates the actual r phases from
all b occurrences in each phase, without identifying equal response values. -/
def phaseCycleEquiv (b r : ℕ) [NeZero b] [NeZero r] :
    Fin r × ZMod b ≃ ZMod (b * r) :=
  (Equiv.prodCongr (Equiv.refl (Fin r)) (ZMod.finEquiv b).symm.toEquiv).trans
    ((Equiv.prodComm (Fin r) (Fin b)).trans
      (finProdFinEquiv.trans (ZMod.finEquiv (b * r)).toEquiv))

/-- A phase position is its genuine mixed-radix cyclic index. -/
theorem phaseCycleEquiv_apply (b r : ℕ) [NeZero b] [NeZero r]
    (i : Fin r) (k : ZMod b) :
    phaseCycleEquiv b r (i,k) = (i.val : ZMod (b * r)) +
      (r : ZMod (b * r)) * (k.val : ZMod (b * r)) := by
  change ZMod.finEquiv (b * r)
    (finProdFinEquiv ((ZMod.finEquiv b).symm k,i)) = _
  rw [phase_fin_equiv_cast]
  change ((i.val + r * ((ZMod.finEquiv b).symm k).val : ℕ) : ZMod (b * r)) = _
  rw [phase_fin_equiv_symm_val]
  push_cast
  rfl

/-- The actual shift d*r acts inside each phase by the permutation k↦k+d.
There is no coprimality assumption and no directed edge is reversed. -/
theorem phaseCycleEquiv_shift (b r : ℕ) [NeZero b] [NeZero r]
    (i : Fin r) (k : ZMod b) (d : ℕ) :
    phaseCycleEquiv b r (i,k + (d : ZMod b)) =
      phaseCycleEquiv b r (i,k) + ((d * r : ℕ) : ZMod (b * r)) := by
  have hzero : (b : ZMod (b * r)) * (r : ZMod (b * r)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_self]
  have hmod (s : ℕ) : (r : ZMod (b * r)) * ((s % b : ℕ) : ZMod (b * r)) =
      (r : ZMod (b * r)) * (s : ZMod (b * r)) := by
    have he := congrArg (fun n : ℕ => (n : ZMod (b * r)) * (r : ZMod (b * r)))
      (Nat.mod_add_div s b)
    push_cast at he
    have hz : ((b : ZMod (b * r)) * (s / b : ZMod (b * r))) * (r : ZMod (b * r)) = 0 := by
      calc
        _ = (s / b : ZMod (b * r)) * ((b : ZMod (b * r)) * (r : ZMod (b * r))) := by ring
        _ = 0 := by rw [hzero, mul_zero]
    rw [add_mul, hz, add_zero] at he
    simpa only [mul_comm] using he
  have hk : k + (d : ZMod b) = ((k.val + d : ℕ) : ZMod b) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [phaseCycleEquiv_apply, phaseCycleEquiv_apply, hk, ZMod.val_natCast, hmod]
  push_cast
  ring

/-- Every actual response phase is constant on its full occurrence fiber. -/
theorem phaseCycleEquiv_periodic {α : Type*} (b r : ℕ) [NeZero b] [NeZero r]
    (f : ZMod (b * r) → α) (hp : Function.Periodic f (r : ZMod (b * r)))
    (i : Fin r) (k : ZMod b) :
    f (phaseCycleEquiv b r (i,k)) = f (i.val : ZMod (b * r)) := by
  rw [phaseCycleEquiv_apply]
  have he := (hp.nsmul k.val) (i.val : ZMod (b * r))
  simpa only [nsmul_eq_mul, mul_comm] using he

/-- A transported modulus keeps every genuine periodic phase constant.
The ring map preserves the original integer shift and phase label. -/
theorem phaseCycleEquiv_periodic_map {B : ℕ} {α : Type*}
    (b r : ℕ) [NeZero b] [NeZero r] (e : ZMod (b * r) →+* ZMod B)
    (f : ZMod B → α) (hp : Function.Periodic f (r : ZMod B))
    (i : Fin r) (k : ZMod b) :
    f (e (phaseCycleEquiv b r (i,k))) = f (i.val : ZMod B) := by
  have hp' : Function.Periodic (fun x : ZMod (b * r) => f (e x)) (r : ZMod (b * r)) := by
    intro x
    change f (e (x + (r : ZMod (b * r)))) = f (e x)
    rw [map_add, map_natCast]
    exact hp _
  simpa only [map_natCast] using phaseCycleEquiv_periodic b r (fun x => f (e x)) hp' i k

/-- All cyclic positions occur exactly once in the phase decomposition. -/
theorem sum_phaseCycleEquiv {R : Type*} [AddCommMonoid R]
    (b r : ℕ) [NeZero b] [NeZero r] (f : ZMod (b * r) → R) :
    (∑ s, f s) = ∑ i : Fin r, ∑ k : ZMod b, f (phaseCycleEquiv b r (i,k)) := by
  have he := Equiv.sum_comp (phaseCycleEquiv b r) f
  rw [Fintype.sum_prod_type] at he
  exact he.symm

end SkewCornerDescent.CyclicWindows
