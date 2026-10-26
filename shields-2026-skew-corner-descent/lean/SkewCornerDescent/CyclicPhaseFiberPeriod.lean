/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.CyclicPhaseIndex

/-!
# Coprime occurrence shifts give the actual cyclic phase period

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Invariance under a coprime occurrence shift makes every full phase fiber
constant. The genuine mixed-radix indexing then gives the selected phase
period on the entire cycle, with every occurrence retained. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- A coprime full occurrence shift produces the genuine smaller cyclic phase period. -/
theorem phaseCycle_shift_invariant_periodic {α : Type*} {B : ℕ}
    (b r d : ℕ) [NeZero b] [NeZero r]
    (e : ZMod (b * r) ≃+* ZMod B) (f : ZMod B → α) (hc : Nat.Coprime d b)
    (hp : ∀ (i : Fin r) (k : ZMod b),
      f (e (phaseCycleEquiv b r (i, k))) =
        f (e (phaseCycleEquiv b r (i, k + (d : ZMod b))))) :
    Function.Periodic f (r : ZMod B) := by
  have hconstant (i : Fin r) (k l : ZMod b) :
      f (e (phaseCycleEquiv b r (i,k))) = f (e (phaseCycleEquiv b r (i,l))) := by
    let g := fun k : ZMod b => f (e (phaseCycleEquiv b r (i,k)))
    have hd : Function.Periodic g (d : ZMod b) := fun k => (hp i k).symm
    have hg := zmod_periodic_gcd g hd
    rw [hc.gcd_eq_one, Nat.cast_one] at hg
    have hbase (k : ZMod b) : g k = g 0 := by
      have hk := hg.nsmul k.val 0
      simpa only [zero_add, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] using hk
    exact (hbase k).trans (hbase l).symm
  intro z
  obtain ⟨x, rfl⟩ := e.surjective z
  obtain ⟨⟨i,k⟩, rfl⟩ := (phaseCycleEquiv b r).surjective x
  have hshift : e (phaseCycleEquiv b r (i,k+1)) =
      e (phaseCycleEquiv b r (i,k)) + (r : ZMod B) := by
    have hh := congrArg e (phaseCycleEquiv_shift b r i k 1)
    simpa only [one_mul, Nat.cast_one, map_add, map_natCast] using hh
  rw [← hshift]
  exact hconstant i (k+1) k

end SkewCornerDescent.CyclicWindows
