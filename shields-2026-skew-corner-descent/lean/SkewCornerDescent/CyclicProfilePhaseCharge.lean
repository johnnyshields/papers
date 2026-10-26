/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.CyclicPhaseIndex
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Complete directed profile charges by actual occurrence phase

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The genuine mixed-radix equivalence retains every directed position.
Only height and scalar weight use their proved smaller periods; full
profile values remain at their actual shifted cyclic positions. Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows
open scoped BigOperators

/-- A directed Laurent profile charge splits over all genuine occurrence
phases. Heights and weights use only their proved residue periods; the
profiles themselves are never replaced by a smaller-period word. -/
theorem cyclic_profile_charge_phases {B : ℕ} [NeZero B] {R : Type*} [CommRing R]
    (b r d : ℕ) [NeZero b] [NeZero r]
    (e : ZMod (b * r) ≃+* ZMod B)
    (profile : ZMod B → Polynomial R × Polynomial R)
    (height : ZMod B → ℤ) (weight : ZMod B → R)
    (hheight : Function.Periodic height (r : ZMod B))
    (hweight : Function.Periodic weight (r : ZMod B)) (J : ℤ) :
    (∑ x : ZMod B,
      (((profile x).1 * (profile (x + ((d * r : ℕ) : ZMod B))).2 -
        (profile x).1 * (profile x).2).toLaurent).coeff (height x - J) * weight x) =
      ∑ i : Fin r,
        (∑ k : ZMod b,
          (((profile (e (phaseCycleEquiv b r (i,k)))).1 *
              (profile (e (phaseCycleEquiv b r (i,k + (d : ZMod b))))).2 -
            (profile (e (phaseCycleEquiv b r (i,k)))).1 *
              (profile (e (phaseCycleEquiv b r (i,k)))).2).toLaurent).coeff
            (height (i.val : ZMod B) - J)) * weight (i.val : ZMod B) := by
  classical
  let charge := fun x : ZMod B =>
    (((profile x).1 * (profile (x + ((d * r : ℕ) : ZMod B))).2 -
      (profile x).1 * (profile x).2).toLaurent).coeff (height x - J) * weight x
  have hsum : (∑ x : ZMod B, charge x) =
      ∑ i : Fin r, ∑ k : ZMod b, charge (e (phaseCycleEquiv b r (i,k))) := by
    have he := Equiv.sum_comp ((phaseCycleEquiv b r).trans e.toEquiv) charge
    rw [Fintype.sum_prod_type] at he
    exact he.symm
  change (∑ x : ZMod B, charge x) = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hshift : e (phaseCycleEquiv b r (i,k + (d : ZMod b))) =
      e (phaseCycleEquiv b r (i,k)) + ((d * r : ℕ) : ZMod B) := by
    rw [phaseCycleEquiv_shift, map_add, map_natCast]
  dsimp only [charge]
  have hh : height (e (phaseCycleEquiv b r (i,k))) = height (i.val : ZMod B) :=
    phaseCycleEquiv_periodic_map b r e.toRingHom height hheight i k
  have hw : weight (e (phaseCycleEquiv b r (i,k))) = weight (i.val : ZMod B) :=
    phaseCycleEquiv_periodic_map b r e.toRingHom weight hweight i k
  rw [hh, hw, ← hshift]

end SkewCornerDescent.CyclicWindows
