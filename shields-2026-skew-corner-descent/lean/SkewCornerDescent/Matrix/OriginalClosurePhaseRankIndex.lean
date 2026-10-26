/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalClosurePhaseRowGaps

/-!
# Genuine mixed-radix phase positions and physical row-gap periods

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The completed phase index is its actual nonwrapped source position.
Equal physical gaps in each occurrence phase therefore give a real
period on the finite first source copy of the ordinary closure. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A completed occurrence phase has its exact actual mixed-radix source rank. -/
theorem originalClosurePhaseStateIndex_val {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (b r : ℕ) [NeZero b] [NeZero r]
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P)
    (i : Fin r) (k : ZMod b) :
    (originalClosurePhaseStateIndex P Q b r hB hCQ i k).val = i.val + r*k.val := by
  have hi := i.isLt
  have hk := ZMod.val_lt k
  have hbound : i.val + r*k.val < b*r := by nlinarith
  change (ZMod.ringEquivCongr hB.symm (phaseCycleEquiv b r (i,k))).val = _
  rw [phaseCycleEquiv_apply]
  have he : (i.val : ZMod (b*r)) + (r : ZMod (b*r)) * (k.val : ZMod (b*r)) =
      ((i.val + r*k.val : ℕ) : ZMod (b*r)) := by push_cast; rfl
  rw [he, map_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- Phasewise equality becomes a genuine finite period in the actual source ranks. -/
theorem originalClosure_phase_period_of_constant {pn qn : ℕ} {α : Type*}
    (P : Profile pn) (Q : Profile qn) (b r : ℕ) [NeZero b] [NeZero r]
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hB : originalSelectedCount (hD := hD) P = b * r)
    (hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P)
    (f : Fin (originalSelectedCount (hD := hD) Q - 1) → α)
    (hphase : ∀ (i : Fin r) (k l : ZMod b),
      f (originalClosurePhaseStateIndex P Q b r hB hCQ i k) =
        f (originalClosurePhaseStateIndex P Q b r hB hCQ i l))
    (j : Fin (originalSelectedCount (hD := hD) Q - 1))
    (hj : j.val + r < originalSelectedCount (hD := hD) P) :
    f ⟨j.val + r, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = f j := by
  let i : Fin r := ⟨j.val % r, Nat.mod_lt _ (NeZero.pos r)⟩
  have hdiv : j.val/r+1 < b := by
    have he := Nat.mod_add_div j.val r
    have hm := Nat.mod_lt j.val (NeZero.pos r)
    rw [hB] at hj
    by_contra hn
    have hle : b ≤ j.val / r + 1 := by omega
    have hmul := Nat.mul_le_mul_right r hle
    simp only [Nat.mul_comm] at hmul he hj
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hk : j.val/r < b := by omega
  have hvk : ((j.val/r : ℕ) : ZMod b).val = j.val/r := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have hvl : ((j.val/r+1 : ℕ) : ZMod b).val = j.val/r+1 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hdiv]
  have hi0 : originalClosurePhaseStateIndex P Q b r hB hCQ i ((j.val/r : ℕ) : ZMod b) = j := by
    apply Fin.ext
    rw [originalClosurePhaseStateIndex_val, hvk]
    exact Nat.mod_add_div j.val r
  have hi1 : originalClosurePhaseStateIndex P Q b r hB hCQ i
      ((j.val/r+1 : ℕ) : ZMod b) = ⟨j.val+r, by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega⟩ := by
    apply Fin.ext
    rw [originalClosurePhaseStateIndex_val, hvl]
    dsimp only [i]
    have he := Nat.mod_add_div j.val r
    nlinarith
  have h := hphase i ((j.val/r+1 : ℕ) : ZMod b) ((j.val/r : ℕ) : ZMod b)
  simpa only [hi0, hi1] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
