/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalCrossGradient
import SkewCornerDescent.Matrix.NormalPrefixCycles

/-!
# Actual endpoint-profile cycles and the genuine crossing gradient

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The first complete profile word keeps its genuine positions. The crossing
pair remains the original matrix entry to the next physical state; a
proved full outgoing-profile period identifies only its endpoint profile
with the cyclic successor. No cyclic inverse is substituted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual position of a cyclic letter inside the full original internal word. -/
def originalInternalCycleIndex {n T : ℕ} [NeZero T] (P : Profile n)
    (hT : T ≤ originalSelectedCount (hD := hD) P - 1) (z : ZMod T) :
    Fin (originalSelectedCount (hD := hD) P - 1) :=
  ⟨z.val, (ZMod.val_lt z).trans_le hT⟩

/-- Both complete actual endpoint polynomials in the first full internal period. -/
noncomputable def originalInternalEndpointCycle {n T : ℕ} [NeZero T] (P : Profile n)
    (hT : T ≤ originalSelectedCount (hD := hD) P - 1) :
    ZMod T → Polynomial (OtherField c.top) × Polynomial (OtherField c.top) :=
  finiteWordCycle (c.originalInternalEndpointProfiles P) hT

/-- The actual crossing pair gradient uses the full outgoing-profile period
only to identify its successor. Its matrix entry is never wrapped to column zero. -/
theorem originalInternal_cyclic_cross_gradient {n T : ℕ} [NeZero T]
    (P : Profile n) (hT : T ≤ originalSelectedCount (hD := hD) P - 1 - 1)
    (H : ℕ+) (hH : c.top < H) (k : ℕ)
    (hp : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1), j.val = i.val + T →
      (c.originalInternalEndpointProfiles P i).2 = (c.originalInternalEndpointProfiles P j).2)
    (hdegree : ∀ z : ZMod T, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (originalInternalCycleIndex P (by omega) z))
      (originalInternalStateIndex P ⟨z.val + 1, by have := ZMod.val_lt z; omega⟩) -
        (H : ℤ) = (k : ℤ))
    (hbound : ∀ i : Fin (originalSelectedCount (hD := hD) P - 1),
      (k : ℤ) ≤ originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i)) (z : ZMod T) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (PowerSeries.constantCoeff
        (normalAdjacentCycle ((c.originalInternalResponseMatrix P).map c.normalSeries) hT z)) =
      ((c.originalInternalEndpointCycle P (by omega) z).1 *
        (c.originalInternalEndpointCycle P (by omega) (z+1)).2).coeff k := by
  let hlen : T ≤ originalSelectedCount (hD := hD) P - 1 := by omega
  let i := originalInternalCycleIndex P hlen z
  let j : Fin (originalSelectedCount (hD := hD) P - 1) :=
    ⟨z.val+1, by have := ZMod.val_lt z; omega⟩
  have hr := finiteWordCycle_eq
    (fun i => (c.originalInternalEndpointProfiles P i).2) hlen hp j
  have hj : (j.val : ZMod T) = z+1 := by
    simp only [j, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [hj] at hr
  change (c.originalInternalEndpointProfiles P j).2 =
    (c.originalInternalEndpointCycle P hlen (z+1)).2 at hr
  change residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
    (PowerSeries.constantCoeff (c.normalSeries (c.originalInternalResponseMatrix P i j))) = _
  rw [c.normalSeries_constant_apply,
    c.originalInternal_cross_residue_gradient P i j (by change z.val ≤ z.val+1; omega)
      H hH k (hdegree z) (hbound i) (hbound j), hr]
  rfl

/-- Constant actual local heights supply the resolving degree of every
genuine cyclic pair, including the crossing pair through the next real state. -/
theorem originalInternal_cyclic_resolving_cross_gradient {n T : ℕ} [NeZero T]
    (P : Profile n) (hT : T ≤ originalSelectedCount (hD := hD) P - 1 - 1)
    (H : ℕ+) (hH : c.top < H) (K w : ℕ) (hw : 2 * w ≤ K)
    (hresolve : (H : ℤ) = 2 * (K : ℤ) - (c.top : ℤ) - 2 * (w : ℤ))
    (hp : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1), j.val = i.val + T →
      (c.originalInternalEndpointProfiles P i).2 = (c.originalInternalEndpointProfiles P j).2)
    (hheight : ∀ i : Fin (originalSelectedCount (hD := hD) P - 1),
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) = (K : ℤ))
    (z : ZMod T) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (PowerSeries.constantCoeff
        (normalAdjacentCycle ((c.originalInternalResponseMatrix P).map c.normalSeries) hT z)) =
      ((c.originalInternalEndpointCycle P (by omega) z).1 *
        (c.originalInternalEndpointCycle P (by omega) (z+1)).2).coeff (2*w) := by
  apply c.originalInternal_cyclic_cross_gradient P hT H hH (2*w) hp
  · intro z
    rw [c.originalInternal_adjacent_distance P _ _ rfl, hheight, hheight, hresolve]
    push_cast
    ring
  · intro i
    rw [hheight]
    exact_mod_cast hw

end SkewCornerDescent.Matrix.SelectedCoordinate
