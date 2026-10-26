/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalCyclicProfiles
import SkewCornerDescent.Matrix.OriginalBinaryCrossEnergy
import SkewCornerDescent.Matrix.OriginalNormalResidueCycles

/-!
# Complete binary energy on an actual internal profile cycle

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
Actual internal indices supply both selected endpoints, all complete
profiles and their interval heights. Equal onsite residues supply the
self-product jets internally before the binary energy identity is used.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing BinaryTransitions
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete cross-minus-self energy of the actual internal endpoint cycle,
with all self jets produced from the actual common response and local heights. -/
theorem originalInternal_cyclic_binary_energy {n T : ℕ} [NeZero T]
    (P : Profile n) (hT : T ≤ originalSelectedCount (hD := hD) P - 1)
    (K w : ℕ) (hw : 0 < w) (hhigh : (c.top : ℕ) + w < K)
    (hheight : ∀ z : ZMod T, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (originalInternalCycleIndex P hT z))
      (originalInternalStateIndex P (originalInternalCycleIndex P hT z)) = (K : ℤ))
    (hresponse : ∀ z, c.originalInternalResidue P (originalInternalCycleIndex P hT z) =
      c.originalInternalResidue P (originalInternalCycleIndex P hT 0))
    (hmatch : ∀ z k, k < w →
      (c.originalInternalEndpointCycle P hT z).1.coeff k =
        (c.originalInternalEndpointCycle P hT (z + 1)).1.coeff k)
    (η : OtherField c.top) (bits : ZMod T → Bool)
    (hbits : ∀ z, (c.originalInternalEndpointCycle P hT z).1.coeff w -
      (c.originalInternalEndpointCycle P hT 0).1.coeff w = if bits z then η else 0) :
    ∑ z, ((c.originalInternalEndpointCycle P hT z).1 *
        (c.originalInternalEndpointCycle P hT (z+1)).2 -
      (c.originalInternalEndpointCycle P hT z).1 *
        (c.originalInternalEndpointCycle P hT z).2).coeff (2*w) =
      (1/2 : OtherField c.top) * η^2 * (transitionCount bits 1 : OtherField c.top) := by
  let idx := originalInternalCycleIndex P hT
  let a := fun z : ZMod T => (⟨(idx z).val, by have := (idx z).isLt; omega⟩ :
    Fin (originalSelectedCount (hD := hD) P))
  let b := fun z : ZMod T => (⟨(idx z).val+1, by have := (idx z).isLt; omega⟩ :
    Fin (originalSelectedCount (hD := hD) P))
  let E := originalSelectedEnumeration (hD := hD) P
  have hk (z : ZMod T) : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E (a z))))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E (b z))))) = (K : ℤ) := by
    have he := hheight z
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P (a z).succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P (b z).castSucc))) = _ at he
    rwa [originalHessenbergRows_succ, originalHessenbergCols_castSucc] at he
  have hr (z : ZMod T) : c.regularResidue
      (c.originalLocalResponse P (some (E (a z))) (some (E (b z)))) =
      c.originalInternalResidue P (idx z) := by
    have he := c.originalInternal_normal_constant P (idx z)
    change PowerSeries.constantCoeff (c.normalSeries
      (c.originalInternalResponseMatrix P (idx z) (idx z))) = _ at he
    rwa [c.originalInternalResponseMatrix_selected_entry P (idx z) (idx z),
      c.normalSeries_constant_apply] at he
  have hs (z : ZMod T) : c.regularResidue
      (c.originalLocalResponse P (some (E (a z))) (some (E (b z)))) =
      c.regularResidue (c.originalLocalResponse P (some (E (a 0))) (some (E (b 0)))) :=
    (hr z).trans ((hresponse z).trans (hr 0).symm)
  have hl (z : ZMod T) : c.originalResidueLeftEndpointPolynomial P
      (some (E (a z))) (some (E (b z))) =
      (c.originalInternalEndpointCycle P hT z).1 := rfl
  have hrr (z : ZMod T) : c.originalResidueRightEndpointPolynomial P
      (some (E (a z))) (some (E (b z))) =
      (c.originalInternalEndpointCycle P hT z).2 := rfl
  have he := c.original_cross_profile_binary_energy P
    (fun z => some (E (a z))) (fun z => some (E (b z))) 0 K w hw hhigh hk hs
    (fun z l hlw => by rw [hl, hl]; exact hmatch z l hlw) η bits
    (fun z => by rw [hl, hl]; exact hbits z)
  simpa only [hl, hrr] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
