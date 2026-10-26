/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureProfileCycle
import SkewCornerDescent.Matrix.OriginalCrossPrefixCharge

/-!
# Actual directed cyclic cross-minus-self profile charge

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete genuine closure prefix is reindexed together with its actual
profiles, integer heights, and residue inverses. Cyclic profile-word values
retain the real shifted endpoints, never a wrapped matrix column. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire genuine closure prefix is its directed cyclic profile charge.
Actual shifted endpoints, integer heights, and every residue inverse are
transported together; the matrix's wrapped column zero is never substituted. -/
theorem originalClosure_cross_self_cyclic_charge {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (active : OtherField c.top) (m : ℕ) (hm : m < originalSelectedCount (hD := hD) P)
    (J : ℕ+) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    (c.originalInternalResidue Q ⟨originalSelectedCount (hD := hD) P - 1, by
      have := NeZero.pos (originalSelectedCount (hD := hD) P)
      omega⟩ = active) →
    let cycle := finiteWordCycle (c.originalInternalEndpointProfiles Q)
      (show originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) Q - 1 by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega)
    c.originalCrossPrefixCharge Q m J (originalSelectedCount (hD := hD) P) (by omega) -
      c.originalSelfPrefixCharge Q J (originalSelectedCount (hD := hD) P) (by
        have := NeZero.pos (originalSelectedCount (hD := hD) P)
        omega) =
      ∑ s : ZMod (originalSelectedCount (hD := hD) P),
        (((cycle s).1 * (cycle (s + (m : ZMod (originalSelectedCount (hD := hD) P)))).2 -
          (cycle s).1 * (cycle s).2).toLaurent).coeff
            ((c.top : ℤ) + c.originalCompletedGap P ((ZMod.finEquiv _).symm s) - (J : ℤ)) *
          (completeResponseCycle (c.originalInternalResidue P) active s)⁻¹ := by
  obtain ⟨hCQ, hstate⟩ := c.originalClosure_profile_height_residue_cycle P Q z hQ active
  have hBpos := NeZero.pos (originalSelectedCount (hD := hD) P)
  refine ⟨hCQ, ?_⟩
  intro hactive
  have hst := hstate hactive
  dsimp only at hst ⊢
  unfold originalCrossPrefixCharge originalSelfPrefixCharge
  dsimp only
  rw [← Finset.sum_sub_distrib]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv (originalSelectedCount (hD := hD) P)).symm.toEquiv
  intro x
  let s : Fin (originalSelectedCount (hD := hD) P) := (ZMod.finEquiv _).symm x
  let i : Fin (originalSelectedCount (hD := hD) Q - 1) := ⟨s.val, by have := s.isLt; omega⟩
  let j : Fin (originalSelectedCount (hD := hD) Q - 1) := ⟨s.val + m, by have := s.isLt; omega⟩
  have hi : (i.val : ZMod (originalSelectedCount (hD := hD) P)) = x := by
    simp only [i, s, finEquiv_symm_val, ZMod.natCast_zmod_val]
  have hj : (j.val : ZMod (originalSelectedCount (hD := hD) P)) = x + m := by
    simp only [j, s, finEquiv_symm_val, Nat.cast_add, ZMod.natCast_zmod_val]
  obtain ⟨hpi, hKi, hSi⟩ := hst i
  have hpj := (hst j).1
  rw [hi] at hpi hKi hSi
  rw [hj] at hpj
  change _ =
    (((c.originalInternalEndpointProfiles Q i).1 *
      (c.originalInternalEndpointProfiles Q j).2).toLaurent).coeff
        (originalHessenbergDistance (hD := hD) Q
          (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) - (J : ℤ)) *
      (c.originalInternalResidue Q i)⁻¹ -
    (((c.originalInternalEndpointProfiles Q i).1 *
      (c.originalInternalEndpointProfiles Q i).2).toLaurent).coeff
        (originalHessenbergDistance (hD := hD) Q
          (originalInternalStateIndex Q i) (originalInternalStateIndex Q i) - (J : ℤ)) *
      (c.originalInternalResidue Q i)⁻¹
  rw [hpi, hpj, hKi, hSi]
  simp only [map_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
