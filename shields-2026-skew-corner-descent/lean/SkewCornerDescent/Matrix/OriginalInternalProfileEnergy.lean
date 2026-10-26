/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCrossProfileEnergy
import SkewCornerDescent.Matrix.OriginalInternalHeights

/-!
# Full energy and lower jets of actual internal profile families

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual original height and residue interfaces supply the family contracts.
The genuine source height floor derives the fresh-generator margin from the
half-height discrepancy bound, then the complete lower and energy jets follow
from produced equal-response self jets. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete actual internal profiles have vanishing earlier cross jets and
the exact directed half-square energy. The real source height floor supplies
the fresh-generator margin from the paper's half-height discrepancy bound. -/
theorem originalInternal_profile_energy_jets {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Profile n) (idx : ι → Fin (originalSelectedCount (hD := hD) P - 1))
    (σ : Equiv.Perm ι) (i₀ : ι) (K w : ℕ) (hw : 0 < w) (hhalf : 2 * w < K)
    (hheight : ∀ i, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (idx i)) (originalInternalStateIndex P (idx i)) = (K : ℤ))
    (hS : ∀ i, c.originalInternalResidue P (idx i) = c.originalInternalResidue P (idx i₀))
    (hmatch : ∀ i k, k < w →
      (c.originalInternalEndpointProfiles P (idx i)).1.coeff k =
      (c.originalInternalEndpointProfiles P (idx (σ i))).1.coeff k) :
    let f := fun i => (c.originalInternalEndpointProfiles P (idx i)).1
    let g := fun i => (c.originalInternalEndpointProfiles P (idx i)).2
    (∀ k, k < 2 * w → ∑ i, (f i * g (σ i) - f i * g i).coeff k = 0) ∧
      (∑ i, (f i * g (σ i) - f i * g i).coeff (2 * w)) =
        (1/2 : OtherField c.top) * ∑ i, ((f i).coeff w - (f (σ i)).coeff w)^2 := by
  have hN := c.originalInternal_height_gt_twice_top P (idx i₀)
  rw [hheight i₀] at hN
  have hN' : 2 * (c.top : ℕ) < K := by exact_mod_cast hN
  have hhigh : (c.top : ℕ) + w < K := by omega
  let E := originalSelectedEnumeration (hD := hD) P
  let b := fun i => some (E ⟨(idx i).val, by have := (idx i).isLt; omega⟩)
  let d := fun i => some (E ⟨(idx i).val + 1, by have := (idx i).isLt; omega⟩)
  have hgeom (i : ι) : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (idx i)) (originalInternalStateIndex P (idx i)) =
      P.xi (originalRowSplitEquiv P (.inl (b i))) -
        P.zeta (originalColSplitEquiv P (.inl (d i))) := by
    let a : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨(idx i).val, by have := (idx i).isLt; omega⟩
    let q : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨(idx i).val + 1, by have := (idx i).isLt; omega⟩
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P q.castSucc))) = _
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hK : ∀ i, P.xi (originalRowSplitEquiv P (.inl (b i))) -
      P.zeta (originalColSplitEquiv P (.inl (d i))) = (K : ℤ) :=
    fun i => (hgeom i).symm.trans (hheight i)
  have hres (i : ι) : c.regularResidue (c.originalLocalResponse P (b i) (d i)) =
      c.originalInternalResidue P (idx i) := by
    have he := c.originalInternalResponseMatrix_selected_entry P (idx i) (idx i)
    change c.originalInternalResponseMatrix P (idx i) (idx i) =
      c.originalLocalResponse P (b i) (d i) at he
    rw [← he]
    rfl
  have hS' : ∀ i, c.regularResidue (c.originalLocalResponse P (b i) (d i)) =
      c.regularResidue (c.originalLocalResponse P (b i₀) (d i₀)) := by
    intro i
    rw [hres, hres]
    exact hS i
  have hm : ∀ i k, k < w →
      (c.originalResidueLeftEndpointPolynomial P (b i) (d i)).coeff k =
      (c.originalResidueLeftEndpointPolynomial P (b (σ i)) (d (σ i))).coeff k := by
    simpa only [originalInternalEndpointProfiles, b, d, E] using hmatch
  constructor
  · intro k hk
    have he := c.original_cross_profile_sum_low P b d σ i₀ K w hw hhigh hK hS' hm k hk
    simpa only [originalInternalEndpointProfiles, b, d, E] using he
  · have he := c.original_cross_profile_energy P b d σ i₀ K w hw hhigh hK hS' hm
    simpa only [originalInternalEndpointProfiles, b, d, E] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
