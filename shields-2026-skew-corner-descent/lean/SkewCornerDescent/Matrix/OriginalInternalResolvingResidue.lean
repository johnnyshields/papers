/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalResolvingJets
import SkewCornerDescent.Matrix.OriginalSelectedCoreWords
import SkewCornerDescent.Matrix.SelectedCorePolynomialGradient
import SkewCornerDescent.Matrix.OriginalNormalResidueCycles

/-!
# Actual resolving slope of a pure-phase onsite residue

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The original interval gradient and matching actual outgoing proper cores
identify the derivative of the onsite residue. The selected-function raw
gradient supplies its normalization, including negative Laurent offsets.
This retains dependence of the onsite residue on the resolving generator.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem laurent_negative {R : Type*} [CommRing R] (p : Polynomial R)
    (w : ℤ) (hw : w < 0) : p.toLaurent.coeff w = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [LaurentPolynomial.support_coeff_toLaurent]
  intro h
  obtain ⟨k, _, he⟩ := Finset.mem_map.mp h
  change (k : ℤ) = w at he
  omega

/-- The proper-core polynomial version of the normalized raw gradient keeps
integer offsets, rather than truncating the negative-offset regime. -/
theorem selected_core_polynomial_laurent_gradient {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (J : ℕ+) :
    c.normalCoefficient *
      ((c.selectedCoreLeftPolynomial P hP * c.selectedCoreRightPolynomial P hP).toLaurent).coeff
        ((c.top : ℤ)-(J : ℤ)) = c.residueMap (pderiv J (cellSchur D hD.1)) := by
  have hcorner : ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate (Fin.last n) 0 =
      c.normalCoefficient := by
    rw [← c.original_profile_top_gradient P, ← c.top_eq_profile P hP, ← hP,
      c.selected_prime_top_partial, c.residue_coefficient_eq_normal]
  have he := c.selected_core_profile_product_gradient P hP J
  rw [hcorner, ← c.selected_core_left_toLaurent P hP,
    ← c.selected_core_right_toLaurent P hP, ← map_mul, ← hP] at he
  exact he

/-- A matching actual outgoing proper core produces the correct resolving
slope of the full onsite residue, with no assumption that this residue is
constant in that generator. Both possible endpoint-offset signs are covered. -/
theorem originalInternal_resolving_residue_gradient {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (H J : ℕ+) (hH : c.top < H)
    (hdegree : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) - (H : ℤ) =
        (c.top : ℤ) - (J : ℤ))
    (hright : c.originalSelectedCoreRight P ⟨i.val + 1, by have := i.isLt; omega⟩ =
      c.originalSelectedCoreRight P ⟨i.val, by have := i.isLt; omega⟩) :
    c.normalCoefficient * residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.originalInternalResidue P i) = c.residueMap (pderiv J (cellSchur D hD.1)) := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let Q := interiorBlockProfile P (E a).val.val
    (originalBlockSelected_nonempty P (E a).val (E a).property)
  have hQ : cellSchur D hD.1 = Q.schur := (originalSelectedProfile_schur P (E a)).symm
  let K := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E a)))) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E b))))
  have hheight : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) = K := by
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))) = K
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  rw [hheight] at hdegree
  have hres : c.originalInternalResidue P i =
      c.regularResidue (c.originalLocalResponse P (some (E a)) (some (E b))) := by
    have he := c.originalInternal_normal_constant P i
    change PowerSeries.constantCoeff
      (c.normalSeries (c.originalInternalResponseMatrix P i i)) = _ at he
    rw [c.originalInternalResponseMatrix_selected_entry P i i,
      c.normalSeries_constant_apply] at he
    exact he.symm
  have hraw := c.selected_core_polynomial_laurent_gradient Q hQ J
  by_cases hj : 0 ≤ (c.top : ℤ)-(J : ℤ)
  · let k := ((c.top : ℤ)-(J : ℤ)).toNat
    have hk : (c.top : ℤ)-(J : ℤ) = (k : ℤ) := (Int.toNat_of_nonneg hj).symm
    have hbound : k ≤ (c.top : ℕ) := by have := J.pos; omega
    have hab : a < b := by change i.val < i.val+1; omega
    have he := c.originalLocalResponse_normal_low_core_jets P (E a) (E b)
      (originalSelectedEnumeration_label_strictMono P hab).le H hH k hbound
      (hdegree.trans hk) 0
    simp only [↓reduceIte, PowerSeries.coeff_zero_eq_constantCoeff,
      c.normalSeries_constant_apply] at he
    rw [← hres] at he
    change residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.originalInternalResidue P i) =
      (c.originalSelectedCoreLeft P a * c.originalSelectedCoreRight P b).coeff k at he
    rw [hright] at he
    rw [he]
    have hcoeff (f : Polynomial (OtherField c.top)) : f.toLaurent.coeff (k : ℤ) = f.coeff k := by
      change (Finsupp.mapDomain (fun z : ℕ => (z : ℤ)) f.toFinsupp.coeff) (k : ℤ) = _
      exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k
    rw [hk, hcoeff] at hraw
    exact hraw
  · have hfull := c.originalLocalResponse_normal_gradient_above_span
      P (some (E a)) (some (E b)) H hH (by change K < (H : ℤ); omega)
    have he := congrArg (PowerSeries.coeff 0) hfull
    rw [residueSeriesGeneratorDeriv_coeff, map_zero,
      PowerSeries.coeff_zero_eq_constantCoeff, c.normalSeries_constant_apply] at he
    rw [← hres] at he
    change residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.originalInternalResidue P i) = 0 at he
    rw [he, mul_zero]
    rw [laurent_negative _ _ (by omega), mul_zero] at hraw
    exact hraw

end SkewCornerDescent.Matrix.SelectedCoordinate
