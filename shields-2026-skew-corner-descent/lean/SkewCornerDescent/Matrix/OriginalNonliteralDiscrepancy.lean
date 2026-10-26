/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEarlyRecovery
import SkewCornerDescent.Matrix.OriginalProfileProductJets
import SkewCornerDescent.Matrix.OriginalSelectedCoreProfiles

/-!
# First profile discrepancy from nonliteral original geometry

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Complete original interval recovery produces a discrepancy strictly below
half-height for every nonliteral equal-response pair.  Its least positive
degree has opposite nonzero endpoint differences.  The same witness lies
strictly above the selected span whenever both endpoint core profiles agree.
No visible-discrepancy or half-height premise is supplied.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

set_option maxHeartbeats 800000 in
-- Reducing both full interval-equivalence types and the dependent source-core
-- profile arguments requires the larger elaboration limit.
/-- Nonliteral equal-response original intervals have a least visible
nonzero opposite profile difference.  Complete original reconstruction
produces existence below half-height; it is not a discrepancy hypothesis. -/
theorem original_nonliteral_first_profile_difference {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1)
    (i' t' : Fin (originalSelectedCount (hD := hD) Q)) (ht' : t'.val = i'.val + 1)
    (K : ℕ+) (hK : 2 * (c.top : ℕ) < (K : ℕ))
    (hKP : P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t)))) = (K : ℤ))
    (hKQ : Q.xi (originalRowSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q i')))) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q t')))) = (K : ℤ))
    (hmaxP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (hresponse : c.regularResidue (c.originalLocalResponse P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))) =
      c.regularResidue (c.originalLocalResponse Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t'))))
    (hnonliteral :
      let a := originalSelectedEnumeration (hD := hD) P i
      let b := originalSelectedEnumeration (hD := hD) P t
      let a' := originalSelectedEnumeration (hD := hD) Q i'
      let b' := originalSelectedEnumeration (hD := hD) Q t'
      let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
      ¬ ∃ e : OriginalResponseInterval (hD := hD) P (some a) (some b) ≃
          OriginalResponseInterval (hD := hD) Q (some a') (some b'),
        ∀ p, originalResponseRows Q (e p).1.1 = originalResponseRows P p.1.1 + shift ∧
          originalResponseCols Q (e p).1.1 = originalResponseCols P p.1.1 + shift) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    ∃ w : ℕ, 0 < w ∧ 2 * w < (K : ℕ) ∧
      (∀ k < w, (c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff k =
        (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff k) ∧
      (∀ k < w, (c.originalResidueRightEndpointPolynomial P (some a) (some b)).coeff k =
        (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff k) ∧
      (c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff w -
        (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff w ≠ 0 ∧
      (c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff w -
        (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff w =
      -((c.originalResidueRightEndpointPolynomial P (some a) (some b)).coeff w -
        (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff w) ∧
      (c.selectedCoreLeftPolynomial
          (interiorBlockProfile P a.val.val (originalBlockSelected_nonempty P a.val a.property))
          (originalSelectedProfile_schur P a).symm =
        c.selectedCoreLeftPolynomial
          (interiorBlockProfile Q a'.val.val (originalBlockSelected_nonempty Q a'.val a'.property))
          (originalSelectedProfile_schur Q a').symm →
        c.selectedCoreRightPolynomial
          (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
          (originalSelectedProfile_schur P b).symm =
        c.selectedCoreRightPolynomial
          (interiorBlockProfile Q b'.val.val (originalBlockSelected_nonempty Q b'.val b'.property))
          (originalSelectedProfile_schur Q b').symm →
        (c.top : ℕ) < w) := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  have hvis : ∃ w : ℕ, 2 * w < (K : ℕ) ∧
      ((c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff w ≠
        (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff w ∨
      (c.originalResidueRightEndpointPolynomial P (some a) (some b)).coeff w ≠
        (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff w) := by
    by_contra hn
    have hleft (w : ℕ) (hw : 2 * (w : ℤ) < (K : ℤ)) :
        (c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff w =
          (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff w := by
      by_contra he
      exact hn ⟨w, by exact_mod_cast hw, Or.inl he⟩
    have hright (w : ℕ) (hw : 2 * (w : ℤ) < (K : ℤ)) :
        (c.originalResidueRightEndpointPolynomial P (some a) (some b)).coeff w =
          (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff w := by
      by_contra he
      exact hn ⟨w, by exact_mod_cast hw, Or.inr he⟩
    apply hnonliteral
    exact c.original_early_recovery_interval P Q i t ht i' t' ht' (K : ℤ)
      (by exact_mod_cast hK) hKP hKQ hmaxP hmaxQ hleft hright hresponse
  obtain ⟨w, hw, hbound, hleft, hright, hη, hop⟩ :=
    c.original_visible_first_difference P Q (some a) (some b) (some a') (some b')
      K hK hKP hKQ hresponse hvis
  refine ⟨w, hw, hbound, hleft, hright, hη, hop, ?_⟩
  intro hcoresLeft hcoresRight
  exact c.original_profile_discrepancy_gt_top_of_cores P Q a b a' b'
    (original_consecutive_endpoint_label_le P i t ht)
    (original_consecutive_endpoint_label_le Q i' t' ht') hcoresLeft hcoresRight w
    (Or.inl (sub_ne_zero.mp hη))

end SkewCornerDescent.Matrix.SelectedCoordinate
