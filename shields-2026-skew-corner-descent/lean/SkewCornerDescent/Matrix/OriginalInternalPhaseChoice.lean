/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalDiscrepancy

/-!
# Uniform first discrepancy of an actual occurrence phase

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
An actual constant-height and constant-response phase either has identical
shifted full incoming profiles, or has one least visible discrepancy degree
uniform over every position, with a genuine nonzero difference attaining it.
The visible discrepancy is produced by original interval recovery.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- An actual constant-height, constant-response occurrence phase either has
identical incoming profiles under the prescribed shift, or has one uniform
least visible discrepancy degree across all its genuine positions. -/
theorem originalInternal_phase_discrepancy_choice {n b : ℕ} (P : Profile n)
    (idx : ZMod b → Fin (originalSelectedCount (hD := hD) P - 1))
    (d : ℕ) (K : ℤ)
    (hheight : ∀ k, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (idx k)) (originalInternalStateIndex P (idx k)) = K)
    (hresponse : ∀ k, c.originalInternalResidue P (idx k) = c.originalInternalResidue P (idx 0))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ choice : Option ℕ, match choice with
    | none => ∀ k, (c.originalInternalEndpointProfiles P (idx k)).1 =
        (c.originalInternalEndpointProfiles P (idx (k + (d : ZMod b)))).1
    | some w => 0 < w ∧ 2 * (w : ℤ) < K ∧
        (∀ k l, l < w → (c.originalInternalEndpointProfiles P (idx k)).1.coeff l =
          (c.originalInternalEndpointProfiles P (idx (k + (d : ZMod b)))).1.coeff l) ∧
        ∃ k, (c.originalInternalEndpointProfiles P (idx k)).1.coeff w -
          (c.originalInternalEndpointProfiles P (idx (k + (d : ZMod b)))).1.coeff w ≠ 0 := by
  classical
  let incoming := fun k => (c.originalInternalEndpointProfiles P (idx k)).1
  by_cases hperiod : ∀ k, incoming k = incoming (k + (d : ZMod b))
  · exact ⟨none, hperiod⟩
  obtain ⟨k, hk⟩ := not_forall.mp hperiod
  obtain ⟨w, _, hbound, _, hη⟩ := c.originalInternal_incoming_difference_visible P
    (idx k) (idx (k + (d : ZMod b)))
    ((hheight k).trans (hheight _).symm) ((hresponse k).trans (hresponse _).symm) hmax hk
  have hex : ∃ w : ℕ, 2 * (w : ℤ) < K ∧
      ∃ k, (incoming k).coeff w ≠ (incoming (k + (d : ZMod b))).coeff w := by
    refine ⟨w, ?_, k, sub_ne_zero.mp hη⟩
    rwa [hheight] at hbound
  let first := Nat.find hex
  have hfirst := Nat.find_spec hex
  change 2 * (first : ℤ) < K ∧
    ∃ k, (incoming k).coeff first ≠ (incoming (k + (d : ZMod b))).coeff first at hfirst
  have hzero (k) : (incoming k).coeff 0 = 1 := by
    simp only [incoming, originalInternalEndpointProfiles,
      c.originalResidueLeftEndpointPolynomial_coeff_zero]
  have hfirstPos : 0 < first := by
    by_contra hn
    have he : first = 0 := by omega
    obtain ⟨k, hk⟩ := hfirst.2
    rw [he, hzero, hzero] at hk
    exact hk rfl
  have hbefore (k : ZMod b) (l : ℕ) (hl : l < first) :
      (incoming k).coeff l = (incoming (k + (d : ZMod b))).coeff l := by
    by_contra hn
    apply Nat.find_min hex hl
    exact ⟨by have := hfirst.1; omega, k, hn⟩
  obtain ⟨k, hk⟩ := hfirst.2
  exact ⟨some first, hfirstPos, hfirst.1, hbefore, k, sub_ne_zero.mpr hk⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
