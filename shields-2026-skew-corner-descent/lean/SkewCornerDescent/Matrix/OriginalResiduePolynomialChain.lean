/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalResidue
import SkewCornerDescent.Matrix.ResidueGeneratorDerivation
import SkewCornerDescent.Matrix.SelectedCorePolynomialGradient

/-!
# Actual raw and chart derivatives of polynomial residues

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every surviving original generator has its genuine coefficient-field derivative.
The selected variable's dependent residue contributes the complete raw selected
partial correction, including when the surviving generator lies below the top.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Coefficient-field differentiation at fixed selected normal coordinate.
The selected generator itself has zero chart direction. -/
noncomputable def residueChartDeriv (N j : ℕ+) :
    Derivation ℚ (OtherField N) (OtherField N) :=
  if h : j = N then 0 else residueGeneratorDeriv N ⟨j, h⟩

namespace SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

private theorem residue_polynomial_C (a : ℚ) :
    c.residueMap (C a) = algebraMap (OtherPolynomial c.top) (OtherField c.top) (C a) := by
  have h : c.residueMap.comp (C : ℚ →+* Lambda) =
      (algebraMap (OtherPolynomial c.top) (OtherField c.top)).comp
        (C : ℚ →+* OtherPolynomial c.top) := RingHom.ext_rat _ _
  exact RingHom.congr_fun h a

private theorem residue_surviving_variable (j : ℕ+) (hj : j ≠ c.top) (k : ℕ+)
    (hk : k ≠ c.top) :
    residueGeneratorDeriv c.top ⟨j, hj⟩ (c.residueMap (X k)) =
      c.residueMap (pderiv j (X k)) := by
  rw [c.residueMap_other k hk, residueGeneratorDeriv_algebraMap]
  by_cases he : k = j
  · subst k
    simp
  · have hs : (⟨k, hk⟩ : {k : ℕ+ // k ≠ c.top}) ≠ ⟨j, hj⟩ :=
      fun h => he (congrArg Subtype.val h)
    rw [pderiv_X_of_ne hs, pderiv_X_of_ne he, map_zero, map_zero]

private theorem residue_polynomial_chain_with_selected_value
    (j : ℕ+) (hj : j ≠ c.top) (κ : OtherField c.top)
    (hκ : residueGeneratorDeriv c.top ⟨j, hj⟩ (c.residueMap (X c.top)) = κ) (f : Lambda) :
    residueGeneratorDeriv c.top ⟨j, hj⟩ (c.residueMap f) =
      c.residueMap (pderiv j f) + κ * c.residueMap (pderiv c.top f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp only [pderiv_C, map_zero, mul_zero, add_zero]
    rw [c.residue_polynomial_C, residueGeneratorDeriv_algebraMap, pderiv_C, map_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    ring
  | mul_X p k hp =>
    have hX : residueGeneratorDeriv c.top ⟨j, hj⟩ (c.residueMap (X k)) =
        c.residueMap (pderiv j (X k)) + κ * c.residueMap (pderiv c.top (X k)) := by
      by_cases hk : k = c.top
      · subst k
        rw [hκ]
        simp [pderiv_X_of_ne hj.symm]
      · rw [c.residue_surviving_variable j hj k hk, pderiv_X_of_ne hk,
          map_zero, mul_zero, add_zero]
    simp only [map_mul, map_add, Derivation.leibniz, smul_eq_mul, hp, hX]
    ring

/-- The actual coefficient-field derivative equals the raw partial minus its
selected-coordinate contribution. The selected residue is not treated as an
independent field variable, even for generators below the selected top. -/
theorem original_residue_polynomial_chain (j : ℕ+) (hj : j ≠ c.top) (f : Lambda) :
    residueGeneratorDeriv c.top ⟨j, hj⟩ (c.residueMap f) =
      c.residueMap (pderiv j f) - c.normalCoefficient⁻¹ * c.residueMap (pderiv c.top f) *
        c.residueMap (pderiv j (cellSchur D hD.1)) := by
  let κ := residueGeneratorDeriv c.top ⟨j, hj⟩ (c.residueMap (X c.top))
  have hgen := c.residue_polynomial_chain_with_selected_value j hj κ rfl
  have ha := c.normalCoefficient_ne_zero
  have hψ : c.residueMap (cellSchur D hD.1) = 0 :=
    (c.residueMap_eq_zero_iff _).mpr dvd_rfl
  have hψder : pderiv c.top (cellSchur D hD.1) = c.coefficient := c.selected_prime_top_partial
  have h0 := hgen (cellSchur D hD.1)
  rw [hψ, map_zero, hψder, c.residue_coefficient_eq_normal] at h0
  have hka : κ * c.normalCoefficient = -c.residueMap (pderiv j (cellSchur D hD.1)) := by
    linear_combination -h0
  have hκ : κ = -c.residueMap (pderiv j (cellSchur D hD.1)) * c.normalCoefficient⁻¹ := by
    rw [← hka, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  rw [hgen f, hκ]
  ring

/-- Uniform raw/chart chain rule, including the selected direction. Differentiating
the selected generator while keeping the normal coordinate fixed is the zero chart
derivation; its raw partial is canceled by the selected-coordinate correction. -/
theorem original_residue_chart_polynomial_chain (j : ℕ+) (f : Lambda) :
    residueChartDeriv c.top j (c.residueMap f) =
      c.residueMap (pderiv j f) - c.normalCoefficient⁻¹ * c.residueMap (pderiv c.top f) *
        c.residueMap (pderiv j (cellSchur D hD.1)) := by
  by_cases hj : j = c.top
  · subst j
    rw [residueChartDeriv, dite_eq_left rfl]
    simp only [Derivation.zero_apply, c.selected_prime_top_partial,
      c.residue_coefficient_eq_normal]
    field_simp [c.normalCoefficient_ne_zero]
    ring
  · rw [residueChartDeriv, dite_eq_right hj]
    exact c.original_residue_polynomial_chain j hj f

end SelectedCoordinate

end SkewCornerDescent.Matrix
