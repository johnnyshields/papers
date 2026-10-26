/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalResidue
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Regular fractions at the actual selected divisor

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`). The residue extends to the localization at the actual connected
prime. Its fraction formula retains the original numerator and denominator. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual selected prime ideal, realized as the proved residue kernel. -/
noncomputable def selectedIdeal : Ideal Lambda := RingHom.ker c.residueMap

instance selectedIdeal_isPrime : c.selectedIdeal.IsPrime := RingHom.ker_isPrime c.residueMap

@[simp]
theorem mem_selectedIdeal (f : Lambda) :
    f ∈ c.selectedIdeal ↔ cellSchur D hD.1 ∣ f := by
  simp [selectedIdeal]

/-- Only denominators regular at the selected connected prime are inverted. -/
abbrev RegularRing := Localization.AtPrime c.selectedIdeal

theorem regularDenominator_residue_ne_zero (y : c.selectedIdeal.primeCompl) :
    c.residueMap y ≠ 0 := by
  intro h
  exact y.2 (RingHom.mem_ker.mpr h)

/-- Residue on the genuine local ring, not an evaluation of arbitrary field fractions. -/
noncomputable def regularResidue : c.RegularRing →+* OtherField c.top :=
  IsLocalization.lift (fun y => (c.regularDenominator_residue_ne_zero y).isUnit)

@[simp]
theorem regularResidue_polynomial (f : Lambda) :
    c.regularResidue (algebraMap Lambda c.RegularRing f) = c.residueMap f :=
  IsLocalization.lift_eq _ f

/-- The full rational fraction specializes by its actual regular denominator. -/
theorem regularResidue_fraction (f : Lambda) (y : c.selectedIdeal.primeCompl) :
    c.regularResidue (IsLocalization.mk' c.RegularRing f y) =
      c.residueMap f / c.residueMap y := by
  apply (IsLocalization.lift_mk'_spec _ _ _ _).2
  field_simp [c.regularDenominator_residue_ne_zero y]

/-- Vanishing of a regular fraction is exactly divisibility of its numerator. -/
theorem regularResidue_fraction_eq_zero_iff (f : Lambda) (y : c.selectedIdeal.primeCompl) :
    c.regularResidue (IsLocalization.mk' c.RegularRing f y) = 0 ↔
      cellSchur D hD.1 ∣ f := by
  rw [c.regularResidue_fraction, div_eq_zero_iff]
  simp [c.regularDenominator_residue_ne_zero y]

/-- A regular denominator is nonzero in the original polynomial ring. -/
theorem regularDenominator_ne_zero (y : c.selectedIdeal.primeCompl) : (y : Lambda) ≠ 0 := by
  intro h
  exact c.regularDenominator_residue_ne_zero y (h ▸ map_zero c.residueMap)

/-- The local ring embeds into the original rational field. -/
noncomputable def regularEmbedding : c.RegularRing →+* actualField :=
  IsLocalization.lift (fun y =>
    ((map_ne_zero_iff originalMap originalMap_injective).2
      (c.regularDenominator_ne_zero y)).isUnit)

theorem regularEmbedding_injective : Function.Injective c.regularEmbedding := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro x y
  rw [(FaithfulSMul.algebraMap_injective Lambda c.RegularRing).eq_iff,
    originalMap_injective.eq_iff]

@[simp]
theorem regularEmbedding_polynomial (f : Lambda) :
    c.regularEmbedding (algebraMap Lambda c.RegularRing f) = originalMap f :=
  IsLocalization.lift_eq _ f

/-- The embedded local fraction is the unmodified original rational function. -/
theorem regularEmbedding_fraction (f : Lambda) (y : c.selectedIdeal.primeCompl) :
    c.regularEmbedding (IsLocalization.mk' c.RegularRing f y) =
      originalMap f / originalMap y := by
  apply (IsLocalization.lift_mk'_spec _ _ _ _).2
  field_simp [(map_ne_zero_iff originalMap originalMap_injective).2
    (c.regularDenominator_ne_zero y)]

end SkewCornerDescent.Matrix.SelectedCoordinate
