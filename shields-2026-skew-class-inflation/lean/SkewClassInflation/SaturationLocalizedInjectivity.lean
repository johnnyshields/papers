/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationNormalization
import SkewClassInflation.SaturationSubstitution
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Injectivity of the actual localized power substitution

The injectivity step following `eq:saturation-substitution` in
`shields-2026-skew-class-inflation.tex`.  The ratio substitution factors
through localization at the genuine larger-seam generator.  Its map to
the full fraction field is injective, while seam normalization supplies
an injective triangular comparison.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- Localize only at the distinguished seam generator, not at arbitrary polynomials. -/
abbrev sourceLocalization := Localization.Away (complete A.d)

/-- The canonical embedding of the seam localization into the full fraction field. -/
noncomputable def fractionLift : A.sourceLocalization →+* SaturationFractionField :=
  IsLocalization.Away.lift (g := algebraMap CompleteRing SaturationFractionField) (complete A.d)
    (isUnit_iff_ne_zero.mpr A.large_generator_nonzero)

/-- The fraction embedding retains every original polynomial. -/
theorem fractionLift_algebraMap (p : CompleteRing) :
    A.fractionLift (algebraMap CompleteRing A.sourceLocalization p) =
      algebraMap CompleteRing SaturationFractionField p := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- Normalization extends because the distinguished denominator is sent to the unit one. -/
noncomputable def normalizationLift : A.sourceLocalization →+* CompleteRing :=
  IsLocalization.Away.lift (g := A.normalizeSeams.toRingHom) (complete A.d) (by
    change IsUnit (A.normalizeSeams (complete A.d))
    rw [A.normalizeSeams_complete A.d (Or.inr rfl)]
    exact isUnit_one)

/-- The extended normalization agrees with the actual polynomial normalization. -/
theorem normalizationLift_algebraMap (p : CompleteRing) :
    A.normalizationLift (algebraMap CompleteRing A.sourceLocalization p) = A.normalizeSeams p := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The only inverted element is represented by its genuine reciprocal in the fraction field. -/
theorem fractionLift_invSelf :
    A.fractionLift (IsLocalization.Away.invSelf (S := A.sourceLocalization) (complete A.d)) =
      (algebraMap CompleteRing SaturationFractionField (complete A.d))⁻¹ := by
  have he := congrArg (fun z : A.sourceLocalization => A.fractionLift z)
    (IsLocalization.Away.mul_invSelf (S := A.sourceLocalization) (complete A.d))
  rw [map_mul, map_one, A.fractionLift_algebraMap] at he
  rw [← one_div]
  apply (eq_div_iff A.large_generator_nonzero).mpr
  simpa only [mul_comm] using he

/-- The inverted distinguished generator also normalizes to one. -/
theorem normalizationLift_invSelf :
    A.normalizationLift (IsLocalization.Away.invSelf (S := A.sourceLocalization) (complete A.d)) =
      1 := by
  have he := congrArg (fun z : A.sourceLocalization => A.normalizationLift z)
    (IsLocalization.Away.mul_invSelf (S := A.sourceLocalization) (complete A.d))
  rw [map_mul, map_one, A.normalizationLift_algebraMap,
    A.normalizeSeams_complete A.d (Or.inr rfl), one_mul] at he
  exact he

/-- The seam localization embeds without collapsing any element. -/
theorem fractionLift_injective : Function.Injective A.fractionLift := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (complete A.d)) A.fractionLift).mpr
  intro p q
  rw [A.fractionLift_algebraMap, A.fractionLift_algebraMap]
  constructor
  · intro he
    have hh := congrArg (fun z : A.sourceLocalization => A.fractionLift z) he
    simpa only [A.fractionLift_algebraMap] using hh
  · intro he
    exact congrArg (algebraMap CompleteRing A.sourceLocalization)
      (IsFractionRing.injective CompleteRing SaturationFractionField he)

/-- The actual ratios already live in the localization at the one permitted denominator. -/
noncomputable def localizedSubstitutionAway : CompleteRing →+* A.sourceLocalization :=
  MvPolynomial.eval₂Hom ((algebraMap CompleteRing A.sourceLocalization).comp MvPolynomial.C)
    (fun m : ℕ+ =>
      algebraMap CompleteRing A.sourceLocalization (A.power m.val m.pos).toBetaDiagram.schur *
        IsLocalization.Away.invSelf (S := A.sourceLocalization) (complete A.d))

/-- Embedding the localized ratios recovers the exact fraction-field substitution. -/
theorem fractionLift_comp_substitution :
    A.fractionLift.comp A.localizedSubstitutionAway = A.localizedSubstitution := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, localizedSubstitutionAway, MvPolynomial.eval₂Hom_C,
      A.fractionLift_algebraMap, localizedSubstitution]
    change algebraMap CompleteRing SaturationFractionField (algebraMap ℚ CompleteRing r) =
      algebraMap ℚ SaturationFractionField r
    exact (IsScalarTower.algebraMap_apply ℚ CompleteRing SaturationFractionField r).symm
  · intro m
    simp only [RingHom.comp_apply, localizedSubstitutionAway, MvPolynomial.eval₂Hom_X',
      map_mul, A.fractionLift_algebraMap, A.fractionLift_invSelf,
      localizedSubstitution, div_eq_mul_inv]

/-- Extending normalization turns the localized ratios into the actual triangular power family. -/
theorem normalizationLift_comp_substitution :
    A.normalizationLift.comp A.localizedSubstitutionAway =
      (MvPolynomial.aeval (fun m : ℕ+ =>
        A.normalizeSeams (A.power m.val m.pos).toBetaDiagram.schur) :
          CompleteRing →ₐ[ℚ] CompleteRing).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, localizedSubstitutionAway, MvPolynomial.eval₂Hom_C,
      A.normalizationLift_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_C]
    exact A.normalizeSeams.commutes r
  · intro m
    simp only [RingHom.comp_apply, localizedSubstitutionAway, MvPolynomial.eval₂Hom_X',
      map_mul, A.normalizationLift_algebraMap, A.normalizationLift_invSelf, mul_one,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]

/-- The actual localized power ratios are algebraically independent over the rationals.

**Differs from the paper's route.** Normalizes both seam generators to one and
uses localization at the larger generator to compare with an injective triangular
family, rather than working directly over the rational-function coefficient field. -/
theorem localizedSubstitution_injective : Function.Injective A.localizedSubstitution := by
  intro p q he
  apply A.normalized_substitution_injective
  have hfrac : A.fractionLift (A.localizedSubstitutionAway p) =
      A.fractionLift (A.localizedSubstitutionAway q) := by
    change (A.fractionLift.comp A.localizedSubstitutionAway) p =
      (A.fractionLift.comp A.localizedSubstitutionAway) q
    rw [A.fractionLift_comp_substitution]
    exact he
  have haway := A.fractionLift_injective hfrac
  have hnorm := congrArg (fun z : A.sourceLocalization => A.normalizationLift z) haway
  change (A.normalizationLift.comp A.localizedSubstitutionAway) p =
    (A.normalizationLift.comp A.localizedSubstitutionAway) q at hnorm
  rw [A.normalizationLift_comp_substitution] at hnorm
  exact hnorm

/-- Equality within the full arbitrary-inner family is exactly equality of the outer ribbons. -/
theorem diagram_schur_eq_iff_ribbon {M : ℕ} (α β : Composition M) (hM : 0 < M) :
    (A.diagram α hM).2.toBetaDiagram.schur = (A.diagram β hM).2.toBetaDiagram.schur ↔
      ribbonWord α.blocks = ribbonWord β.blocks := by
  constructor
  · intro he
    have hn := (A.diagram α hM).2.toBetaDiagram.row_count_of_schur_eq
      (A.diagram β hM).2.toBetaDiagram he
    change (A.diagram α hM).1 + 1 = (A.diagram β hM).1 + 1 at hn
    rw [A.diagram_row_count, A.diagram_row_count] at hn
    have hlen : α.length = β.length := by omega
    have hm := congrArg (algebraMap CompleteRing SaturationFractionField) he
    rw [A.diagram_substitution, A.diagram_substitution, hlen] at hm
    apply A.localizedSubstitution_injective
    exact mul_left_cancel₀ (pow_ne_zero _ A.large_generator_nonzero) hm
  · exact A.diagram_schur_eq_of_ribbon_eq α β hM

end SkewClassInflation.SaturationInner
