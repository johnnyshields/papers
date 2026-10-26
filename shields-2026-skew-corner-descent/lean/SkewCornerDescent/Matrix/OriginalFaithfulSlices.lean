/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.RationalGenericChambers
import SkewCornerDescent.Matrix.OriginalExposedPolynomials
import SkewCornerDescent.ExposedPrimeValuation

/-!
# Genuine original fraction-field slices in every open chamber

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`).
A faithful rational assignment can be chosen inside every nonempty open
chamber. Leaving one coordinate polynomial then remains injective and
extends to the whole unchanged original residue fraction field. Every
original polynomial omitting that coordinate maps to a nonzero constant
when nonzero, so its exposed-root valuation is a unit. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open SkewGluing MvPolynomial

/-- Every real open chamber admits an injective complete original
coordinate slice, not merely a regular map on finitely many expressions. -/
theorem exists_faithful_original_coordinate_slice (N K : ℕ+)
    (U : Set (ℕ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, Function.Injective (originalCoordinateSlice N K x) := by
  obtain ⟨x, hxU, hx⟩ := exists_faithful_rational_evaluation_on_open U hU hne
  let renameNat : OtherPolynomial N →+* MvPolynomial ℕ ℚ :=
    (MvPolynomial.rename (fun j : {j : ℕ+ // j ≠ N} => (j.val : ℕ))).toRingHom
  have hrename : Function.Injective renameNat := by
    apply MvPolynomial.rename_injective
    intro i j he
    exact Subtype.ext (Subtype.ext he)
  have heval : (MvPolynomial.eval x).comp (realResiduePolynomial N) =
      (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x).comp renameNat := by
    ext j
    · simp [realResiduePolynomial, renameNat]
    · simp [realResiduePolynomial, renameNat]
  have hreal : Function.Injective ((MvPolynomial.eval x).comp (realResiduePolynomial N)) := by
    rw [heval]
    exact hx.comp hrename
  have hslice : Function.Injective ((coordinatePolynomial (K : ℕ) x).comp
      (realResiduePolynomial N)) := by
    intro p q he
    apply hreal
    have h := congrArg (Polynomial.eval (x K)) he
    simpa only [RingHom.comp_apply, coordinatePolynomial_eval, Function.update_eq_self] using h
  exact ⟨x, hxU, (IsFractionRing.injective (Polynomial ℝ) (RatFunc ℝ)).comp hslice⟩

/-- An injective actual polynomial slice extends to the whole original field. -/
noncomputable def originalCoordinateFieldSlice (N K : ℕ+) (x : ℕ → ℝ)
    (hx : Function.Injective (originalCoordinateSlice N K x)) :
    OtherField N →+* RatFunc ℝ := IsFractionRing.lift hx

/-- The full field map agrees with the actual polynomial coordinate slice. -/
theorem originalCoordinateFieldSlice_algebraMap (N K : ℕ+) (x : ℕ → ℝ)
    (hx : Function.Injective (originalCoordinateSlice N K x)) (p : OtherPolynomial N) :
    originalCoordinateFieldSlice N K x hx (algebraMap (OtherPolynomial N) (OtherField N) p) =
      originalCoordinateSlice N K x p :=
  IsFractionRing.lift_algebraMap hx p

/-- The actual response-prime slice valuation is trivial on every nonzero
original polynomial omitting the exposed coordinate, including higher ones. -/
theorem originalCoordinateFieldSlice_off_coordinate_unit (N K : ℕ+) (x : ℕ → ℝ)
    (hx : Function.Injective (originalCoordinateSlice N K x)) (r : ℝ)
    (p : OtherPolynomial N) (hp : p ≠ 0)
    (hK : (K : ℕ) ∉ (realResiduePolynomial N p).vars) :
    (exposedRootIdeal r).valuation (RatFunc ℝ)
      (originalCoordinateFieldSlice N K x hx
        (algebraMap (OtherPolynomial N) (OtherField N) p)) = 1 := by
  let a := MvPolynomial.eval x (realResiduePolynomial N p)
  have he : originalCoordinateSlice N K x p = RatFunc.C a := by
    simp only [originalCoordinateSlice, RingHom.comp_apply,
      coordinatePolynomial_constant (K : ℕ) x _ hK, RatFunc.algebraMap_C]
    rfl
  have ha : a ≠ 0 := by
    intro hz
    apply hp
    apply hx
    rw [map_zero, he, hz, map_zero]
  rw [originalCoordinateFieldSlice_algebraMap, he]
  exact exposedRoot_constant_valuation r a ha

end SkewCornerDescent.Matrix
