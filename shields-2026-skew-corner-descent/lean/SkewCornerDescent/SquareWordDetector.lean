/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordResponses
import SkewCornerDescent.CyclicDetectors

/-!
# The actual second periodic detector of the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The complete original scalar matrix supplies the period, while literal source
and window counts supply both signed exponents. No detector value is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial SkewCornerDescent.Matrix CyclicWindows
open scoped BigOperators

/-- The first actual period, extracted from the full original response word. -/
noncomputable def actualPeriod (z : ZMod 3) : OtherField coordinate.top :=
  sourceInternalResponse coordinate.residueMap ⟨z.val, by have := ZMod.val_lt z; omega⟩

/-- Both actual residue response classes of the complete scalar matrix. -/
noncomputable def actualResponse (vertical : Bool) : OtherField coordinate.top :=
  responseScalar coordinate.residueMap vertical

private def modelPeriod {F : Type*} (H V : F) (z : ZMod 3) : F :=
  if z.val = 0 then H else V

/-- The period model is derived from the original response matrix. -/
theorem actualPeriod_eq_model : actualPeriod =
    modelPeriod (coordinate.residueMap (X 4))
      (coordinate.residueMap (X 4) - coordinate.residueMap (X 2) ^ 2) := by
  funext z
  rw [actualPeriod, sourceInternalResponse_actual_word]
  fin_cases z <;> norm_num [ZMod.val, sourceWordBits, responseScalar, modelPeriod]

private theorem sum_three {F : Type*} [AddCommMonoid F] (f : ZMod 3 → F) :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0,1,2} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

private theorem sum_five {F : Type*} [AddCommMonoid F] (f : ZMod 5 → F) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have hu : (Finset.univ : Finset (ZMod 5)) = {0,1,2,3,4} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]

private theorem model_second_detector {F : Type*} [Field F] (H V : F)
    (hH : H ≠ 0) (hV : V ≠ 0) :
    windowDefect (modelPeriod H V) (fun b : Bool => if b then V else H)
        sourceClassExponent 5 5 2 = 2 * (H⁻¹ - V⁻¹) ^ 2 := by
  have he : sourceClassExponent = (fun b : Bool => if b then 4 else -1) := by
    funext b
    cases b with
    | false => exact sourceClassExponent_eq.1
    | true => exact sourceClassExponent_eq.2
  rw [he]
  norm_num [windowDefect, inverseWindowSum, sum_three, sum_five,
    windowProduct, closureWord, modelPeriod, ZMod.val_natCast, ZMod.val_ofNat,
    ZMod.val_add, ZMod.val_one_eq_one_mod, ZMod.cast_eq_val,
    Finset.prod_range_succ, Fintype.sum_bool]
  field_simp
  ring

/-- The original signed periodic detector with the produced source period and counts. -/
noncomputable def actualSecondDetector : OtherField coordinate.top :=
  windowDefect actualPeriod actualResponse sourceClassExponent 5 5 2

/-- The exact second detector is the stated nonzero square of inverse differences. -/
theorem actualSecondDetector_eq :
    actualSecondDetector =
      2 * ((coordinate.residueMap (X 4))⁻¹ -
        (coordinate.residueMap (X 4) - coordinate.residueMap (X 2) ^ 2)⁻¹) ^ 2 := by
  rw [actualSecondDetector, actualPeriod_eq_model]
  exact model_second_detector _ _
    (coordinate_residue_generator_ne_zero 4 (by decide))
    coordinate_residue_square_difference_ne_zero

/-- The two physically produced actual response classes are distinct. -/
theorem actualResponse_distinct : actualResponse false ≠ actualResponse true := by
  intro he
  have hz : coordinate.residueMap (X 2) ^ 2 = 0 := by
    unfold actualResponse responseScalar at he
    simp only [Bool.false_eq_true, ite_false, ite_true] at he
    linear_combination he
  exact pow_ne_zero 2 (coordinate_residue_generator_ne_zero 2 (by decide)) hz

/-- The inverse difference cannot vanish on the genuine selected residue field. -/
theorem actualResponse_inverse_difference_ne_zero :
    (actualResponse false)⁻¹ - (actualResponse true)⁻¹ ≠ 0 := by
  intro hz
  have h := congrArg (fun x : OtherField coordinate.top => x⁻¹) (sub_eq_zero.mp hz)
  simp only [inv_inv] at h
  exact actualResponse_distinct h

/-- The second periodic detector is genuinely nonzero on the actual chart. -/
theorem actualSecondDetector_ne_zero : actualSecondDetector ≠ 0 := by
  rw [actualSecondDetector_eq]
  change 2 * ((actualResponse false)⁻¹ - (actualResponse true)⁻¹) ^ 2 ≠ 0
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 actualResponse_inverse_difference_ne_zero)

end SkewCornerDescent.SquareWordProfiles
