/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.GeneratorDerivation
import SkewCornerDescent.Matrix.ResidueProtectedGenerator
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Original surviving-generator derivation in the actual normal coefficient field

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The rational first jet extends the polynomial partial derivative to the complete
coefficient fraction field, including every denominator inverse.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Value and first partial derivative of an actual surviving-generator polynomial. -/
noncomputable def residuePolynomialJet (N : ℕ+) (j : {j : ℕ+ // j ≠ N}) :
    OtherPolynomial N →+* TrivSqZeroExt (OtherField N) (OtherField N) where
  toFun f := TrivSqZeroExt.inl (algebraMap _ _ f) +
    TrivSqZeroExt.inr (algebraMap _ _ (MvPolynomial.pderiv j f))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' f g := by ext <;> simp [Algebra.smul_def]
  map_mul' f g := by
    apply TrivSqZeroExt.ext <;> simp [Algebra.smul_def]; ring

private theorem residuePolynomialJet_units (N : ℕ+) (j : {j : ℕ+ // j ≠ N})
    (s : nonZeroDivisors (OtherPolynomial N)) : IsUnit (residuePolynomialJet N j s) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  simp [residuePolynomialJet]

/-- The whole original coefficient fraction has its full rational first jet. -/
noncomputable def residueRationalJet (N : ℕ+) (j : {j : ℕ+ // j ≠ N}) :
    OtherField N →+* TrivSqZeroExt (OtherField N) (OtherField N) :=
  IsLocalization.lift (residuePolynomialJet_units N j)

@[simp]
theorem residueRationalJet_algebraMap (N : ℕ+) (j : {j : ℕ+ // j ≠ N})
    (f : OtherPolynomial N) :
    residueRationalJet N j (algebraMap (OtherPolynomial N) (OtherField N) f) =
      residuePolynomialJet N j f :=
  IsLocalization.lift_eq (residuePolynomialJet_units N j) f

@[simp]
theorem residueRationalJet_fst (N : ℕ+) (j : {j : ℕ+ // j ≠ N}) (f : OtherField N) :
    (residueRationalJet N j f).fst = f := by
  have h : (TrivSqZeroExt.fstHom (OtherField N) (OtherField N) (OtherField N)).toRingHom.comp
      (residueRationalJet N j) = RingHom.id (OtherField N) := by
    apply IsFractionRing.ringHom_ext (A := OtherPolynomial N)
    intro f
    change (residueRationalJet N j (algebraMap (OtherPolynomial N) (OtherField N) f)).fst = _
    rw [residueRationalJet_algebraMap]
    simp [residuePolynomialJet]
  exact RingHom.congr_fun h f

/-- Partial derivative in the genuine original surviving generator. -/
noncomputable def residueGeneratorDeriv (N : ℕ+) (j : {j : ℕ+ // j ≠ N}) :
    Derivation ℚ (OtherField N) (OtherField N) where
  toFun f := (residueRationalJet N j f).snd
  map_add' f g := by simp
  map_smul' q f :=
    map_rat_smul
      (_instM := (DivisionRing.toRatAlgebra : Algebra ℚ (OtherField N)).toModule)
      ((TrivSqZeroExt.sndHom (OtherField N) (OtherField N)).toAddMonoidHom.comp
        (residueRationalJet N j).toAddMonoidHom) q f
  map_one_eq_zero' := by
    change (residueRationalJet N j 1).snd = 0
    simp
  leibniz' f g := by
    change (residueRationalJet N j (f * g)).snd =
      f * (residueRationalJet N j g).snd + g * (residueRationalJet N j f).snd
    simp [TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm]

@[simp]
theorem residueGeneratorDeriv_algebraMap (N : ℕ+) (j : {j : ℕ+ // j ≠ N})
    (f : OtherPolynomial N) :
    residueGeneratorDeriv N j (algebraMap (OtherPolynomial N) (OtherField N) f) =
      algebraMap (OtherPolynomial N) (OtherField N) (MvPolynomial.pderiv j f) := by
  change (residueRationalJet N j (algebraMap (OtherPolynomial N) (OtherField N) f)).snd = _
  rw [residueRationalJet_algebraMap]
  simp [residuePolynomialJet, Algebra.smul_def]

@[simp]
theorem residueGeneratorDeriv_generator (N : ℕ+) (j k : {j : ℕ+ // j ≠ N}) :
    residueGeneratorDeriv N j (residueGenerator N k) = if k = j then 1 else 0 := by
  by_cases h : k = j
  · subst k
    simp [residueGenerator]
  · simp [residueGenerator, MvPolynomial.pderiv_X_of_ne h, h]

end SkewCornerDescent.Matrix
