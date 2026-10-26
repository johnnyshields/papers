/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Localization.FractionRing
import SkewGluing.RowInvariants

/-!
# Original-generator derivatives on the actual rational field

Supports local algebraic steps in `shields-2026-skew-corner-descent.tex`, «From response
functions to literal copies» (`sec:one-active`).

The rational field is the fraction field of `SkewGluing.Lambda`, not a new symmetric-function
presentation. A generator derivative is extended by the universal property of localization
through the trivial square-zero extension. This supplies full inverse derivatives for
`lem:profile-derivative`; it is distinct from the power-sum adjoint `Plan.pDeriv`.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The rational field of the canonical complete-homogeneous polynomial ring. -/
abbrev actualField := FractionRing Lambda

/-- Embed an original polynomial into its rational field. -/
noncomputable def originalMap : Lambda →+* actualField := algebraMap Lambda actualField

/-- The canonical polynomial embedding is injective. -/
theorem originalMap_injective : Function.Injective originalMap :=
  IsFractionRing.injective Lambda actualField

@[simp]
theorem originalMap_eq_zero (f : Lambda) : originalMap f = 0 ↔ f = 0 :=
  map_eq_zero_iff originalMap originalMap_injective

/-- The polynomial value together with its original-generator first jet. -/
noncomputable def polynomialJet (j : ℕ+) :
    Lambda →+* TrivSqZeroExt actualField actualField where
  toFun f := TrivSqZeroExt.inl (originalMap f) +
    TrivSqZeroExt.inr (originalMap (MvPolynomial.pderiv j f))
  map_one' := by ext <;> simp [originalMap]
  map_zero' := by ext <;> simp [originalMap]
  map_add' f g := by ext <;> simp [originalMap]
  map_mul' f g := by
    ext <;> simp [originalMap, smul_eq_mul, mul_comm, add_comm]

private theorem polynomialJet_units (j : ℕ+) (s : nonZeroDivisors Lambda) :
    IsUnit (polynomialJet j s) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  simp [polynomialJet, originalMap]

/-- Extend the jet to every rational function, including every inverse entry. -/
noncomputable def rationalJet (j : ℕ+) :
    actualField →+* TrivSqZeroExt actualField actualField :=
  IsLocalization.lift (polynomialJet_units j)

@[simp]
theorem rationalJet_originalMap (j : ℕ+) (f : Lambda) :
    rationalJet j (originalMap f) = polynomialJet j f :=
  IsLocalization.lift_eq (polynomialJet_units j) f

@[simp]
theorem rationalJet_fst (j : ℕ+) (f : actualField) : (rationalJet j f).fst = f := by
  have h : (TrivSqZeroExt.fstHom ℚ actualField actualField).toRingHom.comp (rationalJet j) =
      RingHom.id actualField := by
    apply IsFractionRing.ringHom_ext (A := Lambda)
    intro f
    change (rationalJet j (originalMap f)).fst = originalMap f
    rw [rationalJet_originalMap]
    simp [polynomialJet]
  exact RingHom.congr_fun h f

/-- The rational jet respects the original rational constants. -/
noncomputable def rationalJetAlgHom (j : ℕ+) :
    actualField →ₐ[ℚ] TrivSqZeroExt actualField actualField where
  __ := rationalJet j
  commutes' q := by
    change rationalJet j ((algebraMap ℚ actualField) q) = _
    rw [IsScalarTower.algebraMap_apply ℚ Lambda actualField, ← originalMap,
      rationalJet_originalMap]
    ext <;> simp [polynomialJet, originalMap, TrivSqZeroExt.algebraMap_eq_inl',
      IsScalarTower.algebraMap_apply ℚ Lambda actualField]

/-- Partial derivative in the original generator `h_j`, on actual rational functions. -/
noncomputable def generatorDeriv (j : ℕ+) : Derivation ℚ actualField actualField :=
  Derivation.mk'
    ((TrivSqZeroExt.sndHom actualField actualField).restrictScalars ℚ |>.comp
      (rationalJetAlgHom j).toLinearMap)
    (fun f g => by
      simp [rationalJetAlgHom, TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm])

@[simp]
theorem generatorDeriv_originalMap (j : ℕ+) (f : Lambda) :
    generatorDeriv j (originalMap f) = originalMap (MvPolynomial.pderiv j f) := by
  change (rationalJet j (originalMap f)).snd = _
  rw [rationalJet_originalMap]
  simp [polynomialJet]

theorem generatorDeriv_X (j k : ℕ+) :
    generatorDeriv j (originalMap (MvPolynomial.X k)) = if k = j then 1 else 0 := by
  by_cases h : k = j
  · subst k
    simp
  · simp [MvPolynomial.pderiv_X_of_ne h, h]

/-- The original JT entry derivative, including the constant `h_0` and all negative indices. -/
theorem generatorDeriv_hh (j : ℕ+) (k : ℤ) :
    generatorDeriv j (originalMap (hh k)) = if k = (j : ℤ) then 1 else 0 := by
  rw [generatorDeriv_originalMap, SkewGluing.pderiv_hh]
  split_ifs <;> simp

end SkewCornerDescent.Matrix
