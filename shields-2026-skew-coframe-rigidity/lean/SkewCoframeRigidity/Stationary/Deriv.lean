/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Defs
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The derivative in one raw letter

Formalizes the derivative `∂_{H_m}` used in `shields-2026-skew-coframe-rigidity.tex`,
`sc:top-matching` and `sc:positive-power`.  The partial derivative of `ℚ[ϑ, H₁, H₂, …]` in the
variable `m` extends to the fraction field `CohField` as a derivation `dRaw m`; this is built as
the unique extension, through the dual numbers, of the ring map `f ↦ f + (∂_m f) ε`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial

/-- `f ↦ f + (∂_m f) ε` into the dual numbers over the fraction field. -/
noncomputable def dualHom (m : ℕ) : CohRing →+* DualNumber CohField where
  toFun f := TrivSqZeroExt.inl (algebraMap CohRing CohField f) +
    TrivSqZeroExt.inr (algebraMap CohRing CohField (MvPolynomial.pderiv m f))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext <;> simp [Algebra.smul_def]
  map_mul' a b := by
    ext <;> simp [Algebra.smul_def, mul_comm, add_comm]

theorem dualHom_fst (m : ℕ) (f : CohRing) :
    TrivSqZeroExt.fst (dualHom m f) = algebraMap CohRing CohField f := by
  simp [dualHom]

theorem dualHom_unit (m : ℕ) (s : nonZeroDivisors CohRing) : IsUnit (dualHom m s) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualHom_fst]
  exact (IsFractionRing.isUnit_map_of_injective (IsFractionRing.injective CohRing CohField) s)

/-- The extension of `dualHom m` to the fraction field. -/
noncomputable def dualExt (m : ℕ) : CohField →+* DualNumber CohField :=
  IsLocalization.lift (M := nonZeroDivisors CohRing) (dualHom_unit m)

theorem dualExt_fst (m : ℕ) (x : CohField) : TrivSqZeroExt.fst (dualExt m x) = x := by
  have h : (TrivSqZeroExt.fstHom CohField CohField CohField).toRingHom.comp (dualExt m) =
      RingHom.id CohField := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors CohRing) ?_
    refine RingHom.ext fun f => ?_
    have := IsLocalization.lift_eq (S := CohField) (dualHom_unit m) f
    simp only [RingHom.comp_apply, RingHom.id_apply]
    show TrivSqZeroExt.fst (dualExt m (algebraMap CohRing CohField f)) = _
    rw [dualExt, this, dualHom_fst]
  exact congrArg (fun φ => φ x) h

/-- The derivation `∂/∂H_m` of the raw field. -/
noncomputable def dRaw (m : ℕ) (x : CohField) : CohField := TrivSqZeroExt.snd (dualExt m x)

theorem dRaw_add (m : ℕ) (x y : CohField) : dRaw m (x + y) = dRaw m x + dRaw m y := by
  simp [dRaw]

theorem dRaw_mul (m : ℕ) (x y : CohField) :
    dRaw m (x * y) = dRaw m x * y + x * dRaw m y := by
  simp only [dRaw, map_mul, TrivSqZeroExt.snd_mul, dualExt_fst]
  simp [mul_comm, add_comm]

theorem dRaw_algebraMap (m : ℕ) (f : CohRing) :
    dRaw m (algebraMap CohRing CohField f) = algebraMap CohRing CohField (MvPolynomial.pderiv m f) := by
  have := IsLocalization.lift_eq (S := CohField) (dualHom_unit m) f
  have e : dRaw m (algebraMap CohRing CohField f) = TrivSqZeroExt.snd (dualHom m f) := by
    rw [dRaw, dualExt, this]
  rw [e]; simp [dualHom, Algebra.smul_def]

theorem dRaw_letter (m k : ℕ) : dRaw m (cohLetters k) = if k = m then 1 else 0 := by
  unfold cohLetters
  rw [dRaw_algebraMap, MvPolynomial.pderiv_X]
  by_cases h : k = m
  · subst h; simp
  · simp [h]

theorem dRaw_zero (m : ℕ) : dRaw m 0 = 0 := by
  have := dRaw_add m 0 0; simpa using this

theorem dRaw_one (m : ℕ) : dRaw m 1 = 0 := by
  have := dRaw_mul m 1 1; simp at this; simpa using this

theorem dRaw_neg (m : ℕ) (x : CohField) : dRaw m (-x) = -dRaw m x := by
  have := dRaw_add m x (-x); rw [add_neg_cancel, dRaw_zero] at this
  linear_combination -this

theorem dRaw_sub (m : ℕ) (x y : CohField) : dRaw m (x - y) = dRaw m x - dRaw m y := by
  rw [sub_eq_add_neg, dRaw_add, dRaw_neg]; ring

theorem dRaw_sum (m : ℕ) {ι : Type*} (s : Finset ι) (f : ι → CohField) :
    dRaw m (∑ i ∈ s, f i) = ∑ i ∈ s, dRaw m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dRaw_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dRaw_add, ih]

theorem dRaw_pow (m : ℕ) (x : CohField) (k : ℕ) :
    dRaw m (x ^ k) = k * x ^ (k - 1) * dRaw m x := by
  induction k with
  | zero => simp [dRaw_one]
  | succ k ih =>
    rw [pow_succ, dRaw_mul, ih]
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring

theorem dRaw_inv (m : ℕ) (x : CohField) (hx : x ≠ 0) :
    dRaw m x⁻¹ = -(dRaw m x) * (x⁻¹) ^ 2 := by
  have := dRaw_mul m x x⁻¹
  rw [mul_inv_cancel₀ hx, dRaw_one] at this
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h2 : x * dRaw m x⁻¹ = -(dRaw m x) * x⁻¹ := by linear_combination -this
  field_simp
  field_simp at h2
  linear_combination h2

end SkewCoframeRigidity.Coframe
