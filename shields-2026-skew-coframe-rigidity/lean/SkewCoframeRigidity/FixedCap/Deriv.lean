/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.FixedCap.LetterField
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# The partial derivative in a letter

Formalizes the derivative with respect to one raw letter `h_L` used throughout the descent in the
proof of `sc:fixed-cap` of `shields-2026-skew-coframe-rigidity.tex`.  The derivation `∂_L` of the
polynomial ring in the letters extends to the raw field (`letterDeriv`); it sends `h_j` to
`δ_{jL}`, kills `letterField L`, and acts on the coefficients of power series.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCoframeRigidity.Coframe MvPolynomial TrivSqZeroExt

private noncomputable abbrev embD : CohRing →+* CohField := algebraMap CohRing CohField

/-- The ring map to the dual numbers `p ↦ (p, ∂_L p)`. -/
private noncomputable def dualHom (L : ℕ) : CohRing →+* TrivSqZeroExt CohField CohField where
  toFun p := inl (embD p) + inr (embD (pderiv L p))
  map_one' := by simp
  map_mul' p q := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul]
    · simp [TrivSqZeroExt.snd_mul, Derivation.leibniz, add_comm, Algebra.smul_def, mul_comm]
  map_zero' := by simp
  map_add' p q := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Algebra.smul_def]

private theorem dualHom_unit (L : ℕ) (q : nonZeroDivisors CohRing) :
    IsUnit (dualHom L (q : CohRing)) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  have : (q : CohRing) ≠ 0 := nonZeroDivisors.coe_ne_zero q
  simp only [dualHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  exact isUnit_iff_ne_zero.2
    ((map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 this)

private noncomputable def dualLift (L : ℕ) : CohField →+* TrivSqZeroExt CohField CohField :=
  IsLocalization.lift (M := nonZeroDivisors CohRing) (dualHom_unit L)

private theorem fst_dualLift (L : ℕ) (x : CohField) : (dualLift L x).fst = x := by
  have h : ((TrivSqZeroExt.fstHom CohField CohField CohField).toRingHom :
      TrivSqZeroExt CohField CohField →+* CohField).comp
      (dualLift L) = RingHom.id CohField := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors CohRing)
    refine RingHom.ext fun p => ?_
    simp [dualLift, dualHom, RingHom.comp_apply, IsLocalization.lift_eq]
  exact congrArg (fun f => f x) h

/-- The derivation `∂_L` of the raw field with respect to the letter `h_L`, as an additive map;
it satisfies the Leibniz rule `letterDeriv_mul`. -/
noncomputable def letterDeriv (L : ℕ) : CohField →+ CohField where
  toFun x := (dualLift L x).snd
  map_zero' := by simp
  map_add' x y := by simp [TrivSqZeroExt.snd_add]

theorem letterDeriv_mul (L : ℕ) (x y : CohField) :
    letterDeriv L (x * y) = x * letterDeriv L y + y * letterDeriv L x := by
  change (dualLift L (x * y)).snd = x * (dualLift L y).snd + y * (dualLift L x).snd
  rw [map_mul, TrivSqZeroExt.snd_mul, fst_dualLift, fst_dualLift]
  simp [Algebra.smul_def, mul_comm]

theorem letterDeriv_one (L : ℕ) : letterDeriv L 1 = 0 := by
  change (dualLift L 1).snd = 0
  simp

theorem letterDeriv_apply_letter (L j : ℕ) :
    letterDeriv L (cohLetters j) = if j = L then 1 else 0 := by
  change (dualLift L (algebraMap CohRing CohField (X j))).snd = _
  simp only [dualLift, IsLocalization.lift_eq, dualHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, pderiv_X, Pi.single_apply]
  by_cases h : j = L <;> simp [h, eq_comm]

theorem letterDeriv_eq_zero_of_mem {L : ℕ} {x : CohField} (hx : x ∈ letterField L) :
    letterDeriv L x = 0 := by
  induction hx using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    rw [letterDeriv_apply_letter, if_neg (by simp at hj; omega)]
  | one => exact letterDeriv_one L
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | mul x y _ _ hx hy => rw [letterDeriv_mul, hx, hy]; simp
  | inv x _ hx =>
    by_cases h0 : x = 0
    · simp [h0]
    · have := letterDeriv_mul L x x⁻¹
      rw [mul_inv_cancel₀ h0, letterDeriv_one, hx, mul_zero, add_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left h0

/-- The coefficientwise derivative of a power series. -/
noncomputable def dSeries (L : ℕ) (f : PowerSeries CohField) : PowerSeries CohField :=
  PowerSeries.mk fun n => letterDeriv L (PowerSeries.coeff n f)

@[simp] theorem coeff_dSeries (L : ℕ) (f : PowerSeries CohField) (n : ℕ) :
    PowerSeries.coeff n (dSeries L f) = letterDeriv L (PowerSeries.coeff n f) := by
  simp [dSeries]

theorem letterDeriv_coeff_mul (L : ℕ) (f g : PowerSeries CohField) (n : ℕ) :
    letterDeriv L (PowerSeries.coeff n (f * g)) =
      PowerSeries.coeff n (dSeries L f * g) + PowerSeries.coeff n (f * dSeries L g) := by
  simp only [PowerSeries.coeff_mul, map_sum, ← Finset.sum_add_distrib, coeff_dSeries,
    letterDeriv_mul]
  refine Finset.sum_congr rfl fun p _ => by ring

theorem dSeries_letterSeries (L : ℕ) : dSeries L letterSeries = PowerSeries.X ^ L := by
  ext n
  rw [coeff_dSeries, PowerSeries.coeff_X_pow]
  simp only [letterSeries, seriesOf, PowerSeries.coeff_mk, letterDeriv_apply_letter]

end SkewCoframeRigidity.FixedCap
