/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Defs

/-!
# Coframe polynomials with prescribed exponents

Formalizes the polynomial shape shared by the complete right coframe `G_B` and the complete left
coframe `C_K` of `shields-2026-skew-coframe-rigidity.tex` («Rigidity with the same literal cap»,
`sc:splice-identity`): a polynomial `1 + ∑ g_j z^{s_j}`.  The coefficient of a power-series
product against such a polynomial is computed in terms of the coherent letters.  Sorry-free.
-/

namespace SkewCoframeRigidity.FixedCap

open SkewCoframeRigidity.Coframe Polynomial
open scoped Polynomial

variable {L : Type*} {n : ℕ}

/-- The polynomial `1 + ∑ g_j z^{s_j}` with an arbitrary coefficient vector and exponent vector. -/
noncomputable def capPoly [CommRing L] (g : Fin n → L) (s : Fin n → ℕ) : L[X] :=
  1 + ∑ j, C (g j) * X ^ s j

section Letters

variable [Zero L]

theorem letterOf_neg_eq (h : ℕ → L) {m : ℤ} (hm : m < 0) : letterOf h m = 0 := by
  simp [letterOf, hm]

theorem letterOf_nonneg_eq (h : ℕ → L) {m : ℤ} (hm : 0 ≤ m) : letterOf h m = h m.toNat := by
  simp [letterOf, not_lt.mpr hm]

theorem letterOf_natCast_eq (h : ℕ → L) (m : ℕ) : letterOf h (m : ℤ) = h m := by
  simp [letterOf_nonneg_eq h (Int.natCast_nonneg m)]

end Letters

section CommRing

variable [CommRing L]

/-- The coefficient of `H · (1 + ∑ g_j z^{s_j})` at `k`, for an arbitrary letter sequence. -/
theorem coeff_mk_mul_capPoly (f : ℕ → L) (g : Fin n → L) (s : Fin n → ℕ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk f * (capPoly g s : PowerSeries L)) =
      f k + ∑ j, g j * letterOf f ((k : ℤ) - s j) := by
  unfold capPoly
  have hsum : ((∑ j, C (g j) * X ^ s j : L[X]) : PowerSeries L) =
      ∑ j, ((C (g j) * X ^ s j : L[X]) : PowerSeries L) :=
    map_sum (Polynomial.coeToPowerSeries.ringHom (R := L)) _ _
  rw [Polynomial.coe_add, Polynomial.coe_one, mul_add, mul_one, map_add, PowerSeries.coeff_mk]
  congr 1
  rw [hsum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
    mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  by_cases hs : s j ≤ k
  · have e : ((k : ℤ) - s j).toNat = k - s j := by omega
    have : letterOf f ((k : ℤ) - s j) = f (k - s j) := by
      simp [letterOf, show ¬ ((k : ℤ) - s j < 0) by omega, e]
    rw [this]
    simp [hs]
  · have : letterOf f ((k : ℤ) - s j) = 0 := by
      simp [letterOf, show ((k : ℤ) - s j < 0) by omega]
    rw [this]
    simp [hs]

/-- Reading the coefficient sequence of a series back as letters. -/
theorem letterOf_coeff (F : PowerSeries L) {m : ℤ} (hm : 0 ≤ m) :
    letterOf (fun i => PowerSeries.coeff i F) m = PowerSeries.coeff m.toNat F := by
  simp [letterOf, not_lt.mpr hm]

end CommRing

end SkewCoframeRigidity.FixedCap
