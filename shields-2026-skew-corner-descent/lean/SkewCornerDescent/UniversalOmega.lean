/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.AlphabetSeparation
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Full series of the original Schur involution

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The elementary sequence is the constant-unit inverse of the complete sequence
at the negative variable. Its coefficients are the existing recursive elementary
functions, with no finite-alphabet cutoff. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- Complete generator series in the original polynomial ring. -/
noncomputable def universalCompleteSeries : PowerSeries Lambda :=
  PowerSeries.mk hPos

/-- The full elementary generator series, formed by an actual constant-unit inverse. -/
noncomputable def universalElementarySeries : PowerSeries Lambda :=
  PowerSeries.invOfUnit (PowerSeries.rescale (-1 : Lambda) universalCompleteSeries) 1

/-- Every original series coefficient is the existing complete generator sequence. -/
theorem universal_complete_coeff_nat (n : ℕ) :
    PowerSeries.coeff n universalCompleteSeries = hPos n := by
  exact PowerSeries.coeff_mk n hPos

/-- The original complete series has constant coefficient one. -/
theorem universal_complete_constant : PowerSeries.constantCoeff universalCompleteSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, universal_complete_coeff_nat, hPos_zero]

/-- Every positive complete coefficient is the original generator. -/
theorem universal_complete_coeff (n : ℕ+) :
    PowerSeries.coeff (n : ℕ) universalCompleteSeries = X n := by
  rw [universal_complete_coeff_nat, hPos_pnat]

/-- The actual elementary series is normalized. -/
theorem universal_elementary_constant :
    PowerSeries.constantCoeff universalElementarySeries = 1 := by
  simp only [universalElementarySeries, PowerSeries.constantCoeff_invOfUnit,
    inv_one, Units.val_one]

/-- The complete and elementary series satisfy the exact full inverse identity. -/
theorem universal_elementary_complete_product :
    universalElementarySeries * PowerSeries.rescale (-1 : Lambda) universalCompleteSeries = 1 := by
  apply PowerSeries.invOfUnit_mul
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    universal_complete_constant, Units.val_one]

/-- The existing recursive elementary sequence satisfies the full inverse
identity in the same original polynomial ring. -/
theorem recursive_negative_elementary_product :
    PowerSeries.rescale (-1 : Lambda) (PowerSeries.mk elem) * universalCompleteSeries = 1 := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i
      (PowerSeries.rescale (-1 : Lambda) (PowerSeries.mk elem)) *
      PowerSeries.coeff j universalCompleteSeries)]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_mk, universal_complete_coeff_nat]
  by_cases hn : n = 0
  · subst n
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.sub_self,
      elem, hPos_zero, mul_one, PowerSeries.coeff_one, ite_true]
  · rw [PowerSeries.coeff_one, ite_eq_right hn]
    exact altConv_elem_hPos n (Nat.pos_of_ne_zero hn)

/-- Uniqueness of the full series inverse identifies the polynomial and recursive
elementary constructions, without relying on any finite alphabet. -/
theorem universal_elementary_eq_recursive :
    universalElementarySeries = PowerSeries.mk elem := by
  have h := congrArg (PowerSeries.rescale (-1 : Lambda))
    recursive_negative_elementary_product
  have hi : PowerSeries.mk elem *
      PowerSeries.rescale (-1 : Lambda) universalCompleteSeries = 1 := by
    simpa only [map_mul, map_one, PowerSeries.rescale_rescale, neg_mul_neg,
      one_mul, PowerSeries.rescale_one, RingHom.id_apply] using h
  calc
    universalElementarySeries = universalElementarySeries * 1 := (mul_one _).symm
    _ = universalElementarySeries *
        (PowerSeries.rescale (-1 : Lambda) universalCompleteSeries * PowerSeries.mk elem) := by
      rw [mul_comm _ (PowerSeries.mk elem), hi]
    _ = PowerSeries.mk elem := by
      rw [← mul_assoc, universal_elementary_complete_product, one_mul]

/-- Every full power-series elementary coefficient is the existing elementary function. -/
theorem universal_elementary_coeff (n : ℕ) :
    PowerSeries.coeff n universalElementarySeries = elem n := by
  rw [universal_elementary_eq_recursive, PowerSeries.coeff_mk]

/-- The existing original-ring Schur involution is an algebra automorphism. -/
noncomputable def schurInvolutionEquiv : Lambda ≃ₐ[ℚ] Lambda := by
  have h : schurInvolution.comp schurInvolution = AlgHom.id ℚ Lambda :=
    AlgHom.ext schurInvolution_involutive
  exact AlgEquiv.ofAlgHom schurInvolution schurInvolution h h

/-- The algebra equivalence uses the existing original-ring Schur involution. -/
theorem schurInvolutionEquiv_apply (f : Lambda) :
    schurInvolutionEquiv f = schurInvolution f := rfl

end SkewCornerDescent
