/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.LaurentReduction

/-!
# The denominator-only sequence

`reduced_tail_linear_combination` proves `eq:P-linear-combination` for *any* sequence `H`
satisfying the delta recurrence.  What was missing is `H` itself: `eq:H-generating` defines it
as the coefficient sequence of `1/(Q(t) + z t^r)`, and nothing produced one.  Read in
`K[z]⟦t⟧`, the series `mk (ftDenom Q r)` **is** `Q(t) + z t^r` (`mk_ftDenom`), `Q(0) ≠ 0`
makes it a unit, and `H` is its inverse — existing and unique.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Introduction» and «The canonical
Laurent reduction» (`sec:introduction`, `eq:H-generating`; `sec:reduction`,
`eq:P-linear-combination`).

## Tags

denominator sequence, rational generating function, recurrence
-/

namespace ForgacsTran

open Polynomial

variable {𝕜 : Type*} [Field 𝕜]

/-- The `sec:reduction` recurrence in generating-function form. -/
theorem denomConv_eq_iff_mk_mul (d F c : ℕ → Polynomial 𝕜) :
    (∀ M, denomConv d F M = c M)
      ↔ PowerSeries.mk d * PowerSeries.mk F = PowerSeries.mk c := by
  constructor
  · intro h
    rw [← mk_denomConv]
    exact PowerSeries.ext fun m => by
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, h]
  · intro h M
    have hc := congrArg (PowerSeries.coeff M) h
    rw [← mk_denomConv, PowerSeries.coeff_mk, PowerSeries.coeff_mk] at hc
    exact hc

/-- **Paper `eq:H-generating`.**  Read in `K[z]⟦t⟧`, the denominator coefficient sequence is
the pencil itself: `mk (ftDenom Q r) = Q(t) + z t^r`. -/
theorem mk_ftDenom (Q : Polynomial 𝕜) (r : ℕ) :
    PowerSeries.mk (ftDenom Q r)
      = PowerSeries.mk (fun i => Polynomial.C (Q.coeff i))
        + PowerSeries.C (Polynomial.X : Polynomial 𝕜) * PowerSeries.X ^ r := by
  ext i
  rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ftDenom,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases h : i = r
  · simp [h]
  · simp [h]

/-- The pencil is a unit in `K[z]⟦t⟧`, because `Q(0) ≠ 0`. -/
theorem isUnit_mk_ftDenom (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) :
    IsUnit (PowerSeries.mk (ftDenom Q r)) := by
  refine PowerSeries.isUnit_iff_constantCoeff.2 ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, ftDenom,
    if_neg (by omega : (0 : ℕ) ≠ r), add_zero]
  exact (Polynomial.isUnit_C).2 (isUnit_iff_ne_zero.2 hQ0)

/-- The `sec:reduction` recurrence has exactly one solution for each right-hand side. -/
theorem existsUnique_denomConv (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (c : ℕ → Polynomial 𝕜) :
    ∃! F : ℕ → Polynomial 𝕜, ∀ M, denomConv (ftDenom Q r) F M = c M := by
  obtain ⟨v, hv⟩ := isUnit_mk_ftDenom Q hr hQ0
  set D : PowerSeries (Polynomial 𝕜) := PowerSeries.mk (ftDenom Q r) with hD
  set w : PowerSeries (Polynomial 𝕜) := (↑v⁻¹ : PowerSeries (Polynomial 𝕜)) with hw
  have hDw : D * w = 1 := by rw [← hv, hw]; exact v.mul_inv
  have hwD : w * D = 1 := by rw [mul_comm]; exact hDw
  refine ⟨fun M => PowerSeries.coeff M (w * PowerSeries.mk c), ?_, ?_⟩
  · dsimp only
    rw [denomConv_eq_iff_mk_mul]
    have hmk : PowerSeries.mk (fun M => PowerSeries.coeff M (w * PowerSeries.mk c))
        = w * PowerSeries.mk c := PowerSeries.ext fun m => by rw [PowerSeries.coeff_mk]
    rw [hmk, ← hD, ← mul_assoc, hDw, one_mul]
  · intro F hF
    rw [denomConv_eq_iff_mk_mul, ← hD] at hF
    funext M
    have hFw : PowerSeries.mk F = w * PowerSeries.mk c := by
      rw [← hF, ← mul_assoc, hwD, one_mul]
    have h2 := congrArg (PowerSeries.coeff M) hFw
    rwa [PowerSeries.coeff_mk] at h2

/-- **Paper `eq:H-generating`.**  The denominator-only sequence exists and is unique: `H` is
the inverse of the pencil, `(Q(t) + z t^r) ∑_m H_m(z) t^m = 1`. -/
theorem existsUnique_ftH (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) :
    ∃! H : ℕ → Polynomial 𝕜,
      (PowerSeries.mk (fun i => Polynomial.C (Q.coeff i))
        + PowerSeries.C (Polynomial.X : Polynomial 𝕜) * PowerSeries.X ^ r)
        * PowerSeries.mk H = 1 := by
  have h1 : PowerSeries.mk (fun M : ℕ => if M = 0 then (1 : Polynomial 𝕜) else 0) = 1 :=
    PowerSeries.ext fun m => by rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
  obtain ⟨H, hH, huniq⟩ := existsUnique_denomConv Q hr hQ0
    (fun M => if M = 0 then (1 : Polynomial 𝕜) else 0)
  refine ⟨H, ?_, fun H' hH' => ?_⟩
  · dsimp only
    rw [← mk_ftDenom, ← h1, ← denomConv_eq_iff_mk_mul]
    exact hH
  · refine huniq H' ?_
    dsimp only
    rw [denomConv_eq_iff_mk_mul, h1, mk_ftDenom]
    exact hH'

/-- **Paper `eq:P-linear-combination`, with `H` supplied.**  The denominator-only sequence of
`eq:H-generating` exists, the reduced sequence for the weight `B` exists, and the second is
the fixed finite combination `F_M = ∑_j b_j H_{M-j}` of the first. -/
theorem exists_reduced_tail_linear_combination (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (B : Polynomial 𝕜) :
    ∃ H F : ℕ → Polynomial 𝕜,
      (PowerSeries.mk (fun i => Polynomial.C (Q.coeff i))
        + PowerSeries.C (Polynomial.X : Polynomial 𝕜) * PowerSeries.X ^ r)
        * PowerSeries.mk H = 1 ∧
      (∀ M, denomConv (ftDenom Q r) F M = Polynomial.C (B.coeff M)) ∧
      (∀ M, F M = ∑ j ∈ Finset.range (M + 1), Polynomial.C (B.coeff j) * H (M - j)) := by
  have h1 : PowerSeries.mk (fun M : ℕ => if M = 0 then (1 : Polynomial 𝕜) else 0) = 1 :=
    PowerSeries.ext fun m => by rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
  obtain ⟨H, hH, -⟩ := existsUnique_denomConv Q hr hQ0
    (fun M => if M = 0 then (1 : Polynomial 𝕜) else 0)
  obtain ⟨F, hF, -⟩ := existsUnique_denomConv Q hr hQ0 (fun M => Polynomial.C (B.coeff M))
  refine ⟨H, F, ?_, hF, reduced_tail_linear_combination Q hr hQ0 B H F hH hF⟩
  rw [← mk_ftDenom, ← h1, ← denomConv_eq_iff_mk_mul]
  exact hH

end ForgacsTran
