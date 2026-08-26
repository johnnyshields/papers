/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Shields.Analysis.Calculus.TaylorCoeff

/-!
# Coefficient extraction at a dominant simple pole

The proposition reads the coefficient asymptotics of `B/D` off a single pole.
Subtracting the pole at the dominant root `t(z)` leaves a remainder analytic on a
larger disk, and the two halves are:

## Main statements

* `taylorCoeff_inv_sub` — the extraction itself,
  `[t^M](t - τ)^{-1} = -τ^{-M-1}`, from the closed form of the iterated
  derivative of `(t - τ)^{-1}`;
* `norm_taylorCoeff_le` — Cauchy's estimate on the remainder,
  `|[t^M] E| ≤ C/R^M` for `E` bounded by `C` on `|t| = R`.

## Implementation notes

`coeff_of_simple_pole` combines them into `eq:isolated-dominant-expansion`:
`τ^{M+1}[t^M]F = -A + O((‖τ‖/R)^M)`, with the constant named.

The hypothesis `hF` — that `B/D - A/(t - t(z))` extends analytically past the
dominant root — is discharged in `AttractorPole` by polynomial division, and the
branch `t(z)` comes from `AttractorBranch`.  What is proved here is the
coefficient calculus those two are fed into.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`,
`prop:isolated-dominant-cancellation`, `eq:isolated-dominant-expansion`).

## Tags

simple pole, coefficient extraction, dominant pole, partial fractions
-/

namespace ForgacsTran

open Complex Metric Shields

/-! ### The iterated derivative of a simple pole -/

/-- Away from the pole, `(w - τ)^{-1}` has the classical iterated derivative,
written here as `-m! (τ - w)^{-(m+1)}`.  Differentiation is local, so the point
of nondifferentiability does not interfere. -/
theorem iteratedDeriv_inv_sub (τ : ℂ) (m : ℕ) {t : ℂ} (ht : t ≠ τ) :
    iteratedDeriv m (fun w : ℂ => (w - τ)⁻¹) t
      = -((Nat.factorial m : ℕ) : ℂ) * ((τ - t) ^ (m + 1)) ⁻¹ := by
  induction m generalizing t with
  | zero =>
    have hsub : τ - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one]
    rw [show t - τ = -(τ - t) by ring, inv_neg]
    ring
  | succ m ih =>
    have hopen : IsOpen {w : ℂ | w ≠ τ} := isOpen_ne
    have hnhds : {w : ℂ | w ≠ τ} ∈ nhds t := hopen.mem_nhds ht
    have heq : iteratedDeriv m (fun w : ℂ => (w - τ)⁻¹)
        =ᶠ[nhds t] fun w : ℂ => -((Nat.factorial m : ℕ) : ℂ) * ((τ - w) ^ (m + 1))⁻¹ :=
      Filter.eventually_of_mem hnhds fun w hw => ih hw
    have hsub : τ - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have hpow : (τ - t) ^ (m + 1) ≠ 0 := pow_ne_zero _ hsub
    have hbase : HasDerivAt (fun w : ℂ => τ - w) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub τ
    have hd1 : HasDerivAt (fun w : ℂ => (τ - w) ^ (m + 1))
        (((m + 1 : ℕ) : ℂ) * (τ - t) ^ (m + 1 - 1) * (-1)) t := hbase.pow (m + 1)
    have hd2 : HasDerivAt (fun w : ℂ => -((Nat.factorial m : ℕ) : ℂ) * ((τ - w) ^ (m + 1))⁻¹)
        (-((Nat.factorial m : ℕ) : ℂ) *
          (-(((m + 1 : ℕ) : ℂ) * (τ - t) ^ (m + 1 - 1) * (-1)) / ((τ - t) ^ (m + 1)) ^ 2)) t :=
      (hd1.inv hpow).const_mul _
    rw [iteratedDeriv_succ, heq.deriv_eq, hd2.deriv, Nat.factorial_succ]
    push_cast
    field

/-- **Paper `prop:isolated-dominant-cancellation` — the coefficient extraction.**
`[t^M](t - τ)^{-1} = -τ^{-M-1}`. -/
theorem taylorCoeff_inv_sub {τ : ℂ} (hτ : τ ≠ 0) (M : ℕ) :
    taylorCoeff (fun t : ℂ => (t - τ)⁻¹) M = -(τ ^ (M + 1))⁻¹ := by
  have h0 : (0 : ℂ) ≠ τ := fun h => hτ h.symm
  have hfac : ((Nat.factorial M : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
  have hτp : τ ^ (M + 1) ≠ 0 := pow_ne_zero _ hτ
  rw [taylorCoeff, iteratedDeriv_inv_sub τ M h0, sub_zero]
  field_simp

/-! ### Cauchy's estimate on the remainder -/

/-- **Cauchy's estimate, in coefficient form.**  A function bounded by `C` on
`|t| = R` has `|[t^M] E| ≤ C/R^M`.  This is the `O(η^M)` of
`eq:isolated-dominant-expansion` once `R` is chosen past the dominant root. -/
theorem norm_taylorCoeff_le {E : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hE : DiffContOnCl ℂ E (ball (0 : ℂ) R))
    (hC : ∀ w ∈ sphere (0 : ℂ) R, ‖E w‖ ≤ C) (M : ℕ) :
    ‖taylorCoeff E M‖ ≤ C / R ^ M := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le M hR hE hC
  have hfac : (0 : ℝ) < (Nat.factorial M : ℝ) := by exact_mod_cast Nat.factorial_pos M
  rw [taylorCoeff, norm_mul, norm_inv]
  have hcast : ‖((Nat.factorial M : ℕ) : ℂ)‖ = (Nat.factorial M : ℝ) := by simp
  rw [hcast, inv_mul_le_iff₀ hfac]
  calc ‖iteratedDeriv M E 0‖ ≤ (Nat.factorial M : ℝ) * C / R ^ M := h
    _ = (Nat.factorial M : ℝ) * (C / R ^ M) := by ring

/-! ### The expansion -/

/-- **Paper `eq:isolated-dominant-expansion`.**  If `F` is a simple pole of
amplitude `A` at `τ` plus a remainder analytic on `|t| ≤ R`, then
`τ^{M+1}[t^M]F = -A` up to a remainder of size `‖τ‖ C (‖τ‖/R)^M`.  With `τ` the
dominant root and `R` a separating radius, `‖τ‖/R < 1` and the remainder is the
proposition's `O(η^M)`. -/
theorem coeff_of_simple_pole {τ A : ℂ} {E F : ℂ → ℂ} {R C : ℝ}
    (hτ : τ ≠ 0) (hR : 0 < R)
    (hE : DiffContOnCl ℂ E (ball (0 : ℂ) R))
    (hC : ∀ w ∈ sphere (0 : ℂ) R, ‖E w‖ ≤ C)
    (hEan : AnalyticAt ℂ E 0)
    (hF : ∀ t, F t = A * (t - τ)⁻¹ + E t) (M : ℕ) :
    τ ^ (M + 1) * taylorCoeff F M = -A + τ ^ (M + 1) * taylorCoeff E M ∧
      ‖τ ^ (M + 1) * taylorCoeff E M‖ ≤ ‖τ‖ * C * (‖τ‖ / R) ^ M := by
  have h0 : (0 : ℂ) ≠ τ := fun h => hτ h.symm
  have hsub : (0 : ℂ) - τ ≠ 0 := sub_ne_zero.mpr h0
  have hpole : AnalyticAt ℂ (fun t : ℂ => A * (t - τ)⁻¹) 0 :=
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv hsub)
  have hFeq : F = fun t => A * (t - τ)⁻¹ + E t := funext hF
  have hsplit : taylorCoeff F M = A * -(τ ^ (M + 1))⁻¹ + taylorCoeff E M := by
    rw [hFeq, taylorCoeff, iteratedDeriv_fun_add hpole.contDiffAt hEan.contDiffAt,
      mul_add, ← taylorCoeff, ← taylorCoeff]
    congr 1
    rw [taylorCoeff, iteratedDeriv_const_mul_field, ← mul_assoc,
      mul_comm ((((Nat.factorial M : ℕ)) : ℂ))⁻¹ A, mul_assoc, ← taylorCoeff,
      taylorCoeff_inv_sub hτ]
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    have hτp : τ ^ (M + 1) ≠ 0 := pow_ne_zero _ hτ
    field_simp
  · have hbound := norm_taylorCoeff_le hR hE hC M
    have hRM : (0 : ℝ) < R ^ M := pow_pos hR M
    rw [norm_mul, norm_pow]
    calc ‖τ‖ ^ (M + 1) * ‖taylorCoeff E M‖ ≤ ‖τ‖ ^ (M + 1) * (C / R ^ M) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ‖τ‖ * C * (‖τ‖ / R) ^ M := by
          rw [div_pow, pow_succ]
          field_simp

end ForgacsTran
