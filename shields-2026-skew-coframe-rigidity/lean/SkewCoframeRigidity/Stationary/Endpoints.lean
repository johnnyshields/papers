/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.ClippedOperator

/-!
# The two retained endpoint coefficients of the clipped operator

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «A finite pole calculation»
(`sc:positive-power`, equation `sc:two-endpoints`).  For polynomials `G`, `C` with constant
term one and a series `u`, the clipped operator `G [uC]_{<M} - C [uG]_{<M}` equals, as a series,
`C [uG]_{≥M} - G [uC]_{≥M}`, so its coefficients at `M` and `M + 1` are read off the discarded
tails.  For `u = z H^p` they are `-E₀` and `-E₁ - G₁ E₀`, where
`E₀ = [H^p Δ]_{M-1}` and `E₁ = [H^p Δ]_M - Δ₁ [H^p G]_{M-1}`, `Δ = C - G`.  Sorry-free.
-/

namespace SkewCoframeRigidity

open PowerSeries
open scoped Polynomial

variable {R : Type*} [CommRing R]

/-- The discarded tail `f - [f]_{<M}` of a series. -/
noncomputable def tailSeries (M : ℕ) (f : R⟦X⟧) : R⟦X⟧ := f - (trunc M f : R⟦X⟧)

theorem coeff_tailSeries_lt (M : ℕ) (f : R⟦X⟧) {j : ℕ} (hj : j < M) :
    coeff j (tailSeries M f) = 0 := by
  simp [tailSeries, Polynomial.coeff_coe, coeff_trunc, hj]

theorem coeff_tailSeries_ge (M : ℕ) (f : R⟦X⟧) {j : ℕ} (hj : M ≤ j) :
    coeff j (tailSeries M f) = coeff j f := by
  simp [tailSeries, Polynomial.coeff_coe, coeff_trunc, not_lt.mpr hj]

/-- The clipped operator is `C [uG]_{≥M} - G [uC]_{≥M}` as a series. -/
theorem clippedOp_coe_eq_tail (M : ℕ) (G C : R[X]) (u : R⟦X⟧) :
    (clippedOp M G C u : R⟦X⟧) =
      (C : R⟦X⟧) * tailSeries M (u * (G : R⟦X⟧)) -
        (G : R⟦X⟧) * tailSeries M (u * (C : R⟦X⟧)) := by
  unfold clippedOp tailSeries
  push_cast
  ring

private theorem coeff_mul_tail_M (M : ℕ) (P : R[X]) (f : R⟦X⟧) :
    coeff M ((P : R⟦X⟧) * tailSeries M f) = P.coeff 0 * coeff M f := by
  rw [coeff_mul, Finset.sum_eq_single (0, M)]
  · simp [Polynomial.coeff_coe, coeff_tailSeries_ge M f le_rfl]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    have : j < M := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have : j = M := by simpa using hij
        subst this
        exact absurd rfl hne
      · simp only at hij; omega
    simp [coeff_tailSeries_lt M f this]
  · simp

private theorem coeff_mul_tail_succ (M : ℕ) (P : R[X]) (f : R⟦X⟧) :
    coeff (M + 1) ((P : R⟦X⟧) * tailSeries M f) =
      P.coeff 0 * coeff (M + 1) f + P.coeff 1 * coeff M f := by
  rw [coeff_mul, ← Finset.sum_subset (s₁ := {(0, M + 1), (1, M)})]
  · rw [Finset.sum_pair (by simp)]
    simp [Polynomial.coeff_coe, coeff_tailSeries_ge M f (show M ≤ M + 1 by omega),
      coeff_tailSeries_ge M f le_rfl]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [add_comm]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    have : j < M := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at hne
      simp only at hij
      by_contra hc
      apply hne.elim <;> intro h <;> omega
    simp [coeff_tailSeries_lt M f this]

/-- The coefficient of the clipped operator at the cutoff `M`. -/
theorem coeff_clippedOp_cutoff (M : ℕ) (G C : R[X]) (u : R⟦X⟧) :
    (clippedOp M G C u).coeff M =
      C.coeff 0 * coeff M (u * (G : R⟦X⟧)) - G.coeff 0 * coeff M (u * (C : R⟦X⟧)) := by
  have := congrArg (coeff M) (clippedOp_coe_eq_tail M G C u)
  rw [Polynomial.coeff_coe, map_sub, coeff_mul_tail_M, coeff_mul_tail_M] at this
  exact this

/-- The coefficient of the clipped operator at `M + 1`. -/
theorem coeff_clippedOp_succ (M : ℕ) (G C : R[X]) (u : R⟦X⟧) :
    (clippedOp M G C u).coeff (M + 1) =
      (C.coeff 0 * coeff (M + 1) (u * (G : R⟦X⟧)) + C.coeff 1 * coeff M (u * (G : R⟦X⟧))) -
        (G.coeff 0 * coeff (M + 1) (u * (C : R⟦X⟧)) + G.coeff 1 * coeff M (u * (C : R⟦X⟧))) := by
  have := congrArg (coeff (M + 1)) (clippedOp_coe_eq_tail M G C u)
  rw [Polynomial.coeff_coe, map_sub, coeff_mul_tail_succ, coeff_mul_tail_succ] at this
  exact this

/-- `E₀ = [s Δ]_{M-1}` with `Δ = C - G`, the first endpoint (`sc:two-endpoints`). -/
noncomputable def endpointZero (M : ℕ) (G C : R[X]) (s : R⟦X⟧) : R :=
  coeff (M - 1) (s * ((C - G : R[X]) : R⟦X⟧))

/-- `E₁ = [s Δ]_M - Δ₁ [s G]_{M-1}`, the second endpoint (`sc:two-endpoints`). -/
noncomputable def endpointOne (M : ℕ) (G C : R[X]) (s : R⟦X⟧) : R :=
  coeff M (s * ((C - G : R[X]) : R⟦X⟧)) - (C - G).coeff 1 * coeff (M - 1) (s * (G : R⟦X⟧))

/-- `[𝒯(z s)]_M = -E₀` for polynomials with constant term one. -/
theorem coeff_clippedOp_shift_cutoff (M : ℕ) (hM : 1 ≤ M) (G C : R[X]) (s : R⟦X⟧)
    (hG : G.coeff 0 = 1) (hC : C.coeff 0 = 1) :
    (clippedOp M G C (PowerSeries.X * s)).coeff M = -endpointZero M G C s := by
  rw [coeff_clippedOp_cutoff, hG, hC, mul_assoc, mul_assoc]
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  simp only [endpointZero, Nat.add_sub_cancel, Polynomial.coe_sub, mul_sub, map_sub,
    coeff_succ_X_mul]
  ring

/-- `[𝒯(z s)]_{M+1} = -E₁ - G₁ E₀` for polynomials with constant term one. -/
theorem coeff_clippedOp_shift_succ (M : ℕ) (hM : 1 ≤ M) (G C : R[X]) (s : R⟦X⟧)
    (hG : G.coeff 0 = 1) (hC : C.coeff 0 = 1) :
    (clippedOp M G C (PowerSeries.X * s)).coeff (M + 1) =
      -endpointOne M G C s - G.coeff 1 * endpointZero M G C s := by
  rw [coeff_clippedOp_succ, hG, hC, mul_assoc, mul_assoc]
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  simp only [endpointZero, endpointOne, Nat.add_sub_cancel, Polynomial.coe_sub, mul_sub, map_sub,
    coeff_succ_X_mul, Polynomial.coeff_sub]
  ring

end SkewCoframeRigidity
