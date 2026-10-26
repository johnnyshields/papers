/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.ClippedOperator
import Mathlib.Algebra.Field.Subfield.Defs

/-!
# The clipped operator over a subfield

If `G`, `C` have all coefficients in a subfield and `u` has its first `M` coefficients there, the
clipped operator `𝒯_{G,C}(u)` has all coefficients in the subfield.  Used by the field descent
of `cor:stationary-field-descent` in `shields-2026-skew-coframe-rigidity.tex`.  Sorry-free.
-/

namespace SkewCoframeRigidity

open Polynomial

variable {L : Type*} [Field L] (S : Subfield L)

theorem coeff_mul_poly_mem (G H : L[X]) (hG : ∀ k, G.coeff k ∈ S) (hH : ∀ k, H.coeff k ∈ S)
    (k : ℕ) : (G * H).coeff k ∈ S := by
  rw [Polynomial.coeff_mul]
  exact S.sum_mem fun x _ => S.mul_mem (hG _) (hH _)

theorem lowMem_mul {M : ℕ} (u v : PowerSeries L) (hu : ∀ k < M, u.coeff k ∈ S)
    (hv : ∀ k < M, v.coeff k ∈ S) : ∀ k < M, (u * v).coeff k ∈ S := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hu _ ?_) (hv _ ?_) <;>
    · rw [Finset.mem_antidiagonal] at hx
      omega

theorem lowMem_pow {M : ℕ} (u : PowerSeries L) (hu : ∀ k < M, u.coeff k ∈ S) (p : ℕ) :
    ∀ k < M, (u ^ p).coeff k ∈ S := by
  induction p with
  | zero =>
    intro k _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  | succ p ih =>
    rw [pow_succ]
    exact lowMem_mul S _ _ ih hu

theorem lowMem_X_mul {M : ℕ} (u : PowerSeries L) (hu : ∀ k < M, u.coeff k ∈ S) :
    ∀ k < M, (PowerSeries.X * u).coeff k ∈ S := by
  intro k hk
  rcases k with _ | k
  · simp only [PowerSeries.coeff_zero_X_mul]; exact S.zero_mem
  · rw [PowerSeries.coeff_succ_X_mul]; exact hu _ (by omega)

theorem trunc_mul_coeff_mem {M : ℕ} (u : PowerSeries L) (G : L[X]) (hu : ∀ k < M, u.coeff k ∈ S)
    (hG : ∀ k, G.coeff k ∈ S) (k : ℕ) :
    (PowerSeries.trunc M (u * (G : PowerSeries L))).coeff k ∈ S := by
  rw [PowerSeries.coeff_trunc]
  split_ifs with hk
  · rw [PowerSeries.coeff_mul]
    refine S.sum_mem fun x hx => S.mul_mem (hu _ ?_) ?_
    · rw [Finset.mem_antidiagonal] at hx
      omega
    · rw [Polynomial.coeff_coe]; exact hG _
  · exact S.zero_mem

theorem clippedOp_coeff_mem' (M : ℕ) (G C : L[X]) (u : PowerSeries L)
    (hG : ∀ k, G.coeff k ∈ S) (hC : ∀ k, C.coeff k ∈ S) (hu : ∀ k < M, u.coeff k ∈ S)
    (k : ℕ) : (clippedOp M G C u).coeff k ∈ S := by
  unfold clippedOp
  rw [Polynomial.coeff_sub]
  refine S.sub_mem ?_ ?_
  · exact coeff_mul_poly_mem S _ _ hG (trunc_mul_coeff_mem S u C hu hC) k
  · exact coeff_mul_poly_mem S _ _ hC (trunc_mul_coeff_mem S u G hu hG) k

end SkewCoframeRigidity
