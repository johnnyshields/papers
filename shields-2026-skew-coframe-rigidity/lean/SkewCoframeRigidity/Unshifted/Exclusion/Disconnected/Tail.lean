/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.YExpansion

/-!
# The low coefficients of a clipped alternating operator

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner).  For polynomials `a`, `b` vanishing below
orders `A < B` the operator `𝒯_{a,b}(u)` vanishes below degree `M + A` and its coefficient at
`M + A` is `-a_A [u b]_M`.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries Polynomial SkewCoframeRigidity

variable {K : Type*} [CommRing K]

/-- The operator is the difference of the two shifted tails. -/
theorem clippedOp_eq_tails (M : ℕ) (a b : K[X]) (u : K⟦X⟧) :
    ((clippedOp M a b u : K[X]) : K⟦X⟧) =
      PowerSeries.X ^ M * ((b : K⟦X⟧) * mk (fun i => coeff (i + M) (u * (a : K⟦X⟧))) -
        (a : K⟦X⟧) * mk (fun i => coeff (i + M) (u * (b : K⟦X⟧)))) := by
  have ha := PowerSeries.eq_shift_mul_X_pow_add_trunc M (u * (a : K⟦X⟧))
  have hb := PowerSeries.eq_shift_mul_X_pow_add_trunc M (u * (b : K⟦X⟧))
  unfold clippedOp
  rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul]
  have e1 : ((PowerSeries.trunc M (u * (b : K⟦X⟧)) : K[X]) : K⟦X⟧) =
      u * (b : K⟦X⟧) - mk (fun i => coeff (i + M) (u * (b : K⟦X⟧))) * PowerSeries.X ^ M := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hb.symm
  have e2 : ((PowerSeries.trunc M (u * (a : K⟦X⟧)) : K[X]) : K⟦X⟧) =
      u * (a : K⟦X⟧) - mk (fun i => coeff (i + M) (u * (a : K⟦X⟧))) * PowerSeries.X ^ M := by
    rw [eq_sub_iff_add_eq, add_comm]; exact ha.symm
  rw [e1, e2]
  ring

/-- Below degree `M + A` the operator vanishes, and at `M + A` its coefficient is `-a_A [u b]_M`. -/
theorem coeff_clippedOp_low (M A B : ℕ) (hAB : A < B) (a b : K[X]) (u : K⟦X⟧)
    (ha : ∀ i < A, a.coeff i = 0) (hb : ∀ j < B, b.coeff j = 0) :
    (∀ n < M + A, (clippedOp M a b u).coeff n = 0) ∧
      (clippedOp M a b u).coeff (M + A) = -(a.coeff A * coeff M (u * (b : K⟦X⟧))) := by
  have key : ∀ n, (clippedOp M a b u).coeff n =
      if M ≤ n then coeff (n - M) ((b : K⟦X⟧) * mk (fun i => coeff (i + M) (u * (a : K⟦X⟧))) -
        (a : K⟦X⟧) * mk (fun i => coeff (i + M) (u * (b : K⟦X⟧)))) else 0 := by
    intro n
    rw [← Polynomial.coeff_coe, clippedOp_eq_tails, PowerSeries.coeff_X_pow_mul']
  have hlow : ∀ k ≤ A, coeff k ((b : K⟦X⟧) * mk (fun i => coeff (i + M) (u * (a : K⟦X⟧))) -
        (a : K⟦X⟧) * mk (fun i => coeff (i + M) (u * (b : K⟦X⟧)))) =
      if k = A then -(a.coeff A * coeff M (u * (b : K⟦X⟧))) else 0 := by
    intro k hk
    rw [map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    have h1 : ∑ x ∈ Finset.antidiagonal k, coeff x.1 (b : K⟦X⟧) *
        coeff x.2 (mk (fun i => coeff (i + M) (u * (a : K⟦X⟧)))) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have : x.1 < B := by have := Finset.mem_antidiagonal.mp hx; omega
      rw [Polynomial.coeff_coe, hb _ this, zero_mul]
    have h2 : ∑ x ∈ Finset.antidiagonal k, coeff x.1 (a : K⟦X⟧) *
        coeff x.2 (mk (fun i => coeff (i + M) (u * (b : K⟦X⟧)))) =
        if k = A then a.coeff A * coeff M (u * (b : K⟦X⟧)) else 0 := by
      by_cases hkA : k = A
      · subst hkA
        rw [ite_eq_left rfl, Finset.sum_eq_single (k, 0)]
        · simp
        · intro x hx hne
          have hx' := Finset.mem_antidiagonal.mp hx
          have : x.1 < k := by
            by_contra hcon
            apply hne
            ext <;> simp <;> omega
          rw [Polynomial.coeff_coe, ha _ this, zero_mul]
        · intro hn; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hn
      · rw [ite_eq_right hkA]
        refine Finset.sum_eq_zero fun x hx => ?_
        have : x.1 < A := by have := Finset.mem_antidiagonal.mp hx; omega
        rw [Polynomial.coeff_coe, ha _ this, zero_mul]
    rw [h1, h2]
    split_ifs <;> simp
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [key]
    split_ifs with hM
    · rw [hlow _ (by omega), ite_eq_right (by omega)]
    · rfl
  · rw [key, ite_eq_left (by omega), Nat.add_sub_cancel_left, hlow _ le_rfl, ite_eq_left rfl]

end SkewCoframeRigidity.Unshifted
