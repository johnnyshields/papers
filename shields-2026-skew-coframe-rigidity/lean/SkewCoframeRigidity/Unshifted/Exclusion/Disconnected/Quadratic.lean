/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Tail
import SkewCoframeRigidity.Unshifted.Endpoints

/-!
# The quadratic and linear equations at their lowest coefficient

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner).  `defectExpr M p h a b` is the series
`𝓔^M_{a∧b} + p (ϑ^{p-1} - h^{p-1}) z^{M-1} (a - b)`.  When `a` vanishes below order `A` and
`b` below order `B > A`, its lowest possibly nonzero coefficient is at `M + A`, and there it is
the coordinate `α_{F,p}` of the component carrying `b`.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries SkewCoframeRigidity SkewCoframeRigidity.Coframe
open Polynomial hiding coeff

variable {K : Type*} [Field K]

/-- `𝓔^M_{a∧b} + p (ϑ^{p-1} - h^{p-1}) z^{M-1} (a - b)` as a power series. -/
noncomputable def defectExpr (M p : ℕ) (h : ℕ → K) (a b : K[X]) : K⟦X⟧ :=
  ((clippedOp M a b (seriesOf h ^ p) : K[X]) : K⟦X⟧) -
    PowerSeries.C (p : K) * seriesOf h ^ (p - 1) * ((clippedOp M a b (seriesOf h) : K[X]) : K⟦X⟧) +
    PowerSeries.C (p : K) * (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1)) *
      PowerSeries.X ^ (M - 1) * ((a : K⟦X⟧) - (b : K⟦X⟧))

theorem coeff_mul_low {f g : K⟦X⟧} {N : ℕ} (hg : ∀ k < N, coeff k g = 0) :
    (∀ n < N, coeff n (f * g) = 0) ∧ coeff N (f * g) = constantCoeff f * coeff N g := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [hg x.2 (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, N)]
    · simp
    · intro x hx hne
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have : x.2 < N := by
        by_contra hcon
        apply hne
        refine Prod.ext ?_ ?_ <;> simp <;> omega
      rw [hg _ this, mul_zero]
    · intro hn; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hn

/-- The coefficient of the defect expression at `M + A`. -/
theorem coeff_defectExpr_low (M A B p : ℕ) (hp : 2 ≤ p) (hM : 1 ≤ M) (hAB : A < B)
    (h : ℕ → K) (a b : K[X]) (ha : ∀ i < A, a.coeff i = 0) (hb : ∀ j < B, b.coeff j = 0) :
    (∀ n < M + A, coeff n (defectExpr M p h a b) = 0) ∧
    coeff (M + A) (defectExpr M p h a b) = -(a.coeff A *
      (coeff M (seriesOf h ^ p * (b : K⟦X⟧)) -
        (p : K) * h 0 ^ (p - 1) * coeff M (seriesOf h * (b : K⟦X⟧)) +
        (p : K) * ((p - 1 : ℕ) : K) * h 0 ^ (p - 2) * h 1)) := by
  obtain ⟨hl1, hc1⟩ := coeff_clippedOp_low M A B hAB a b (seriesOf h ^ p) ha hb
  obtain ⟨hl2, hc2⟩ := coeff_clippedOp_low M A B hAB a b (seriesOf h) ha hb
  have hab : ∀ k < A, coeff k ((a : K⟦X⟧) - (b : K⟦X⟧)) = 0 := by
    intro k hk
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, ha k hk, hb k (by omega), sub_zero]
  have habA : coeff A ((a : K⟦X⟧) - (b : K⟦X⟧)) = a.coeff A := by
    rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, hb A hAB, sub_zero]
  set Cc : K⟦X⟧ := PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1) with hCc
  have hcz : constantCoeff Cc = 0 := by simp [hCc, seriesOf]
  have hc1' : coeff 1 Cc = -(((p - 1 : ℕ) : K) * h 0 ^ (p - 2) * h 1) := by
    rw [hCc, map_sub, PowerSeries.coeff_C, ite_eq_right one_ne_zero, coeff_one_pow]
    have e0 : constantCoeff (seriesOf h) = h 0 := by simp [seriesOf]
    have e1 : coeff 1 (seriesOf h) = h 1 := by simp [seriesOf]
    rw [e0, e1]
    rcases p with _ | _ | p
    · omega
    · omega
    · simp
  obtain ⟨Cc', hCc'⟩ := (PowerSeries.X_dvd_iff (φ := Cc)).mpr hcz
  have hCc'0 : constantCoeff Cc' = coeff 1 Cc := by
    rw [hCc']; simp [PowerSeries.coeff_succ_X_mul]
  have prod := coeff_mul_low (f := Cc') (g := (a : K⟦X⟧) - (b : K⟦X⟧)) hab
  have term3 : ∀ n, coeff n (PowerSeries.C (p : K) * Cc * PowerSeries.X ^ (M - 1) *
        ((a : K⟦X⟧) - (b : K⟦X⟧))) =
      if M ≤ n then (p : K) * coeff (n - M) (Cc' * ((a : K⟦X⟧) - (b : K⟦X⟧))) else 0 := by
    intro n
    have : PowerSeries.C (p : K) * Cc * PowerSeries.X ^ (M - 1) * ((a : K⟦X⟧) - (b : K⟦X⟧)) =
        PowerSeries.C (p : K) * (PowerSeries.X ^ M * (Cc' * ((a : K⟦X⟧) - (b : K⟦X⟧)))) := by
      rw [hCc']
      have : M = (M - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
      ring
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    split_ifs <;> simp
  have hHp : ∀ n, n < M + A → coeff n (seriesOf h ^ (p - 1) *
      ((clippedOp M a b (seriesOf h) : K[X]) : K⟦X⟧)) = 0 := by
    intro n hn
    exact (coeff_mul_low (f := seriesOf h ^ (p - 1)) (g := ((clippedOp M a b (seriesOf h) : K[X]) :
      K⟦X⟧)) (N := M + A) (fun k hk => by rw [Polynomial.coeff_coe]; exact hl2 k hk)).1 n hn
  have hHpN := (coeff_mul_low (f := seriesOf h ^ (p - 1))
    (g := ((clippedOp M a b (seriesOf h) : K[X]) : K⟦X⟧)) (N := M + A)
    (fun k hk => by rw [Polynomial.coeff_coe]; exact hl2 k hk)).2
  have e0 : constantCoeff (seriesOf h) = h 0 := by simp [seriesOf]
  unfold defectExpr
  rw [← hCc]
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [map_add, map_sub, term3, mul_assoc (PowerSeries.C (p : K)), PowerSeries.coeff_C_mul, hHp n hn, Polynomial.coeff_coe,
      hl1 n hn]
    split_ifs with hMn
    · rw [prod.1 _ (by omega)]; simp
    · simp
  · rw [map_add, map_sub, term3, mul_assoc (PowerSeries.C (p : K)), PowerSeries.coeff_C_mul, hHpN, Polynomial.coeff_coe,
      Polynomial.coeff_coe, hc1, hc2, ite_eq_left (by omega),
      show M + A - M = A by omega, prod.2, hCc'0, hc1', habA, map_pow, e0]
    ring

theorem coeff_mul_shift (u : K⟦X⟧) (β : K) (c : K[X]) (B M : ℕ) (hB : B ≤ M) :
    coeff M (u * ((Polynomial.C β * (Polynomial.X ^ B * c) : K[X]) : K⟦X⟧)) =
      β * coeff (M - B) (u * (c : K⟦X⟧)) := by
  have : u * ((Polynomial.C β * (Polynomial.X ^ B * c) : K[X]) : K⟦X⟧) =
      PowerSeries.C β * (PowerSeries.X ^ B * (u * (c : K⟦X⟧))) := by
    rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
      Polynomial.coe_X]
    ring
  rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_left hB]

/-- If the defect expression vanishes at `M + A` and `b = β z^B c` with `β [H c]_L = -1` and
`L + 1 + B = M`, then `α_{c,p} = 0`, provided `a_A ≠ 0`. -/
theorem alphaOf_eq_zero_of_low (M A B L p : ℕ) (hp : 2 ≤ p) (hM : 1 ≤ M) (hAB : A < B)
    (hLB : L + 1 + B = M) (h : ℕ → K) (a c : K[X]) (β : K)
    (ha : ∀ i < A, a.coeff i = 0) (haA : a.coeff A ≠ 0) (hβ : β ≠ 0)
    (hk : β * coeff L (seriesOf h * (c : K⟦X⟧)) = -1)
    (hq : coeff (M + A) (defectExpr M p h a (Polynomial.C β * (Polynomial.X ^ B * c))) = 0) :
    alphaOf h c p L = 0 := by
  have hb : ∀ j < B, (Polynomial.C β * (Polynomial.X ^ B * c)).coeff j = 0 := by
    intro j hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
  obtain ⟨-, hc⟩ := coeff_defectExpr_low M A B p hp hM hAB h a _ ha hb
  rw [hc, coeff_mul_shift _ _ _ _ _ (by omega), coeff_mul_shift _ _ _ _ _ (by omega),
    show M - B = L + 1 by omega] at hq
  have hne : a.coeff A * β ≠ 0 := mul_ne_zero haA hβ
  have : (a.coeff A * β) * alphaOf h c p L = 0 := by
    unfold alphaOf
    rw [sub_mul, map_sub, mul_assoc (PowerSeries.C _), PowerSeries.coeff_C_mul]
    linear_combination (-1 : K) * hq - (a.coeff A * (p : K) * ((p - 1 : ℕ) : K) * h 0 ^ (p - 2) * h 1) * hk
  exact (mul_eq_zero.mp this).resolve_left hne

end SkewCoframeRigidity.Unshifted
