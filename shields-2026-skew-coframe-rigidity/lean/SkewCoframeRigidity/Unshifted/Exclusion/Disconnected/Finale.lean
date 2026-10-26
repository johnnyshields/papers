/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Branch

/-!
# The linear equation when the two endpoint columns agree

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner, final step).  With `a = b` and `Δ = G₀ - C₀`,
the linear equation is the quadratic one for the pair `(Δ, a)` plus a term of order above `M + d`,
where `d` is the order of `Δ`.  Its lowest coefficient is the coordinate `α_{E,p}`; and at `p = 2`
for the two-cell row it says that the order of `Δ` is at least `M - 4`.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries SkewCoframeRigidity SkewCoframeRigidity.Coframe
open Polynomial hiding coeff

variable {K : Type*} [Field K]

/-- The linear equation of the `y`-expansion, in the notation of the paper:
`𝓔^M_{W₁} + p (ϑ^{p-1} - h^{p-1}) z^{M-1} (G₀ - C₀)`, with `W₁ = a ∧ C₀ + G₀ ∧ b`. -/
noncomputable def linExpr (M p : ℕ) (h : ℕ → K) (G₀ C₀ a b : K[X]) : K⟦X⟧ :=
  ((clippedOp M a C₀ (seriesOf h ^ p) + clippedOp M G₀ b (seriesOf h ^ p) : K[X]) : K⟦X⟧) -
    PowerSeries.C (p : K) * seriesOf h ^ (p - 1) *
      ((clippedOp M a C₀ (seriesOf h) + clippedOp M G₀ b (seriesOf h) : K[X]) : K⟦X⟧) +
    PowerSeries.C (p : K) * (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1)) *
      PowerSeries.X ^ (M - 1) * ((G₀ : K⟦X⟧) - (C₀ : K⟦X⟧))

/-- With equal endpoint columns the linear equation is that of the pair `(G₀ - C₀, a)` plus the
single term `p (ϑ^{p-1} - h^{p-1}) z^{M-1} a`. -/
theorem linExpr_same (M p : ℕ) (h : ℕ → K) (G₀ C₀ a : K[X]) :
    linExpr M p h G₀ C₀ a a = defectExpr M p h (G₀ - C₀) a +
      PowerSeries.C (p : K) * (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1)) *
        PowerSeries.X ^ (M - 1) * (a : K⟦X⟧) := by
  have hb : ∀ u : K⟦X⟧, clippedOp M a C₀ u + clippedOp M G₀ a u = clippedOp M (G₀ - C₀) a u := by
    intro u
    unfold clippedOp
    rw [Polynomial.coe_sub]
    simp only [Polynomial.coe_sub, mul_sub, sub_mul, map_sub]
    ring
  unfold linExpr defectExpr
  rw [hb, hb]
  simp only [Polynomial.coe_sub]
  ring

/-- The lowest coefficient of the linear equation, for equal endpoint columns
`a = β z^A g` and `Δ` of order `d < A`: the coordinate of the component vanishes. -/
theorem alphaOf_eq_zero_of_lin (M d A L p : ℕ) (hp : 2 ≤ p) (hM : 1 ≤ M) (hdA : d < A)
    (hLA : L + 1 + A = M) (h : ℕ → K) (Δ g : K[X]) (β : K)
    (hΔ : ∀ i < d, Δ.coeff i = 0) (hΔd : Δ.coeff d ≠ 0) (hβ : β ≠ 0)
    (hk : β * coeff L (seriesOf h * (g : K⟦X⟧)) = -1)
    (heq : ∀ n < 2 * M, coeff n (defectExpr M p h Δ (Polynomial.C β * (Polynomial.X ^ A * g)) +
      PowerSeries.C (p : K) * (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1)) *
        PowerSeries.X ^ (M - 1) *
        ((Polynomial.C β * (Polynomial.X ^ A * g) : K[X]) : K⟦X⟧)) = 0) :
    alphaOf h g p L = 0 := by
  refine alphaOf_eq_zero_of_low M d A L p hp hM hdA hLA h Δ g β hΔ hΔd hβ hk ?_
  have h1 := heq (M + d) (by omega)
  have hextra : coeff (M + d) (PowerSeries.C (p : K) *
      (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1)) * PowerSeries.X ^ (M - 1) *
        ((Polynomial.C β * (Polynomial.X ^ A * g) : K[X]) : K⟦X⟧)) = 0 := by
    have hcz : PowerSeries.constantCoeff (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1) :
        K⟦X⟧) = 0 := by simp [seriesOf]
    obtain ⟨Cc', hCc'⟩ := (PowerSeries.X_dvd_iff (φ := PowerSeries.C (h 0 ^ (p - 1)) -
      seriesOf h ^ (p - 1))).mpr hcz
    have : PowerSeries.C (p : K) * (PowerSeries.C (h 0 ^ (p - 1)) - seriesOf h ^ (p - 1)) *
        PowerSeries.X ^ (M - 1) * ((Polynomial.C β * (Polynomial.X ^ A * g) : K[X]) : K⟦X⟧) =
        PowerSeries.X ^ (M + A) * (PowerSeries.C (p : K) * Cc' * (PowerSeries.C β * (g : K⟦X⟧))) := by
      rw [hCc', Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X,
        Polynomial.coe_C]
      have : M + A = (M - 1) + 1 + A := by omega
      rw [this, pow_add, pow_add, pow_one]
      ring
    rw [this, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  rw [map_add, hextra, add_zero] at h1
  exact h1

/-- Against the two-cell row at `p = 2`, with `a = b = β z^s`, the linear equation forces the
order `d` of `Δ` to be at least `s - 1 = M - 4`. -/
theorem rowTwo_lin_order (s d : ℕ) (h : ℕ → K) (Δ : K[X]) (β : K) (hβ : β * h 2 = -1)
    (hΔ : ∀ i < d, Δ.coeff i = 0) (hΔd : Δ.coeff d ≠ 0)
    (heq : ∀ n < 2 * (s + 3), coeff n (defectExpr (s + 3) 2 h Δ
      (Polynomial.C β * Polynomial.X ^ s) +
      PowerSeries.C ((2 : ℕ) : K) * (PowerSeries.C (h 0 ^ (2 - 1)) - seriesOf h ^ (2 - 1)) *
        PowerSeries.X ^ (s + 3 - 1) *
        ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧)) = 0) : s ≤ d + 1 := by
  have hh2 : h 2 ≠ 0 := fun e => by rw [e, mul_zero] at hβ; exact absurd hβ (by norm_num)
  have hβ0 : β ≠ 0 := fun e => by rw [e, zero_mul] at hβ; exact absurd hβ (by norm_num)
  have hβ' : PowerSeries.C β * PowerSeries.C (h 2) = -1 := by
    rw [← map_mul, hβ]; simp
  set Bl : K⟦X⟧ := (seriesOf h - PowerSeries.C (h 0) - PowerSeries.C (h 1) * PowerSeries.X) ^ 2 *
      (Δ : K⟦X⟧) + tailS (s + 3) (seriesOf h ^ 2 * (Δ : K⟦X⟧)) -
      2 * seriesOf h * tailS (s + 3) (seriesOf h * (Δ : K⟦X⟧)) with hBl
  have hfac : defectExpr (s + 3) 2 h Δ (Polynomial.C β * Polynomial.X ^ s) +
      PowerSeries.C ((2 : ℕ) : K) * (PowerSeries.C (h 0 ^ (2 - 1)) - seriesOf h ^ (2 - 1)) *
        PowerSeries.X ^ (s + 3 - 1) *
        ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) =
      ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) * Bl := by
    rw [defectExpr_two_row s h Δ β hβ, hBl]
    simp only [Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one, map_mul, map_ofNat,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
    have e : (PowerSeries.X : K⟦X⟧) ^ (s + 3 - 1) = PowerSeries.X ^ s * PowerSeries.X ^ 2 := by
      rw [← pow_add]; rfl
    rw [e]
    linear_combination (2 * (PowerSeries.C (h 0) - seriesOf h) * PowerSeries.X ^ s *
      PowerSeries.X ^ 2 * (PowerSeries.C β * PowerSeries.X ^ s)) * hβ'
  have hBl0 : ∀ n < s + 3, coeff n Bl = 0 → True := fun _ _ _ => trivial
  have hz : ∀ n < s + 3, coeff n Bl = 0 := by
    intro n hn
    have := heq (s + n) (by omega)
    rw [hfac, coeff_C_X_pow_mul_mul] at this
    have hn' := (mul_eq_zero.mp this).resolve_left hβ0
    exact hn'
  set R' : K⟦X⟧ := mk (fun i => h (i + 2)) with hR'
  have hR2 : (seriesOf h - PowerSeries.C (h 0) - PowerSeries.C (h 1) * PowerSeries.X) ^ 2 *
      (Δ : K⟦X⟧) = PowerSeries.X ^ 4 * (R' ^ 2 * (Δ : K⟦X⟧)) := by
    rw [sub_sub_eq_X_sq_mul]; ring
  have hR'a := coeff_mul_low (f := R' ^ 2) (g := (Δ : K⟦X⟧)) (N := d)
    (fun k hk => by rw [Polynomial.coeff_coe]; exact hΔ k hk)
  have hR'c : PowerSeries.constantCoeff (R' ^ 2) = h 2 ^ 2 := by simp [hR']
  by_contra hcon
  have h1 := hz (d + 4) (by omega)
  have t1 : coeff (d + 4) (tailS (s + 3) (seriesOf h ^ 2 * (Δ : K⟦X⟧))) = 0 := by
    rw [coeff_tailS, ite_eq_right (by omega)]
  have t2 : coeff (d + 4) (2 * seriesOf h * tailS (s + 3) (seriesOf h * (Δ : K⟦X⟧))) = 0 :=
    (coeff_mul_low (f := 2 * seriesOf h) (g := tailS (s + 3) (seriesOf h * (Δ : K⟦X⟧)))
      (N := s + 3) (fun k hk => by rw [coeff_tailS, ite_eq_right (by omega)])).1 _ (by omega)
  rw [hBl, map_sub, map_add, t1, t2, hR2, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
    show d + 4 - 4 = d by omega, hR'a.2, hR'c, Polynomial.coeff_coe] at h1
  exact mul_ne_zero (pow_ne_zero 2 hh2) hΔd (by simpa using h1)

end SkewCoframeRigidity.Unshifted
