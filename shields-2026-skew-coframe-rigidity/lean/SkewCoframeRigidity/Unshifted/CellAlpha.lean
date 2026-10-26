/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Endpoints

/-!
# The exponent coordinate of a cell component

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`).  A single cell has span one and own coframe `1`; its coordinate
`α_{E,p}` equals `-\binom p2 ϑ^{p-2} H_1²`, which is nonzero for every `p ≥ 2`.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCoframeRigidity.Coframe Polynomial PowerSeries

variable {K : Type*} [Field K]

/-- The coefficient of `X²` in a power of a series, multiplied by two. -/
theorem two_mul_coeff_two_pow (A : K⟦X⟧) (m : ℕ) :
    2 * coeff 2 (A ^ m) = 2 * m * constantCoeff A ^ (m - 1) * coeff 2 A +
      m * ((m - 1 : ℕ) : K) * constantCoeff A ^ (m - 2) * coeff 1 A ^ 2 := by
  have h2 : ∀ B C : K⟦X⟧, coeff 2 (B * C) =
      constantCoeff B * coeff 2 C + coeff 1 B * coeff 1 C + coeff 2 B * constantCoeff C := by
    intro B C
    simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, add_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := coeff_one_pow A m
    have hm : 2 * (constantCoeff (A ^ m) * coeff 2 A + coeff 1 (A ^ m) * coeff 1 A +
        coeff 2 (A ^ m) * constantCoeff A) = 2 * (constantCoeff (A ^ m) * coeff 2 A) +
        2 * (coeff 1 (A ^ m) * coeff 1 A) + constantCoeff A * (2 * coeff 2 (A ^ m)) := by ring
    rw [pow_succ, h2, hm, ih, h1, map_pow]
    rcases m with _ | _ | m
    · simp
    · simp; ring
    · simp only [map_pow, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      have e1 : m + 1 + 1 + 1 - 2 = m + 1 := by omega
      have e2 : m + 1 + 1 - 2 = m := by omega
      rw [e1, e2]
      ring

/-- A cell component (own coframe `1`, span one): `α_{E,p} = -\binom p2 ϑ^{p-2} H_1²`, written
as `2 α = -p(p-1) ϑ^{p-2} H_1²`. -/
theorem two_mul_alphaOf_cell (h : ℕ → K) (p : ℕ) :
    2 * alphaOf h 1 p 1 = -((p : K) * ((p - 1 : ℕ) : K) * h 0 ^ (p - 2) * h 1 ^ 2) := by
  unfold alphaOf
  rw [Polynomial.coe_one, mul_one, mul_sub, map_sub]
  have hs : ∀ k, coeff k (seriesOf h) = h k := fun k => by simp [seriesOf]
  have hc : constantCoeff (seriesOf h) = h 0 := by simp [seriesOf]
  have hmul : coeff 2 (PowerSeries.C ((p : K) * h 0 ^ (p - 1)) * seriesOf h) =
      (p : K) * h 0 ^ (p - 1) * h 2 := by
    rw [PowerSeries.coeff_C_mul, hs]
  rw [hmul, mul_sub, two_mul_coeff_two_pow, hc, hs, hs, mul_one, hs]
  rcases p with _ | _ | p
  · simp
  · simp
  · have e : p + 1 + 1 - 1 = p + 1 := by omega
    have e2 : p + 1 + 1 - 2 = p := by omega
    rw [e, e2]
    push_cast
    ring

theorem alphaOf_cell_ne_zero (h : ℕ → K) [CharZero K] (p : ℕ) (hp : 2 ≤ p) (h0 : h 0 ≠ 0)
    (h1 : h 1 ≠ 0) : alphaOf h 1 p 1 ≠ 0 := by
  intro hz
  have := two_mul_alphaOf_cell h p
  rw [hz, mul_zero] at this
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : ((p - 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (by omega : p - 1 ≠ 0)
  have : (p : K) * ((p - 1 : ℕ) : K) * h 0 ^ (p - 2) * h 1 ^ 2 = 0 := by linear_combination this
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hp0 hp1) (pow_ne_zero _ h0)) (pow_ne_zero _ h1)) this

end SkewCoframeRigidity.Unshifted
