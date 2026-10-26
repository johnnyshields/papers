/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Ring.GeomSum

/-!
# First-order perturbation of a power of a series

Formalizes the coefficient expansion used in `shields-2026-skew-coframe-rigidity.tex`,
`sc:component-remainder`: perturbing a series by a multiple of `z^L` changes the coefficient of
`z^L` in its `p`-th power, multiplied by any fixed series, by `p A₀^{p-1} E₀ Q₀`.  Sorry-free.
-/

namespace SkewCoframeRigidity

open PowerSeries

variable {R : Type*} [CommRing R]

/-- `[(A + z^L E)^p Q]_L = [A^p Q]_L + p A₀^{p-1} E₀ Q₀` for `L ≥ 1`. -/
theorem coeff_add_X_pow_mul_pow (L : ℕ) (hL : 1 ≤ L) (A E Q : R⟦X⟧) (p : ℕ) :
    coeff L ((A + X ^ L * E) ^ p * Q) =
      coeff L (A ^ p * Q) +
        p * (constantCoeff A) ^ (p - 1) * constantCoeff E * constantCoeff Q := by
  set u : R⟦X⟧ := X ^ L * E with hu
  have hgeom := Commute.geom_sum₂_mul (Commute.all (A + u) A) p
  rw [add_sub_cancel_left] at hgeom
  set S : R⟦X⟧ := ∑ i ∈ Finset.range p, (A + u) ^ i * A ^ (p - 1 - i) with hS
  have h1 : (A + u) ^ p = A ^ p + S * u := by
    rw [hgeom]; ring
  have hu0 : constantCoeff u = 0 := by
    rw [hu, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul]
  have hS0 : constantCoeff S = p * (constantCoeff A) ^ (p - 1) := by
    rw [hS, map_sum]
    have : ∀ i ∈ Finset.range p, constantCoeff ((A + u) ^ i * A ^ (p - 1 - i)) =
        constantCoeff A ^ (p - 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [map_mul, map_pow, map_pow, map_add, hu0, add_zero, ← pow_add]
      congr 1; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [h1, add_mul, map_add, hu]
  congr 1
  have : S * (X ^ L * E) * Q = X ^ L * (S * E * Q) := by ring
  rw [this, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff,
    map_mul, map_mul, hS0]

end SkewCoframeRigidity
