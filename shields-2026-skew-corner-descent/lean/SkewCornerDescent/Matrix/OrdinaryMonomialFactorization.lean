/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.NormalRationalFactorization
import SkewCornerDescent.Matrix.FormalNormalDetection

/-!
# Full ordinary monomial defect and finite detection

Supports `shields-2026-skew-corner-descent.tex` (`eq:original-defect`,
`prop:normal-interface`). Exact unit factorization retains every coefficient
of the original normal germs and their inverse series. Geometric residue
matching normalizes the quotient, and finite logarithmic detection transfers
to the complete defect through its genuine nonzero prefactor. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
variable {F : Type*} [Field F]

/-- Exact ordinary defect factorization with the full source inverse. -/
theorem ordinaryMonomialDefect_factorization (E f O : PowerSeries F) (κ : F)
    (a b : ℕ) (hab : a ≤ b) (hf : PowerSeries.constantCoeff f ≠ 0)
    (hO : PowerSeries.constantCoeff O ≠ 0) (hκ : κ ≠ 0) :
    f^a * (E*f⁻¹^2)^b - PowerSeries.C κ * (O*f⁻¹^2)^(b-a) =
      (PowerSeries.C κ * (O*f⁻¹^2)^(b-a)) *
        (PowerSeries.C κ⁻¹ * (E^b * (f^a*O^(b-a))⁻¹) - 1) := by
  have he : (∑ i ∈ ({()} : Finset Unit), (fun _ : Unit => ((b-a : ℕ) : ℤ)) i) =
      ((b-a : ℕ) : ℤ) := by simp
  have h := normalRationalDefect_factorization ({()} : Finset Unit) E f O
    (fun _ => 0) (fun _ => ((b-a : ℕ) : ℤ)) κ a (b-a) hf hκ
    (by intro i hi; simpa only [map_zero, zero_mul, sub_zero] using hO) he
  dsimp only at h
  simp only [signedNormalProduct, Finset.prod_singleton, Int.toNat_natCast,
    Int.toNat_neg_natCast, pow_zero, inv_one, mul_one, map_zero, zero_mul,
    sub_zero, Nat.add_sub_of_le hab] at h
  rw [h]
  simp only [PowerSeries.mul_inv_rev, PowerSeries.C_inv]
  ring

/-- Geometric residue matching normalizes the complete ordinary quotient. -/
theorem ordinaryMonomialRatio_constant (E f O : PowerSeries F) (κ : F)
    (a b : ℕ) (hf : PowerSeries.constantCoeff f ≠ 0)
    (hO : PowerSeries.constantCoeff O ≠ 0) (hκ : κ ≠ 0)
    (hmatch : (PowerSeries.constantCoeff E) ^ b =
      κ * (PowerSeries.constantCoeff f) ^ a * (PowerSeries.constantCoeff O) ^ (b - a)) :
    PowerSeries.constantCoeff (PowerSeries.C κ⁻¹ * (E^b * (f^a*O^(b-a))⁻¹)) = 1 := by
  simp only [map_mul, map_pow, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv]
  rw [hmatch]
  field_simp

/-- Finite logarithmic detection transfers through the full actual monomial
prefactor, without discarding any higher normal inverse coefficients. -/
theorem ordinaryMonomialDefect_detection [Algebra ℚ F]
    (E f O : PowerSeries F) (κ : F) (a b n : ℕ) (hab : a ≤ b)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hO : PowerSeries.constantCoeff O ≠ 0)
    (hκ : κ ≠ 0)
    (hmatch : (PowerSeries.constantCoeff E) ^ b =
      κ * (PowerSeries.constantCoeff f) ^ a * (PowerSeries.constantCoeff O) ^ (b - a))
    (hlog : PowerSeries.coeff n (PowerSeries.logOf
      (PowerSeries.C κ⁻¹ * (E ^ b * (f ^ a * O ^ (b - a))⁻¹))) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ j ≤ n ∧ PowerSeries.coeff j
      (f^a * (E*f⁻¹^2)^b - PowerSeries.C κ * (O*f⁻¹^2)^(b-a)) ≠ 0 := by
  have hR := ordinaryMonomialRatio_constant E f O κ a b hf hO hκ hmatch
  have hU : PowerSeries.constantCoeff
      (PowerSeries.C κ * (O*f⁻¹^2)^(b-a)) ≠ 0 := by
    simp only [map_mul, map_pow, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv]
    exact mul_ne_zero hκ (pow_ne_zero _ (mul_ne_zero hO (pow_ne_zero _ (inv_ne_zero hf))))
  obtain ⟨j, hj, hjn, hjD⟩ := log_coeff_ne_zero_imp_prefactor_detection _ _ hR hU n hlog
  refine ⟨j, hj, hjn, ?_⟩
  rw [ordinaryMonomialDefect_factorization E f O κ a b hab hf hO hκ]
  exact hjD

end SkewCornerDescent.Matrix
