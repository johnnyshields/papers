/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalRationalFactorization

/-!
# Resolving-generator independence of the full rational defect

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Every original source and virtual jet is retained. Products and full inverses propagate
independence through the rational prefactor and both summands of the defect. Exact
residue matching is unnecessary at these earlier orders. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F : Type*} [Field F] [CharZero F] [Module ℚ F]

/-- The full rational prefactor omits a generator whenever the original source and
virtual factors omit it through that order. Its independence is produced, not assumed. -/
theorem coeff_deriv_rational_prefactor_zero {ι : Type*} (D : Derivation ℚ F F)
    (s : Finset ι) (f β : PowerSeries F) (α : ι → F) (e : ι → ℤ) (ε : F)
    (d n : ℕ) (hf0 : PowerSeries.constantCoeff f ≠ 0) (hDε : D ε = 0)
    (hT0 : ∀ i ∈ s, PowerSeries.constantCoeff (β - PowerSeries.C (α i) * f ^ 2) ≠ 0)
    (he : (∑ i ∈ s, e i) = (d : ℤ))
    (hf : ∀ k, k ≤ n → D (PowerSeries.coeff k f) = 0)
    (hT : ∀ i ∈ s, ∀ k, k ≤ n →
      D (PowerSeries.coeff k (β - PowerSeries.C (α i) * f ^ 2)) = 0) :
    D (PowerSeries.coeff n (PowerSeries.C ε *
      signedNormalProduct s (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) e)) = 0 := by
  let T := fun i => β - PowerSeries.C (α i) * f ^ 2
  have hg0 : PowerSeries.constantCoeff (f⁻¹ ^ 2) ≠ 0 := by
    rw [map_pow, PowerSeries.constantCoeff_inv]
    exact pow_ne_zero _ (inv_ne_zero hf0)
  have hscale := signedNormalProduct_mul_common s T e (f⁻¹ ^ 2) d hg0 he
  have hquot : (fun i => T i * f⁻¹ ^ 2) =
      (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) := by
    funext i
    exact virtualSeries_quotient β f (α i) hf0
  rw [hquot] at hscale
  rw [hscale, PowerSeries.coeff_C_mul, Derivation.leibniz, hDε, smul_zero, add_zero]
  suffices hz : D (PowerSeries.coeff n
      (signedNormalProduct s T e * (f⁻¹ ^ 2) ^ d)) = 0 by rw [hz, smul_zero]
  apply coeff_deriv_mul_zero D _ _ n
  · intro k hk
    exact coeff_deriv_signed_product_zero D s T e k hT0
      (fun i hi j hj => hT i hi j (hj.trans hk))
  · intro k hk
    apply coeff_deriv_pow_zero D _ k _ d
    intro l hl
    apply coeff_deriv_pow_zero D _ l _ 2
    intro a ha
    exact coeff_deriv_inv_zero D f a hf0 (fun b hb => hf b (hb.trans (ha.trans (hl.trans hk))))

/-- Both full rational-defect summands omit the generator at an earlier order, without
assuming their earlier intrinsic coefficients vanish or that their residues match. -/
theorem coeff_deriv_full_rational_defect_zero {ι : Type*} (D : Derivation ℚ F F)
    (s : Finset ι) (E f β : PowerSeries F) (α : ι → F) (e : ι → ℤ) (ε : F)
    (v d n : ℕ) (hf0 : PowerSeries.constantCoeff f ≠ 0) (hDε : D ε = 0)
    (hT0 : ∀ i ∈ s, PowerSeries.constantCoeff (β - PowerSeries.C (α i) * f ^ 2) ≠ 0)
    (he : (∑ i ∈ s, e i) = (d : ℤ))
    (hE : ∀ k, k ≤ n → D (PowerSeries.coeff k E) = 0)
    (hf : ∀ k, k ≤ n → D (PowerSeries.coeff k f) = 0)
    (hT : ∀ i ∈ s, ∀ k, k ≤ n →
      D (PowerSeries.coeff k (β - PowerSeries.C (α i) * f ^ 2)) = 0) :
    D (PowerSeries.coeff n (f ^ v * (E * f⁻¹ ^ 2) ^ (v + d) -
      PowerSeries.C ε * signedNormalProduct s
        (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) e)) = 0 := by
  rw [map_sub, map_sub, coeff_deriv_rational_prefactor_zero D s f β α e ε d n
    hf0 hDε hT0 he hf hT, sub_zero]
  apply coeff_deriv_mul_zero D _ _ n
  · intro k hk
    exact coeff_deriv_pow_zero D f k (fun j hj => hf j (hj.trans hk)) v
  · intro k hk
    apply coeff_deriv_pow_zero D _ k _ (v + d)
    intro j hj
    apply coeff_deriv_mul_zero D _ _ j
    · intro l hl
      exact hE l (hl.trans (hj.trans hk))
    · intro l hl
      apply coeff_deriv_pow_zero D _ l _ 2
      intro a ha
      exact coeff_deriv_inv_zero D f a hf0
        (fun b hb => hf b (hb.trans (ha.trans (hl.trans (hj.trans hk)))))

end SkewCornerDescent.Matrix
