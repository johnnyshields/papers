/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalComparisonCoefficient

/-!
# Full signed rational factorization in the normal series ring

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
All inverses are full series inverses, with their actual unit conditions. Positive
and negative multiplicities are retained separately before signed balance is used.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F : Type*} [Field F]

/-- A common normal unit scales a signed product by its total multiplicity. -/
theorem signedNormalProduct_mul_common {ι : Type*} (s : Finset ι)
    (p : ι → PowerSeries F) (e : ι → ℤ) (g : PowerSeries F) (d : ℕ)
    (hg : PowerSeries.constantCoeff g ≠ 0) (he : (∑ i ∈ s, e i) = (d : ℤ)) :
    signedNormalProduct s (fun i => p i * g) e = signedNormalProduct s p e * g ^ d := by
  classical
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ s) =>
    show e i = ((e i).toNat : ℤ) - ((-e i).toNat : ℤ) by omega)
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, he] at hs
  have hn : (∑ i ∈ s, (e i).toNat) = (∑ i ∈ s, (-e i).toNat) + d := by omega
  have hc : g ^ (∑ i ∈ s, (-e i).toNat) *
      (g ^ (∑ i ∈ s, (-e i).toNat))⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    rw [map_pow]
    exact pow_ne_zero _ hg
  unfold signedNormalProduct
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    PowerSeries.mul_inv_rev, hn, pow_add]
  calc
    _ = (∏ i ∈ s, p i ^ (e i).toNat) *
        (∏ i ∈ s, p i ^ (-e i).toNat)⁻¹ * g ^ d *
        (g ^ (∑ i ∈ s, (-e i).toNat) *
          (g ^ (∑ i ∈ s, (-e i).toNat))⁻¹) := by ring
    _ = _ := by rw [hc, mul_one]

/-- The virtual factor divided by the full source square is the corresponding
rational factor. The orientation scalar is not changed. -/
theorem virtualSeries_quotient (β f : PowerSeries F) (α : F)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (β - PowerSeries.C α * f ^ 2) * f⁻¹ ^ 2 = β * f⁻¹ ^ 2 - PowerSeries.C α := by
  have hc : f ^ 2 * f⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, PowerSeries.mul_inv_cancel f hf, one_pow]
  rw [sub_mul, mul_assoc, hc, mul_one]

/-- Exact full-series defect factorization, including arbitrary signed multiplicities
and the nonzero orientation scalar. No exponential is used in the series ring. -/
theorem normalRationalDefect_factorization {ι : Type*} (s : Finset ι)
    (E f β : PowerSeries F) (α : ι → F) (e : ι → ℤ) (ε : F)
    (v d : ℕ) (hf : PowerSeries.constantCoeff f ≠ 0) (hε : ε ≠ 0)
    (hT : ∀ i ∈ s,
      PowerSeries.constantCoeff (β - PowerSeries.C (α i) * f ^ 2) ≠ 0)
    (he : (∑ i ∈ s, e i) = (d : ℤ)) :
    let T := fun i => β - PowerSeries.C (α i) * f ^ 2
    let ρ := PowerSeries.C ε *
      signedNormalProduct s (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) e
    let R := E ^ (v + d) * (PowerSeries.C ε * f ^ v * signedNormalProduct s T e)⁻¹
    f ^ v * (E * f⁻¹ ^ 2) ^ (v + d) - ρ = ρ * (R - 1) := by
  classical
  let T := fun i => β - PowerSeries.C (α i) * f ^ 2
  let S := signedNormalProduct s T e
  have hg : PowerSeries.constantCoeff (f⁻¹ ^ 2) ≠ 0 := by
    rw [map_pow, PowerSeries.constantCoeff_inv]
    exact pow_ne_zero _ (inv_ne_zero hf)
  have hscale := signedNormalProduct_mul_common s T e (f⁻¹ ^ 2) d hg he
  have hquot : (fun i => T i * f⁻¹ ^ 2) =
      (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) := by
    funext i
    exact virtualSeries_quotient β f (α i) hf
  rw [hquot] at hscale
  have hSc : PowerSeries.constantCoeff S ≠ 0 :=
    signedNormalProduct_constant_ne_zero s T e hT
  have hSi : S * S⁻¹ = 1 := PowerSeries.mul_inv_cancel S hSc
  have hεi : PowerSeries.C ε * (PowerSeries.C ε)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa only [PowerSeries.constantCoeff_C] using hε)
  have hfi : f ^ v * f⁻¹ ^ v = 1 := by
    rw [← mul_pow, PowerSeries.mul_inv_cancel f hf, one_pow]
  have hsq : (f⁻¹ ^ 2) ^ v = f⁻¹ ^ v * f⁻¹ ^ v := by
    rw [← pow_mul, Nat.mul_comm 2 v, pow_mul, pow_two]
  have hp : f ^ v * (f⁻¹ ^ 2) ^ (v + d) = f⁻¹ ^ v * (f⁻¹ ^ 2) ^ d := by
    rw [pow_add, hsq]
    calc
      _ = (f ^ v * f⁻¹ ^ v) * (f⁻¹ ^ v * (f⁻¹ ^ 2) ^ d) := by ring
      _ = _ := by rw [hfi, one_mul]
  dsimp only
  rw [hscale]
  change f ^ v * (E * f⁻¹ ^ 2) ^ (v + d) - PowerSeries.C ε * (S * (f⁻¹ ^ 2) ^ d) =
    (PowerSeries.C ε * (S * (f⁻¹ ^ 2) ^ d)) *
      (E ^ (v + d) * (PowerSeries.C ε * f ^ v * S)⁻¹ - 1)
  rw [mul_pow, PowerSeries.mul_inv_rev, PowerSeries.mul_inv_rev,
    ← PowerSeries.inv_pow]
  have hcancel :
      (PowerSeries.C ε * (S * (f⁻¹ ^ 2) ^ d)) *
        (E ^ (v + d) * (S⁻¹ * (f⁻¹ ^ v * (PowerSeries.C ε)⁻¹))) =
      E ^ (v + d) * (f⁻¹ ^ v * (f⁻¹ ^ 2) ^ d) := by
    calc
      _ = (S * S⁻¹) * (PowerSeries.C ε * (PowerSeries.C ε)⁻¹) *
          (E ^ (v + d) * (f⁻¹ ^ v * (f⁻¹ ^ 2) ^ d)) := by ring
      _ = _ := by rw [hSi, hεi, one_mul, one_mul]
  rw [mul_sub, hcancel, mul_one, ← hp]
  ring

end SkewCornerDescent.Matrix
