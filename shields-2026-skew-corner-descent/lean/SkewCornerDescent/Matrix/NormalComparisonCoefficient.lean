/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.SignedNormalProducts
import SkewCornerDescent.Matrix.NormalDefectCoefficient

/-!
# Complete normal comparison before geometric coefficient substitution

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The comparison retains the full amalgamation, source, virtual factors and signed
multiplicities. Every earlier coefficient is carried through products and inverses;
none is discarded merely because its resolving-generator derivative vanishes.
The actual diagram assemblies supply each factor's earlier independence. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F : Type*} [Field F] [CharZero F] [Module ℚ F]

/-- The complete original normal ratio, with every signed virtual factor retained. -/
noncomputable def normalComparisonSeries {ι : Type*} (s : Finset ι)
    (E f : PowerSeries F) (T : ι → PowerSeries F) (e : ι → ℤ) (b v : ℕ) : PowerSeries F :=
  E ^ b * (f ^ v * signedNormalProduct s T e)⁻¹

omit [CharZero F] [Module ℚ F] in
/-- Exact original residue matching supplies the residue-one comparison internally. -/
theorem normalComparisonSeries_constant_one {ι : Type*} (s : Finset ι)
    (E f : PowerSeries F) (T : ι → PowerSeries F) (e : ι → ℤ) (b v : ℕ)
    (hf0 : PowerSeries.constantCoeff f ≠ 0)
    (hT0 : ∀ i ∈ s, PowerSeries.constantCoeff (T i) ≠ 0)
    (hmatch : PowerSeries.constantCoeff E ^ b =
      PowerSeries.constantCoeff f ^ v * ∏ i ∈ s, PowerSeries.constantCoeff (T i) ^ e i) :
    PowerSeries.constantCoeff (normalComparisonSeries s E f T e b v) = 1 := by
  classical
  have hprod : (∏ i ∈ s, PowerSeries.constantCoeff (T i) ^ e i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => zpow_ne_zero _ (hT0 i hi))
  simp only [normalComparisonSeries, map_mul, map_pow, PowerSeries.constantCoeff_inv,
    signedNormalProduct_constant]
  rw [hmatch, mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ hf0) hprod)]

/-- Earlier resolving-generator independence propagates through the entire comparison. -/
theorem coeff_deriv_normal_comparison_zero {ι : Type*} (D : Derivation ℚ F F)
    (s : Finset ι) (E f : PowerSeries F) (T : ι → PowerSeries F) (e : ι → ℤ)
    (b v n : ℕ) (hf0 : PowerSeries.constantCoeff f ≠ 0)
    (hT0 : ∀ i ∈ s, PowerSeries.constantCoeff (T i) ≠ 0)
    (hE : ∀ k, k ≤ n → D (PowerSeries.coeff k E) = 0)
    (hf : ∀ k, k ≤ n → D (PowerSeries.coeff k f) = 0)
    (hT : ∀ i ∈ s, ∀ k, k ≤ n → D (PowerSeries.coeff k (T i)) = 0) :
    D (PowerSeries.coeff n (normalComparisonSeries s E f T e b v)) = 0 := by
  have hden0 : PowerSeries.constantCoeff (f ^ v * signedNormalProduct s T e) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hf0) (signedNormalProduct_constant_ne_zero s T e hT0)
  apply coeff_deriv_mul_zero D _ _ n
  · intro k hk
    exact coeff_deriv_pow_zero D E k (fun l hl => hE l (hl.trans hk)) b
  · intro k hk
    apply coeff_deriv_inv_zero D _ k hden0
    intro l hl
    apply coeff_deriv_mul_zero D _ _ l
    · intro a ha
      exact coeff_deriv_pow_zero D f a (fun z hz => hf z (hz.trans (ha.trans (hl.trans hk)))) v
    · intro a ha
      exact coeff_deriv_signed_product_zero D s T e a hT0
        (fun i hi z hz => hT i hi z (hz.trans (ha.trans (hl.trans hk))))

/-- The full comparison's first fresh logarithmic coefficient has the exact signed inventory.
The hypotheses concern original series coefficients; no detector formula is assumed. -/
theorem coeff_deriv_normal_comparison_log_first {ι : Type*} (D : Derivation ℚ F F)
    (s : Finset ι) (E f : PowerSeries F) (T : ι → PowerSeries F) (e : ι → ℤ)
    (b v n : ℕ) (hn : 0 < n)
    (hE0 : PowerSeries.constantCoeff E ≠ 0) (hf0 : PowerSeries.constantCoeff f ≠ 0)
    (hT0 : ∀ i ∈ s, PowerSeries.constantCoeff (T i) ≠ 0)
    (hE : ∀ k, k < n → D (PowerSeries.coeff k E) = 0)
    (hf : ∀ k, k < n → D (PowerSeries.coeff k f) = 0)
    (hT : ∀ i ∈ s, ∀ k, k < n → D (PowerSeries.coeff k (T i)) = 0) :
    let R := normalComparisonSeries s E f T e b v
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff R)⁻¹ * R))) =
      (b : F) * D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff E)⁻¹ * E))) -
      (v : F) * D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f))) -
      ∑ i ∈ s, (e i : F) * D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (T i))⁻¹ * T i))) := by
  have hpow (p : PowerSeries F) (a : ℕ)
      (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0) :
      ∀ k, k < n → D (PowerSeries.coeff k (p ^ a)) = 0 :=
    fun k hk => coeff_deriv_pow_zero D p k (fun l hl => hp l (hl.trans_lt hk)) a
  have hsig : ∀ k, k < n → D (PowerSeries.coeff k (signedNormalProduct s T e)) = 0 :=
    fun k hk => coeff_deriv_signed_product_zero D s T e k hT0
      (fun i hi l hl => hT i hi l (hl.trans_lt hk))
  have hs0 := signedNormalProduct_constant_ne_zero s T e hT0
  have hfPow0 : PowerSeries.constantCoeff (f ^ v) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hf0
  have hEPow0 : PowerSeries.constantCoeff (E ^ b) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ hE0
  have hden0 : PowerSeries.constantCoeff (f ^ v * signedNormalProduct s T e) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hfPow0 hs0
  have hden : ∀ k, k < n →
      D (PowerSeries.coeff k (f ^ v * signedNormalProduct s T e)) = 0 :=
    fun k hk => coeff_deriv_mul_zero D _ _ k
      (fun l hl => hpow f v hf l (hl.trans_lt hk))
      (fun l hl => hsig l (hl.trans_lt hk))
  have hi0 : PowerSeries.constantCoeff (f ^ v * signedNormalProduct s T e)⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero hden0
  have hi : ∀ k, k < n →
      D (PowerSeries.coeff k (f ^ v * signedNormalProduct s T e)⁻¹) = 0 :=
    fun k hk => coeff_deriv_inv_zero D _ k hden0 (fun l hl => hden l (hl.trans_lt hk))
  dsimp only [normalComparisonSeries]
  rw [coeff_deriv_normalized_mul_log_first D _ _ n hn hEPow0 hi0 (hpow E b hE) hi,
    coeff_deriv_normalized_inv_log_first D _ n hn hden0 hden,
    coeff_deriv_normalized_mul_log_first D _ _ n hn hfPow0 hs0 (hpow f v hf) hsig,
    coeff_deriv_normalized_pow_log_first D E n hn hE0 hE b,
    coeff_deriv_normalized_pow_log_first D f n hn hf0 hf v,
    coeff_deriv_normalized_signed_product_log_first D s T e n hn hT0 hT]
  ring

/-- The complete original defect retains its nonzero residue prefactor at the first
resolving-generator order. Residue-one normalization is derived from exact matching. -/
theorem coeff_deriv_complete_comparison_defect {ι : Type*} (D : Derivation ℚ F F)
    (s : Finset ι) (E f rho : PowerSeries F) (T : ι → PowerSeries F) (e : ι → ℤ)
    (b v n : ℕ) (hn : 0 < n)
    (hE0 : PowerSeries.constantCoeff E ≠ 0) (hf0 : PowerSeries.constantCoeff f ≠ 0)
    (hT0 : ∀ i ∈ s, PowerSeries.constantCoeff (T i) ≠ 0)
    (hmatch : PowerSeries.constantCoeff E ^ b =
      PowerSeries.constantCoeff f ^ v * ∏ i ∈ s, PowerSeries.constantCoeff (T i) ^ e i)
    (hE : ∀ k, k < n → D (PowerSeries.coeff k E) = 0)
    (hf : ∀ k, k < n → D (PowerSeries.coeff k f) = 0)
    (hT : ∀ i ∈ s, ∀ k, k < n → D (PowerSeries.coeff k (T i)) = 0)
    (hrho : ∀ k, k < n → D (PowerSeries.coeff k rho) = 0) :
    D (PowerSeries.coeff n (rho * (normalComparisonSeries s E f T e b v - 1))) =
      PowerSeries.constantCoeff rho *
        ((b : F) * D (PowerSeries.coeff n
            (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff E)⁻¹ * E))) -
          (v : F) * D (PowerSeries.coeff n
            (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f))) -
          ∑ i ∈ s, (e i : F) * D (PowerSeries.coeff n
            (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (T i))⁻¹ * T i)))) := by
  have hR0 := normalComparisonSeries_constant_one s E f T e b v hf0 hT0 hmatch
  have hprev : ∀ k, k < n →
      D (PowerSeries.coeff k (normalComparisonSeries s E f T e b v)) = 0 :=
    fun k hk => coeff_deriv_normal_comparison_zero D s E f T e b v k hf0 hT0
      (fun l hl => hE l (hl.trans_lt hk)) (fun l hl => hf l (hl.trans_lt hk))
      (fun i hi l hl => hT i hi l (hl.trans_lt hk))
  have he := coeff_deriv_normal_comparison_log_first D s E f T e b v n hn
    hE0 hf0 hT0 hE hf hT
  dsimp only at he
  simp only [hR0, inv_one, map_one, one_mul] at he
  rw [coeff_deriv_normal_defect D _ _ n hn hR0 hrho hprev, he, smul_eq_mul]

end SkewCornerDescent.Matrix
