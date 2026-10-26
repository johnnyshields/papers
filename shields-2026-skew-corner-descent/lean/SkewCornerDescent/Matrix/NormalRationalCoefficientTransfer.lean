/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalOrientationTransfer
import SkewCornerDescent.Matrix.NormalRationalIndependence

/-!
# Rational defect coefficient with the exact orientation and residue prefactor

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Signed full-series factorization and residue matching supply the prefactor transfer.
Every earlier prefactor coefficient is proved independent from the same original
factor coefficients; no independence of the prefactor is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F : Type*} [Field F] [CharZero F] [Module ℚ F]

/-- The full rational original defect has the prefactor-weighted signed logarithmic
coefficient. Only the original factors' earlier coefficients enter the independence inputs. -/
theorem coeff_deriv_full_rational_defect {ι : Type*} (D : Derivation ℚ F F)
    (s : Finset ι) (E f β : PowerSeries F) (α : ι → F) (e : ι → ℤ)
    (ε : F) (v d n : ℕ) (hn : 0 < n)
    (hf0 : PowerSeries.constantCoeff f ≠ 0) (hE0 : PowerSeries.constantCoeff E ≠ 0)
    (hε : ε ≠ 0) (hDε : D ε = 0)
    (hT0 : ∀ i ∈ s,
      PowerSeries.constantCoeff (β - PowerSeries.C (α i) * f ^ 2) ≠ 0)
    (he : (∑ i ∈ s, e i) = (d : ℤ))
    (hmatch : PowerSeries.constantCoeff E ^ (v + d) =
      ε * PowerSeries.constantCoeff f ^ v *
        ∏ i ∈ s, PowerSeries.constantCoeff (β - PowerSeries.C (α i) * f ^ 2) ^ e i)
    (hE : ∀ k, k < n → D (PowerSeries.coeff k E) = 0)
    (hf : ∀ k, k < n → D (PowerSeries.coeff k f) = 0)
    (hT : ∀ i ∈ s, ∀ k, k < n →
      D (PowerSeries.coeff k (β - PowerSeries.C (α i) * f ^ 2)) = 0) :
    let T := fun i => β - PowerSeries.C (α i) * f ^ 2
    let ρ := PowerSeries.C ε *
      signedNormalProduct s (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) e
    D (PowerSeries.coeff n (f ^ v * (E * f⁻¹ ^ 2) ^ (v + d) - ρ)) =
      PowerSeries.constantCoeff ρ *
        ((v + d : ℕ) * D (PowerSeries.coeff n
            (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff E)⁻¹ * E))) -
          (v : F) * D (PowerSeries.coeff n
            (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f))) -
          ∑ i ∈ s, (e i : F) * D (PowerSeries.coeff n
            (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (T i))⁻¹ * T i)))) := by
  classical
  let T := fun i => β - PowerSeries.C (α i) * f ^ 2
  let S := signedNormalProduct s T e
  let ρ := PowerSeries.C ε *
    signedNormalProduct s (fun i => β * f⁻¹ ^ 2 - PowerSeries.C (α i)) e
  let R := normalComparisonSeries s E f T e (v + d) v
  have hprod : (∏ i ∈ s, PowerSeries.constantCoeff (T i) ^ e i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => zpow_ne_zero _ (hT0 i hi))
  have hR0 : PowerSeries.constantCoeff R = ε := by
    dsimp only [R, normalComparisonSeries]
    rw [map_mul, map_pow, PowerSeries.constantCoeff_inv, map_mul, map_pow,
      signedNormalProduct_constant, hmatch]
    field_simp [hf0, hprod]
    rfl
  have hprevR : ∀ k, k < n → D (PowerSeries.coeff k R) = 0 := by
    intro k hk
    exact coeff_deriv_normal_comparison_zero D s E f T e (v + d) v k hf0 hT0
      (fun j hj => hE j (hj.trans_lt hk)) (fun j hj => hf j (hj.trans_lt hk))
      (fun i hi j hj => hT i hi j (hj.trans_lt hk))
  have hpref : ∀ k, k < n → D (PowerSeries.coeff k ρ) = 0 := by
    intro k hk
    exact coeff_deriv_rational_prefactor_zero D s f β α e ε d k hf0 hDε hT0 he
      (fun j hj => hf j (hj.trans_lt hk))
      (fun i hi j hj => hT i hi j (hj.trans_lt hk))
  have horient : E ^ (v + d) * (PowerSeries.C ε * f ^ v * S)⁻¹ =
      PowerSeries.C ε⁻¹ * R := by
    dsimp only [R, normalComparisonSeries, S]
    rw [PowerSeries.mul_inv_rev, PowerSeries.mul_inv_rev, PowerSeries.C_inv,
      PowerSeries.mul_inv_rev]
    ring
  have hfactor := normalRationalDefect_factorization s E f β α e ε v d hf0 hε hT0 he
  dsimp only at hfactor ⊢
  rw [horient] at hfactor
  rw [hfactor]
  have hDinv : D ε⁻¹ = 0 := by rw [Derivation.leibniz_inv, hDε, smul_zero]
  rw [coeff_deriv_oriented_normal_defect D ρ R ε⁻¹ (inv_ne_zero hε) hDinv n hn
    (by simpa only [inv_inv] using hR0) hpref hprevR]
  rw [coeff_deriv_normal_comparison_log_first D s E f T e (v + d) v n hn
    hE0 hf0 hT0 hE hf hT]

end SkewCornerDescent.Matrix
