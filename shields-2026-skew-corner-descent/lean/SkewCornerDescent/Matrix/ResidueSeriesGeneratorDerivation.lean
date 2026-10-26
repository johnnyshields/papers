/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.PowerSeriesCoefficientDerivation
import SkewCornerDescent.Matrix.ResidueEndpointGradient
import SkewCornerDescent.Matrix.ProtectedComponentMinors

/-!
# Actual surviving-generator derivatives of complete original normal entries

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The genuine original residue derivative acts coefficientwise on the entire normal
series. Actual affine support supplies the exact higher-generator derivative of
every original Jacobi--Trudi entry, including its selected-generator substitution.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- The genuine surviving-generator derivative on complete normal series. -/
def residueSeriesGeneratorDeriv (N : ℕ+) (j : {j : ℕ+ // j ≠ N}) :
    @Derivation ℚ (PowerSeries (OtherField N)) (PowerSeries (OtherField N)) _ _ _ _ _
      (inferInstance : Algebra ℚ (PowerSeries (OtherField N))).toModule := by
  let d : OtherField N →+ OtherField N :=
    { toFun := residueGeneratorDeriv N j
      map_zero' := (residueGeneratorDeriv N j).map_zero
      map_add' := (residueGeneratorDeriv N j).map_add }
  exact powerSeriesCoefficientDerivation d
    (fun q => by
      change residueGeneratorDeriv N j (algebraMap ℚ (OtherField N) q) = 0
      exact (residueGeneratorDeriv N j).map_algebraMap q)
    (by change residueGeneratorDeriv N j 1 = 0; exact (residueGeneratorDeriv N j).map_one_eq_zero)
    (fun f g => by
      change residueGeneratorDeriv N j (f * g) =
        f * residueGeneratorDeriv N j g + g * residueGeneratorDeriv N j f
      simpa only [smul_eq_mul] using (residueGeneratorDeriv N j).leibniz f g)

/-- Every complete normal jet is differentiated by the unchanged coefficient-field derivative. -/
theorem residueSeriesGeneratorDeriv_coeff (N : ℕ+) (j : {j : ℕ+ // j ≠ N})
    (f : PowerSeries (OtherField N)) (m : ℕ) :
    PowerSeries.coeff m (residueSeriesGeneratorDeriv N j f) =
      residueGeneratorDeriv N j (PowerSeries.coeff m f) := by
  unfold residueSeriesGeneratorDeriv
  exact powerSeriesCoefficientDerivation_coeff _ _ _ _ f m

/-- Constant series keep their actual surviving-generator derivative. -/
theorem residueSeriesGeneratorDeriv_C (N : ℕ+) (j : {j : ℕ+ // j ≠ N}) (x : OtherField N) :
    residueSeriesGeneratorDeriv N j (PowerSeries.C x) =
      PowerSeries.C (residueGeneratorDeriv N j x) := by
  unfold residueSeriesGeneratorDeriv
  exact powerSeriesCoefficientDerivation_C _ _ _ _ x

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every complete original JT entry has its exact higher-generator derivative.
No selected-coordinate coefficient, normal remainder or positive jet is frozen. -/
theorem normal_hh_higher_derivative (H : ℕ+) (hH : c.top < H) (z : ℤ) :
    residueSeriesGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩ (c.normalPolynomialSeries (hh z)) =
      if z = (H : ℤ) then 1 else 0 := by
  by_cases hz : z < (H : ℤ)
  · rw [ite_eq_right (ne_of_lt hz)]
    ext m
    rw [residueSeriesGeneratorDeriv_coeff, map_zero]
    exact residueGeneratorDeriv_lower c.top ⟨H, ne_of_gt hH⟩
      (c.normalPolynomialSeries_coeff_mem_lower H hH (hh_mem_strictly_below H z hz) m)
  · have hpos : 0 < z := by have := H.pos; omega
    let k : ℕ+ := ⟨z.toNat, by omega⟩
    have hk : (k : ℤ) = z := Int.toNat_of_nonneg hpos.le
    have hkN : k ≠ c.top := by
      intro he
      have he' := congrArg (fun t : ℕ+ => (t : ℤ)) he
      have hNH : (c.top : ℤ) < (H : ℤ) := by exact_mod_cast hH
      omega
    have he : c.normalPolynomialSeries (hh z) =
        PowerSeries.C (residueGenerator c.top ⟨k, hkN⟩) := by
      rw [← hk, hh_pnat]
      simp only [normalPolynomialSeries, RingHom.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, c.normalChart_other k hkN, Polynomial.coe_C]
      rfl
    rw [he, residueSeriesGeneratorDeriv_C, residueGeneratorDeriv_generator]
    have hi : (⟨k, hkN⟩ : {t : ℕ+ // t ≠ c.top}) = ⟨H, ne_of_gt hH⟩ ↔ z = (H : ℤ) := by
      constructor
      · intro he
        have h := congrArg (fun t : {t : ℕ+ // t ≠ c.top} => (t.val : ℤ)) he
        simpa only [hk] using h
      · intro he
        apply Subtype.ext
        exact_mod_cast hk.trans he
    simp only [hi, apply_ite, map_one, map_zero]
    split_ifs <;> rfl

end SelectedCoordinate
end SkewCornerDescent.Matrix
