/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalSeries
import SkewCornerDescent.Matrix.OriginalHessenberg

/-!
# Complete original Hessenberg responses in the normal series chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The genuine selected coefficient is constant in the normal variable, each selected
subdiagonal is exactly that variable divided by the coefficient, and every signed
interval contraction retains the full original response and trailing determinant series.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- An original polynomial omitting the selected generator stays constant in the actual
normal chart. This applies to the complete selected cofactor, not just its residue. -/
theorem normalChart_of_top_notMem (f : Lambda) (hf : c.top ∉ f.vars) :
    c.normalChart f = Polynomial.C
      (algebraMap (OtherPolynomial c.top) (OtherField c.top)
        ((splitGenerator c.top f).coeff 0)) := by
  let := invertibleOfNonzero c.normalCoefficient_ne_zero
  change (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm
    (splitOverField c.top f) = _
  have hs : splitOverField c.top f = Polynomial.C
      (algebraMap (OtherPolynomial c.top) (OtherField c.top)
        ((splitGenerator c.top f).coeff 0)) := by
    change (splitGenerator c.top f).map (algebraMap _ (OtherField c.top)) = _
    conv_lhs => rw [splitGenerator_eq_constant c.top f hf]
    rw [Polynomial.map_C]
  rw [hs]
  simp

/-- The entire original selected coefficient has no positive-order normal jets. -/
theorem normalSeries_coefficient :
    c.normalSeries (algebraMap Lambda c.RegularRing c.coefficient) =
      PowerSeries.C c.normalCoefficient := by
  rw [c.normalSeries_polynomial]
  simp only [normalPolynomialSeries, RingHom.comp_apply,
    Polynomial.coeToPowerSeries.ringHom_apply,
    c.normalChart_of_top_notMem c.coefficient c.top_notMem_coefficient, Polynomial.coe_C]
  rfl

/-- The actual selected diagonal has exactly its full normal quotient, with no higher
inverse jets introduced by the lower selected coefficient. -/
theorem originalSelected_normalSeries {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    c.normalSeries (c.originalLocalResponse P (some b) (some b)) =
      PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹ := by
  have he := congrArg c.normalSeries (originalLocalResponse_mul_coefficient P b c)
  rw [map_mul, c.normalSeries_coefficient, c.normalSeries_prime] at he
  have hm := congrArg (fun z : PowerSeries (OtherField c.top) =>
    z * PowerSeries.C (c.normalCoefficient)⁻¹) he
  simpa only [mul_assoc, ← map_mul, mul_inv_cancel₀ c.normalCoefficient_ne_zero,
    map_one, mul_one] using hm

/-- Every original selected subdiagonal has the same exact normal series. -/
theorem originalHessenberg_normalSeries_subdiagonal {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    c.normalSeries (c.originalHessenbergResponse P i.succ i.castSucc) =
      PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹ := by
  change c.normalSeries (c.originalLocalResponse P
    (originalHessenbergRows (hD := hD) P i.succ)
    (originalHessenbergCols (hD := hD) P i.castSucc)) = _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  exact c.originalSelected_normalSeries P _

/-- The complete actual source determinant has its signed interval expansion as a series.
Neither a diagonal-only inverse nor a truncated response replaces an original entry. -/
theorem originalHessenberg_normalSeries_det {n : ℕ} (P : Profile n) :
    let A := (c.originalHessenbergResponse P).map c.normalSeries
    c.normalSeries (c.originalHessenbergResponse P).det =
      ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
        (-1) ^ (j : ℕ) * A 0 j *
          ((PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹) ^ (j : ℕ) *
            (contractionTail A j).det) := by
  dsimp only
  rw [RingHom.map_det]
  apply hessenberg_det_constant_subdiagonal
  · intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P i j) = 0
    rw [c.originalHessenbergResponse_isUpperHessenberg P i j hij, map_zero]
  · exact c.originalHessenberg_normalSeries_subdiagonal P

end SkewCornerDescent.Matrix.SelectedCoordinate
