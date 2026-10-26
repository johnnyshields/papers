/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPositiveExtraWitness
import SkewCornerDescent.RegularFractionExpressions

/-!
# Nonzero original discrepancy energy over actual response classes

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
One common positive actual chamber avoids a nonzero discrepancy numerator
and every discrepancy denominator.  Clearing the same finite dependent
fraction expression transfers a hypothetical zero identity, contradicting
its strictly positive real specialization.  No response independence or
map of the entire fraction field is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A nonzero family of original rational discrepancies has nonzero squared
energy over actual response classes.  The common positive chamber avoids the
chosen numerator and every discrepancy denominator.  Only the finite dependent
expression is specialized; no map of the whole fraction field is asserted. -/
theorem originalResponseClasses_square_energy_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    {I : Type*} [Fintype I] (weight : I → c.OriginalResponseClass P)
    (η : I → OtherField c.top) (hη : ∃ i, η i ≠ 0) :
    (∑ i, (η i)^2 / (weight i).val) ≠ 0 := by
  classical
  let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
  have hfractions (i : I) : ∃ u v : OtherPolynomial c.top, v ≠ 0 ∧ ι u / ι v = η i := by
    obtain ⟨u, v, hv, he⟩ := IsFractionRing.div_surjective (OtherPolynomial c.top) (η i)
    exact ⟨u, v, mem_nonZeroDivisors_iff_ne_zero.mp hv, he⟩
  choose u v hv hrep using hfractions
  obtain ⟨i0, hi0⟩ := hη
  have hu0 : u i0 ≠ 0 := by
    intro hz
    have hh := hrep i0
    rw [hz, map_zero, zero_div] at hh
    exact hi0 hh.symm
  let G := u i0 * ∏ i, v i
  have hG : G ≠ 0 := mul_ne_zero hu0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i))
  obtain ⟨num, den, x, hresponse, hnumF, _, hnumR, _, hpositive, havoid⟩ :=
    c.originalResponseClasses_positive_avoiding P hB hmax G hG
  let φ : OtherPolynomial c.top →+* ℝ := (MvPolynomial.eval x).comp (realResiduePolynomial c.top)
  have hGu : φ (u i0) ≠ 0 := by
    intro hz
    apply havoid
    change φ (u i0 * ∏ i, v i) = 0
    rw [map_mul, hz, zero_mul]
  have hGv : (∏ i, φ (v i)) ≠ 0 := by
    intro hz
    apply havoid
    change φ (u i0 * ∏ i, v i) = 0
    rw [map_mul, map_prod, hz, mul_zero]
  have hvR (i) : φ (v i) ≠ 0 := (Finset.prod_ne_zero_iff.mp hGv) i (Finset.mem_univ i)
  have hvF (i) : ι (v i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hv i)
  let numerator : I ⊕ c.OriginalResponseClass P → OtherPolynomial c.top := Sum.elim u den
  let denominator : I ⊕ c.OriginalResponseClass P → OtherPolynomial c.top := Sum.elim v num
  let expr : MvPolynomial (I ⊕ c.OriginalResponseClass P) (OtherPolynomial c.top) :=
    ∑ i, (MvPolynomial.X (.inl i))^2 * MvPolynomial.X (.inr (weight i))
  have hdenF (i) : ι (denominator i) ≠ 0 := by
    cases i with
    | inl i => exact hvF i
    | inr X => exact hnumF X
  have hdenR (i) : φ (denominator i) ≠ 0 := by
    cases i with
    | inl i => exact hvR i
    | inr X => exact hnumR X
  have hweightF (i) : ι (den (weight i)) / ι (num (weight i)) = (weight i).val⁻¹ := by
    rw [hresponse, inv_div]
  intro hzero
  have hsource : expr.eval₂ ι (fun i => ι (numerator i) / ι (denominator i)) = 0 := by
    have heval : expr.eval₂ ι (fun i => ι (numerator i) / ι (denominator i)) =
        ∑ i, (ι (u i) / ι (v i))^2 * (ι (den (weight i)) / ι (num (weight i))) := by
      simp [expr, numerator, denominator]
    rw [heval]
    simp only [hrep, hweightF]
    simpa only [div_eq_mul_inv] using hzero
  have htarget := eval₂_fraction_zero_transfer ι φ (IsFractionRing.injective _ _)
    numerator denominator hdenF hdenR expr hsource
  have hzeroR : (∑ i, (φ (u i) / φ (v i))^2 *
      (φ (den (weight i)) / φ (num (weight i)))) = 0 := by
    simpa [expr, numerator, denominator] using htarget
  have hweightR (i) : 0 < φ (den (weight i)) / φ (num (weight i)) := by
    simpa only [inv_div] using inv_pos.mpr (hpositive (weight i))
  have hnonneg (i) : 0 ≤ (φ (u i) / φ (v i))^2 *
      (φ (den (weight i)) / φ (num (weight i))) :=
    mul_nonneg (sq_nonneg _) (hweightR i).le
  have hpos : 0 < (φ (u i0) / φ (v i0))^2 *
      (φ (den (weight i0)) / φ (num (weight i0))) :=
    mul_pos (sq_pos_of_ne_zero (div_ne_zero hGu (hvR i0))) (hweightR i0)
  have hsum := Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ i0)
  have hsumPos := lt_of_lt_of_le hpos hsum
  rw [hzeroR] at hsumPos
  exact (lt_irrefl 0) hsumPos

end SkewCornerDescent.Matrix.SelectedCoordinate
