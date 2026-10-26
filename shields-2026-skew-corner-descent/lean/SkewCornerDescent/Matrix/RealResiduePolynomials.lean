/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueBandFractions
import SkewCornerDescent.RationalExposure

/-!
# Faithful real polynomial representatives of actual residue responses

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Rational coefficients and surviving original indices embed injectively into real
polynomials. Actual retained corrections acquire lower-denominator representatives,
and distinct residue fractions retain a nonzero real cross-difference polynomial.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- Reindex the surviving original generators literally and embed rational coefficients. -/
noncomputable def realResiduePolynomial (N : ℕ+) :
    OtherPolynomial N →+* MvPolynomial ℕ ℝ :=
  (MvPolynomial.rename (fun j : {j : ℕ+ // j ≠ N} => (j.val : ℕ))).toRingHom.comp
    (MvPolynomial.map (algebraMap ℚ ℝ))

/-- Real coefficient extension and literal reindexing lose no polynomial identities. -/
theorem realResiduePolynomial_injective (N : ℕ+) :
    Function.Injective (realResiduePolynomial N) := by
  apply (MvPolynomial.rename_injective _ ?_).comp
    (MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective)
  intro i j he
  apply Subtype.ext
  exact Subtype.ext he

/-- Lower support survives the real polynomial representative without shifting its top. -/
theorem realResiduePolynomial_vars_lt (N K : ℕ+) {p : OtherPolynomial N}
    (hp : p ∈ supported ℚ {j : {j : ℕ+ // j ≠ N} | j.val < K}) :
    ∀ j ∈ (realResiduePolynomial N p).vars, j < (K : ℕ) := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hj)
  exact mem_supported.mp hp (vars_map p (algebraMap ℚ ℝ) hi)

/-- A nonzero actual polynomial denominator remains a nonzero real polynomial. -/
theorem realResiduePolynomial_ne_zero (N : ℕ+) {p : OtherPolynomial N} (hp : p ≠ 0) :
    realResiduePolynomial N p ≠ 0 :=
  (map_ne_zero_iff _ (realResiduePolynomial_injective N)).mpr hp

/-- Distinct actual residue fractions have a nonzero real cross-difference polynomial. -/
theorem real_cross_difference_ne_zero (N : ℕ+) (p q r s : OtherPolynomial N)
    (hq : q ≠ 0) (hs : s ≠ 0)
    (hne : algebraMap (OtherPolynomial N) (OtherField N) p /
      algebraMap (OtherPolynomial N) (OtherField N) q ≠
      algebraMap (OtherPolynomial N) (OtherField N) r /
      algebraMap (OtherPolynomial N) (OtherField N) s) :
    realResiduePolynomial N p * realResiduePolynomial N s -
      realResiduePolynomial N r * realResiduePolynomial N q ≠ 0 := by
  rw [← map_mul, ← map_mul, ← map_sub]
  apply realResiduePolynomial_ne_zero
  intro he
  apply hne
  apply (div_eq_div_iff
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs)).mpr
  have hv := congrArg (algebraMap (OtherPolynomial N) (OtherField N)) he
  simpa only [map_sub, map_mul, map_zero, sub_eq_zero] using hv

/-- An actual fraction identity survives every regular real specialization. -/
theorem real_fraction_eq_of_fraction_eq (N : ℕ+) (p q r s : OtherPolynomial N)
    (hq : q ≠ 0) (hs : s ≠ 0)
    (he : algebraMap (OtherPolynomial N) (OtherField N) p /
      algebraMap (OtherPolynomial N) (OtherField N) q =
      algebraMap (OtherPolynomial N) (OtherField N) r /
      algebraMap (OtherPolynomial N) (OtherField N) s)
    (x : ℕ → ℝ)
    (hqx : MvPolynomial.eval x (realResiduePolynomial N q) ≠ 0)
    (hsx : MvPolynomial.eval x (realResiduePolynomial N s) ≠ 0) :
    MvPolynomial.eval x (realResiduePolynomial N p) /
      MvPolynomial.eval x (realResiduePolynomial N q) =
      MvPolynomial.eval x (realResiduePolynomial N r) /
      MvPolynomial.eval x (realResiduePolynomial N s) := by
  have hc : p * s = r * q := (IsFractionRing.injective (OtherPolynomial N)
      (OtherField N)) (by
    simp only [map_mul]
    exact (div_eq_div_iff
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq)
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs)).mp he)
  apply (div_eq_div_iff hqx hsx).mpr
  have h := congrArg (fun f => MvPolynomial.eval x (realResiduePolynomial N f)) hc
  simpa only [map_mul] using h

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual residue response has produced polynomial representatives with lower denominators. -/
theorem originalLocalResponse_residue_representatives {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ p ∈ supported ℚ {j : {j : ℕ+ // j ≠ c.top} | j.val < K},
    ∃ q ∈ supported ℚ {j : {j : ℕ+ // j ≠ c.top} | j.val < c.top}, q ≠ 0 ∧
      c.regularResidue (c.originalLocalResponse P b d) =
        residueGenerator c.top ⟨K, ne_of_gt hNK⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) p /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) q := by
  obtain ⟨A, hA, he⟩ := c.originalLocalResponse_residue_polynomial P b d K hNK hK hmax
  obtain ⟨p, hp, q, hq, hq0, hrepr⟩ := residuePolynomialBand_fraction c.top K hNK.le hA
  refine ⟨p, hp, q, hq, hq0, ?_⟩
  rw [he, hrepr, c.residueMap_other K (ne_of_gt hNK)]
  rfl

end SelectedCoordinate
end SkewCornerDescent.Matrix
