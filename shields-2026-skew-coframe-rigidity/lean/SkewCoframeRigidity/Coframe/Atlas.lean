/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Model

/-!
# The coframe atlas

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:atlas`.  For a connected diagram `D` of
span `M`, the coframe `G` is supported exactly on `S_A`, the numerator `P = [HG]_{<M}` vanishes
exactly on `I_A` among the positions `0 < i < M`, and the native coefficients together with the
available numerator coefficients (and `ϑ`) are algebraically independent over `ℚ`.  The letters
below the span are polynomials in these coordinates, with `H = P / G (mod z^M)`, and the
Jacobi–Trudi determinant is the signed proper corner times the degree-`M` coefficient of `HG`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem coframe_coeff_colPos (D : BetaDiagram (n + 1)) (j : Fin n) :
    (coframe D).coeff (colPos D j) = coframeVec D j :=
  uniPoly_coeff_apply _ _ (colPos_injective D) (colPos_pos D) j

theorem atlasCoords_algebraicIndependent {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    AlgebraicIndependent ℚ (atlasCoords D) := by
  have hT := properDet_cohLetters_ne_zero hD
  have h : AlgebraicIndependent ℚ
      (Sum.elim (atlasCoords D) (fun k : ExtIdx D => cohLetters k.1)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    exact toField_injective D hT
  simpa using h.comp Sum.inl Sum.inl_injective

theorem coframe_coeff_ne_zero_iff {D : BetaDiagram (n + 1)} (hD : D.Connected) {s : ℕ}
    (hs : 0 < s) : (coframe D).coeff s ≠ 0 ↔ s ∈ colSet D := by
  by_cases h : s ∈ colSet D
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
    rw [coframe_coeff_colPos]
    exact iff_of_true ((atlasCoords_algebraicIndependent hD).ne_zero (some (Sum.inl j))) h
  · refine iff_of_false ?_ h
    simp only [not_not]
    apply uniPoly_coeff_of_ne _ _ _ hs
    intro j hj
    exact h (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

theorem numerator_coeff_eq_zero_iff {D : BetaDiagram (n + 1)} (hD : D.Connected) {i : ℕ}
    (h0 : 0 < i) (hM : i < span D) : (numerator D).coeff i = 0 ↔ i ∈ rowSet D := by
  by_cases h : i ∈ rowSet D
  · refine iff_of_true ?_ h
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
    exact numeratorOf_coeff_rowPos cohLetters D (properDet_cohLetters_ne_zero hD) j
  · refine iff_of_false ?_ h
    exact (atlasCoords_algebraicIndependent hD).ne_zero
      (some (Sum.inr ⟨i, h0, hM, h⟩) : AtlasIdx D)

theorem numerator_coeff_zero (D : BetaDiagram (n + 1)) :
    (numerator D).coeff 0 = cohLetters 0 :=
  numeratorOf_coeff_zero cohLetters D

theorem letter_mem_adjoin_atlas {D : BetaDiagram (n + 1)} (hD : D.Connected) {j : ℕ}
    (hj : j < span D) : cohLetters j ∈ Algebra.adjoin ℚ (Set.range (atlasCoords D)) :=
  letter_mem_adjoin D (properDet_cohLetters_ne_zero hD) hj

theorem letter_eq_numerator_div_coframe (D : BetaDiagram (n + 1)) {j : ℕ} (hj : j < span D) :
    PowerSeries.coeff j ((numerator D : PowerSeries CohField) *
      (coframe D : PowerSeries CohField)⁻¹) = cohLetters j :=
  coeff_numeratorOf_mul_inv cohLetters D hj

theorem algebraMap_cohSchur (D : BetaDiagram n) :
    algebraMap CohRing CohField (cohSchur D) = schurOf cohLetters D := by
  unfold cohSchur schurOf
  rw [fullMatrix_cohLetters, RingHom.map_det]

theorem algebraMap_cohCorner (D : BetaDiagram (n + 1)) :
    algebraMap CohRing CohField (cohCorner D) = cornerOf cohLetters D := by
  unfold cohCorner cornerOf
  rw [properMatrix_cohLetters, map_mul, map_pow, map_neg, map_one, RingHom.map_det]

theorem schur_eq_corner_mul_topQuotient {D : BetaDiagram (n + 1)} (hD : D.Connected) :
    algebraMap CohRing CohField (cohSchur D) =
      algebraMap CohRing CohField (cohCorner D) * topQuotient D := by
  rw [algebraMap_cohSchur, algebraMap_cohCorner]
  exact schurOf_eq_cornerOf_mul_topQuotientOf cohLetters D (properDet_cohLetters_ne_zero hD)

end SkewCoframeRigidity.Coframe
