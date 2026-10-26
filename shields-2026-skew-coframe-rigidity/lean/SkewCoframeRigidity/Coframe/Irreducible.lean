/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Model

/-!
# Irreducibility of the model coframe

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:coprime`.  The model coframe
`1 + ∑ y_j z^{s_j}` is linear in each private variable `y_j` with coprime coefficients `z^{s_j}`
and `1 + ∑_{i ≠ j} y_i z^{s_i}`, hence irreducible; it is primitive, so Gauss's lemma carries
the irreducibility over to the raw field.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ} (D : BetaDiagram (n + 1))

/-- The variable of the `j`-th native coefficient in the model ring. -/
abbrev yVar (j : Fin n) : VarIdx D := Sum.inl (some (Sum.inl j))

theorem yVar_injective : Function.Injective (yVar D) := by
  intro i j h
  simpa [yVar] using h

/-- The model coframe as a polynomial in the coefficients and an extra variable `z`. -/
noncomputable def mGmv : MvPolynomial (Option (VarIdx D)) ℚ :=
  1 + ∑ j : Fin n, MvPolynomial.X (some (yVar D j)) * MvPolynomial.X none ^ colPos D j

theorem optionEquivLeft_mGmv :
    MvPolynomial.optionEquivLeft ℚ (VarIdx D) (mGmv D) = mG D := by
  simp [mGmv, mG, uniPoly]

theorem mGmv_irreducible (hn : 0 < n) : Irreducible (mGmv D) := by
  classical
  set j0 : Fin n := ⟨0, hn⟩
  set i : Option (VarIdx D) := some (yVar D j0) with hi
  set f : MvPolynomial (Option (VarIdx D)) ℚ := MvPolynomial.X none ^ colPos D j0 with hf
  set g : MvPolynomial (Option (VarIdx D)) ℚ :=
    1 + ∑ j ∈ Finset.univ.erase j0,
      MvPolynomial.X (some (yVar D j)) * MvPolynomial.X none ^ colPos D j with hg
  have hsplit : mGmv D = f * MvPolynomial.X i + g := by
    unfold mGmv
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
    rw [hf, hg, hi]
    ring
  rw [hsplit]
  apply MvPolynomial.irreducible_mul_X_add
  · exact pow_ne_zero _ (MvPolynomial.X_ne_zero _)
  · intro h
    have h1 := MvPolynomial.vars_pow _ _ h
    rw [MvPolynomial.vars_X] at h1
    simp [hi] at h1
  · intro h
    have h1 := MvPolynomial.vars_add_subset _ _ h
    rcases Finset.mem_union.mp h1 with h2 | h2
    · simp at h2
    · have h3 := MvPolynomial.vars_sum_subset _ _ h2
      obtain ⟨j, hj, hmem⟩ := Finset.mem_biUnion.mp h3
      have h4 := MvPolynomial.vars_mul _ _ hmem
      rcases Finset.mem_union.mp h4 with h5 | h5
      · rw [MvPolynomial.vars_X, Finset.mem_singleton] at h5
        have h7 : yVar D j0 = yVar D j := Option.some_injective _ h5
        exact (Finset.ne_of_mem_erase hj) (yVar_injective D h7).symm
      · have h6 := MvPolynomial.vars_pow _ _ h5
        rw [MvPolynomial.vars_X] at h6
        simp [hi] at h6
  · have hnd : ¬ (MvPolynomial.X none : MvPolynomial (Option (VarIdx D)) ℚ) ∣ g := by
      rintro ⟨q, hq⟩
      have := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) hq
      have hpos : ∀ j, 0 < colPos D j := colPos_pos D
      simp [hg, (hpos _).ne'] at this
    exact ((MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd).2 hnd).pow_left

theorem mG_irreducible (hn : 0 < n) : Irreducible (mG D) := by
  rw [← optionEquivLeft_mGmv]
  exact (MulEquiv.irreducible_iff
    (MvPolynomial.optionEquivLeft ℚ (VarIdx D)).toMulEquiv).2 (mGmv_irreducible D hn)

theorem mG_isPrimitive : (mG D).IsPrimitive := by
  intro r hr
  have := (Polynomial.C_dvd_iff_dvd_coeff r (mG D)).1 hr 0
  rw [mG, uniPoly_coeff_zero_of_pos _ _ (colPos_pos D)] at this
  exact isUnit_of_dvd_one this

/-- The algebra structure of the coordinate ring over the raw field. -/
noncomputable abbrev modelAlgebra : Algebra (ModelRing D) CohField :=
  (toField D : ModelRing D →+* CohField).toAlgebra

theorem isFractionRing_modelRing (hT : (properMatrixOf cohLetters D).det ≠ 0) :
    letI := modelAlgebra D
    IsFractionRing (ModelRing D) CohField := by
  let _ := modelAlgebra D
  have hinj : Function.Injective (toField D) := toField_injective D hT
  have hcomp := toField_comp_fromField D hT
  have hcomp' : ∀ a : CohRing, toField D (fromField D a) = algebraMap CohRing CohField a :=
    fun a => congrArg (fun g : CohRing →ₐ[ℚ] CohField => g a) hcomp
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩
  · have : (y : ModelRing D) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    rw [isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ hinj).2 this
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := CohRing) (K := CohField) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap CohRing CohField b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2 hb0
    have hb' : fromField D b ∈ nonZeroDivisors (ModelRing D) := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro h0
      apply hbF
      rw [← hcomp' b, h0, map_zero]
    refine ⟨(fromField D a, ⟨fromField D b, hb'⟩), ?_⟩
    change algebraMap CohRing CohField a / algebraMap CohRing CohField b *
      toField D (fromField D b) = toField D (fromField D a)
    rw [hcomp', hcomp']
    field_simp
  · exact ⟨1, by simp [hinj h]⟩

theorem coframe_irreducible_aux (hT : (properMatrixOf cohLetters D).det ≠ 0) (hn : 0 < n) :
    Irreducible (coframe D) := by
  let _ := modelAlgebra D
  have _ := isFractionRing_modelRing D hT
  have h := ((mG_isPrimitive D).irreducible_iff_irreducible_map_fraction_map
    (K := CohField)).1 (mG_irreducible D hn)
  have e : (mG D).map (algebraMap (ModelRing D) CohField) = coframe D := toField_mG D
  rwa [e] at h

theorem dvd_numerator_iff (hT : (properMatrixOf cohLetters D).det ≠ 0) :
    coframe D ∣ numerator D ↔ mG D ∣ mP D := by
  let _ := modelAlgebra D
  have _ := isFractionRing_modelRing D hT
  rw [(mG_isPrimitive D).dvd_iff_fraction_map_dvd_fraction_map CohField]
  have e1 : (mG D).map (algebraMap (ModelRing D) CohField) = coframe D := toField_mG D
  have e2 : (mP D).map (algebraMap (ModelRing D) CohField) = numerator D := toField_mP D hT
  rw [e1, e2]

/-- The specialization that sets every available numerator coordinate to zero. -/
noncomputable def killV : VarIdx D → ModelRing D
  | Sum.inl (some (Sum.inr _)) => 0
  | w => MvPolynomial.X w

theorem natDegree_mG_pos (hn : 0 < n) : 0 < (mG D).natDegree := by
  let j0 : Fin n := ⟨0, hn⟩
  have h : (mG D).coeff (colPos D j0) = MvPolynomial.X (yVar D j0) :=
    uniPoly_coeff_apply _ _ (colPos_injective D) (colPos_pos D) j0
  have h2 : colPos D j0 ≤ (mG D).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [h]; exact MvPolynomial.X_ne_zero _)
  exact lt_of_lt_of_le (colPos_pos D j0) h2

theorem map_killV_mG :
    (mG D).map (MvPolynomial.aeval (killV D) : ModelRing D →ₐ[ℚ] ModelRing D).toRingHom =
      mG D := by
  unfold mG
  rw [uniPoly_map]
  congr 1
  funext j
  simp [killV]

theorem map_killV_mP :
    (mP D).map (MvPolynomial.aeval (killV D) : ModelRing D →ₐ[ℚ] ModelRing D).toRingHom =
      C (MvPolynomial.X (Sum.inl none) : ModelRing D) := by
  ext i
  rw [Polynomial.coeff_map, mP_coeff, Polynomial.coeff_C]
  by_cases h0 : i = 0
  · subst h0
    simp only [ite_eq_left (span_pos D), ite_true]
    unfold mNum
    rw [ite_eq_left rfl]
    simp [killV]
  · rw [ite_eq_right h0]
    by_cases hi : i < span D
    · rw [ite_eq_left hi]
      unfold mNum
      rw [ite_eq_right h0]
      by_cases hc : 0 < i ∧ i < span D ∧ i ∉ rowSet D
      · rw [dite_eq_left hc]
        simp [killV]
      · rw [dite_eq_right hc]
        simp
    · rw [ite_eq_right hi]
      simp

theorem mG_not_dvd_mP (hn : 0 < n) : ¬ mG D ∣ mP D := by
  rintro ⟨q, hq⟩
  have h := congrArg (Polynomial.map
    (MvPolynomial.aeval (killV D) : ModelRing D →ₐ[ℚ] ModelRing D).toRingHom) hq
  rw [Polynomial.map_mul, map_killV_mG, map_killV_mP] at h
  have hθ : (MvPolynomial.X (Sum.inl none) : ModelRing D) ≠ 0 := MvPolynomial.X_ne_zero _
  have hq0 : Polynomial.map
      (MvPolynomial.aeval (killV D) : ModelRing D →ₐ[ℚ] ModelRing D).toRingHom q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact (Polynomial.C_ne_zero.2 hθ) h
  have hG0 : mG D ≠ 0 := by
    intro h0
    have := natDegree_mG_pos D hn
    rw [h0] at this
    simp at this
  have := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_mul hG0 hq0, Polynomial.natDegree_C] at this
  have := natDegree_mG_pos D hn
  omega

theorem coframe_not_dvd_numerator_aux (hT : (properMatrixOf cohLetters D).det ≠ 0)
    (hn : 0 < n) : ¬ coframe D ∣ numerator D := by
  rw [dvd_numerator_iff D hT]
  exact mG_not_dvd_mP D hn

end SkewCoframeRigidity.Coframe
