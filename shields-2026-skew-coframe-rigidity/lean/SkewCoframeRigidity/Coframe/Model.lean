/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Coherent

/-!
# The coordinate ring of the atlas

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:atlas`.  The coframe coefficients, the
available numerator coefficients and the letters above the span are independent variables of a
polynomial ring `ModelRing`.  The inverse formula `H = P / G (mod z^M)` has polynomial
coefficients there, which gives a polynomial section of the coordinate map; a Cramer argument
in the fraction field then shows that the coordinate map is injective.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ} (D : BetaDiagram (n + 1))

/-- The letters above the span, which are independent of the coordinates. -/
abbrev ExtIdx : Type := {k : ℕ // span D ≤ k}

/-- The variables of the model ring. -/
abbrev VarIdx : Type := AtlasIdx D ⊕ ExtIdx D

/-- The polynomial ring in the atlas coordinates and the letters above the span. -/
abbrev ModelRing : Type := MvPolynomial (VarIdx D) ℚ

/-- The model coframe `1 + ∑ y_j z^{s_j}`. -/
noncomputable def mG : (ModelRing D)[X] :=
  uniPoly (fun j : Fin n => (MvPolynomial.X (Sum.inl (some (Sum.inl j))) : ModelRing D))
    (colPos D)

/-- The model numerator coefficients. -/
noncomputable def mNum (i : ℕ) : ModelRing D :=
  if i = 0 then MvPolynomial.X (Sum.inl none)
  else if h : 0 < i ∧ i < span D ∧ i ∉ rowSet D then
    MvPolynomial.X (Sum.inl (some (Sum.inr ⟨i, h⟩)))
  else 0

/-- The model numerator. -/
noncomputable def mP : (ModelRing D)[X] :=
  ∑ i ∈ Finset.range (span D), C (mNum D i) * X ^ i

/-- The inverse of the model coframe as a power series. -/
noncomputable def mGinv : PowerSeries (ModelRing D) :=
  PowerSeries.invOfUnit (mG D : PowerSeries (ModelRing D)) 1

/-- The model letters: `P / G` below the span and fresh variables above it. -/
noncomputable def mLetter (k : ℕ) : ModelRing D :=
  if h : k < span D then PowerSeries.coeff k ((mP D : PowerSeries (ModelRing D)) * mGinv D)
  else MvPolynomial.X (Sum.inr ⟨k, by omega⟩)

theorem constantCoeff_mG : PowerSeries.constantCoeff (mG D : PowerSeries (ModelRing D)) = 1 :=
  constantCoeff_uniPoly _ _ (colPos_pos D)

theorem mG_mul_mGinv : (mG D : PowerSeries (ModelRing D)) * mGinv D = 1 := by
  unfold mGinv
  exact PowerSeries.mul_invOfUnit _ 1 (by rw [constantCoeff_mG]; rfl)

theorem constantCoeff_mGinv : PowerSeries.constantCoeff (mGinv D) = 1 := by
  unfold mGinv
  rw [PowerSeries.constantCoeff_invOfUnit]
  simp

theorem mP_coeff (i : ℕ) : (mP D).coeff i = if i < span D then mNum D i else 0 := by
  unfold mP
  rw [finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : i < span D
  · rw [ite_eq_left h, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hi
      exact absurd (Finset.mem_range.mpr h) hi
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro b hb
    have := Finset.mem_range.mp hb
    have : i ≠ b := by omega
    simp [this]

theorem mLetter_of_lt {k : ℕ} (hk : k < span D) :
    mLetter D k = PowerSeries.coeff k ((mP D : PowerSeries (ModelRing D)) * mGinv D) := by
  unfold mLetter
  rw [dite_eq_left hk]

theorem mLetter_of_ge {k : ℕ} (hk : span D ≤ k) :
    mLetter D k = MvPolynomial.X (Sum.inr ⟨k, hk⟩) := by
  unfold mLetter
  rw [dite_eq_right (by omega)]

theorem mLetter_zero : mLetter D 0 = MvPolynomial.X (Sum.inl none) := by
  rw [mLetter_of_lt D (span_pos D), PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    constantCoeff_mGinv, mul_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Polynomial.coeff_coe, mP_coeff, ite_eq_left (span_pos D)]
  unfold mNum
  rw [ite_eq_left rfl]

/-- Up to degree `< M`, the letters times the model coframe reproduce the model numerator. -/
theorem coeff_mLetter_mul_mG {i : ℕ} (hi : i < span D) :
    PowerSeries.coeff i (seriesOf (mLetter D) * (mG D : PowerSeries (ModelRing D))) =
      mNum D i := by
  have h1 : PowerSeries.coeff i (seriesOf (mLetter D) * (mG D : PowerSeries (ModelRing D))) =
      PowerSeries.coeff i (((mP D : PowerSeries (ModelRing D)) * mGinv D) *
        (mG D : PowerSeries (ModelRing D))) := by
    apply coeff_mul_congr
    intro k hk
    rw [seriesOf, PowerSeries.coeff_mk, mLetter_of_lt D (by omega)]
  rw [h1, mul_assoc, mul_comm (mGinv D), mG_mul_mGinv, mul_one, Polynomial.coeff_coe, mP_coeff,
    ite_eq_left hi]

theorem properMatrix_mLetter_mulVec :
    properMatrixOf (mLetter D) D *ᵥ
        (fun j : Fin n => (MvPolynomial.X (Sum.inl (some (Sum.inl j))) : ModelRing D)) =
      -topVecOf (mLetter D) D := by
  funext i
  have h1 := coeff_rowPos (mLetter D) D
    (fun j : Fin n => (MvPolynomial.X (Sum.inl (some (Sum.inl j))) : ModelRing D)) i
  have h2 := coeff_mLetter_mul_mG D (rowPos_lt_span D i)
  have h3 : mNum D (rowPos D i) = 0 := by
    have h0 : rowPos D i ≠ 0 := (rowPos_pos D i).ne'
    have hI : rowPos D i ∈ rowSet D := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    simp [mNum, h0, hI]
  have : seriesOf (mLetter D) * (mG D : PowerSeries (ModelRing D)) =
      seriesOf (mLetter D) * (uniPoly (fun j : Fin n =>
        (MvPolynomial.X (Sum.inl (some (Sum.inl j))) : ModelRing D)) (colPos D) :
          PowerSeries (ModelRing D)) := rfl
  rw [this, h3] at h2
  unfold seriesOf at h1 h2
  rw [h2] at h1
  simp only [Pi.neg_apply]
  linear_combination -h1

/-- The coordinate map from the model ring into the raw field. -/
noncomputable def toField : ModelRing D →ₐ[ℚ] CohField :=
  MvPolynomial.aeval (Sum.elim (atlasCoords D) (fun k : ExtIdx D => cohLetters k.1))

/-- The polynomial section of the coordinate map. -/
noncomputable def fromField : CohRing →ₐ[ℚ] ModelRing D := MvPolynomial.aeval (mLetter D)

theorem uniPoly_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : Fin n → R)
    (s : Fin n → ℕ) : (uniPoly g s).map f = uniPoly (fun j => f (g j)) s := by
  unfold uniPoly
  simp [Polynomial.map_add, Polynomial.map_sum]

theorem toField_ringHom_apply (x : ModelRing D) :
    (toField D : ModelRing D →+* CohField) x = toField D x := rfl

theorem toField_X (v : VarIdx D) :
    toField D (MvPolynomial.X v) =
      Sum.elim (atlasCoords D) (fun k : ExtIdx D => cohLetters k.1) v :=
  MvPolynomial.aeval_X _ _

theorem coframeVec_eq : coframeVec D = coframeVecOf cohLetters D := rfl

theorem toField_mG : (mG D).map (toField D : ModelRing D →+* CohField) = coframe D := by
  unfold mG
  rw [uniPoly_map]
  change uniPoly _ (colPos D) = uniPoly (coframeVecOf cohLetters D) (colPos D)
  congr 1
  funext j
  rw [toField_ringHom_apply, toField_X]
  rfl

theorem toField_mNum (hT : (properMatrixOf cohLetters D).det ≠ 0) {i : ℕ} (hi : i < span D) :
    toField D (mNum D i) = (numerator D).coeff i := by
  by_cases h0 : i = 0
  · subst h0
    have := numeratorOf_coeff_zero cohLetters D
    have e : (numerator D).coeff 0 = cohLetters 0 := this
    rw [e]
    unfold mNum
    rw [ite_eq_left rfl, toField_X]
    rfl
  · by_cases hI : i ∈ rowSet D
    · have h3 : mNum D i = 0 := by simp [mNum, h0, hI]
      rw [h3, map_zero]
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hI
      exact (numeratorOf_coeff_rowPos cohLetters D hT j).symm
    · have hc : 0 < i ∧ i < span D ∧ i ∉ rowSet D := ⟨Nat.pos_of_ne_zero h0, hi, hI⟩
      have h3 : mNum D i = MvPolynomial.X (Sum.inl (some (Sum.inr ⟨i, hc⟩))) := by
        unfold mNum
        rw [ite_eq_right h0, dite_eq_left hc]
      rw [h3, toField_X]
      rfl

theorem toField_mP (hT : (properMatrixOf cohLetters D).det ≠ 0) :
    (mP D).map (toField D : ModelRing D →+* CohField) = numerator D := by
  ext i
  rw [Polynomial.coeff_map, mP_coeff, toField_ringHom_apply]
  by_cases hi : i < span D
  · rw [ite_eq_left hi, toField_mNum D hT hi]
  · rw [ite_eq_right hi, map_zero]
    unfold numerator
    rw [numeratorOf_coeff, ite_eq_right hi]

theorem toField_mGinv :
    PowerSeries.map (toField D : ModelRing D →+* CohField) (mGinv D) =
      (coframe D : PowerSeries CohField)⁻¹ := by
  have hc : PowerSeries.constantCoeff (coframe D : PowerSeries CohField) ≠ 0 := by
    unfold coframe
    rw [constantCoeff_coframeOf]; exact one_ne_zero
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc]
  have := congrArg (PowerSeries.map (toField D : ModelRing D →+* CohField)) (mG_mul_mGinv D)
  rw [map_mul, map_one, ← Polynomial.polynomial_map_coe, toField_mG] at this
  rw [mul_comm]
  exact this

theorem toField_mLetter (hT : (properMatrixOf cohLetters D).det ≠ 0) (k : ℕ) :
    toField D (mLetter D k) = cohLetters k := by
  by_cases hk : k < span D
  · rw [mLetter_of_lt D hk, ← toField_ringHom_apply, ← PowerSeries.coeff_map, map_mul,
      ← Polynomial.polynomial_map_coe, toField_mP D hT, toField_mGinv D]
    exact coeff_numeratorOf_mul_inv cohLetters D hk
  · rw [mLetter_of_ge D (by omega), toField_X]
    rfl

theorem toField_comp_fromField (hT : (properMatrixOf cohLetters D).det ≠ 0) :
    (toField D).comp (fromField D) = IsScalarTower.toAlgHom ℚ CohRing CohField := by
  apply MvPolynomial.algHom_ext
  intro k
  simp [fromField, toField_mLetter D hT, cohLetters]

theorem fromField_injective (hT : (properMatrixOf cohLetters D).det ≠ 0) :
    Function.Injective (fromField D) := by
  intro a b hab
  have h := congrArg (fun g : CohRing →ₐ[ℚ] CohField => g a) (toField_comp_fromField D hT)
  have h' := congrArg (fun g : CohRing →ₐ[ℚ] CohField => g b) (toField_comp_fromField D hT)
  simp only [AlgHom.comp_apply, hab] at h h'
  apply IsFractionRing.injective CohRing CohField
  exact h.symm.trans h'

theorem properMatrixOf_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (h : ℕ → R)
    (E : BetaDiagram (n + 1)) :
    properMatrixOf (fun k => φ (h k)) E = φ.mapMatrix (properMatrixOf h E) := by
  refine Matrix.ext fun i j => ?_
  simp only [properMatrixOf, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact letterOf_map φ (map_zero φ) h _

theorem topVecOf_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (h : ℕ → R)
    (E : BetaDiagram (n + 1)) :
    topVecOf (fun k => φ (h k)) E = fun i => φ (topVecOf h E i) := by
  funext i
  exact letterOf_map φ (map_zero φ) h _

/-- The coordinate map is injective: the model ring is the coordinate ring of the atlas. -/
theorem toField_injective (hT : (properMatrixOf cohLetters D).det ≠ 0) :
    Function.Injective (toField D) := by
  let K' := FractionRing (ModelRing D)
  let f : ModelRing D →+* K' := algebraMap (ModelRing D) K'
  have hf : Function.Injective f := IsFractionRing.injective (ModelRing D) K'
  let θhat : CohRing →+* K' := f.comp (fromField D : CohRing →+* ModelRing D)
  have hθ : Function.Injective θhat := hf.comp (fromField_injective D hT)
  let Ψ : CohField →+* K' := IsFractionRing.lift hθ
  have hΨ : Function.Injective Ψ := Ψ.injective
  have hΨ0 : ∀ x : CohRing, Ψ (algebraMap CohRing CohField x) = θhat x :=
    fun x => IsFractionRing.lift_algebraMap (K := CohField) hθ x
  have hΨletter : ∀ k : ℕ, Ψ (cohLetters k) = f (mLetter D k) := by
    intro k
    change Ψ (algebraMap CohRing CohField (MvPolynomial.X k)) = _
    rw [hΨ0]
    simp [θhat, fromField]
  have hlet : (fun k => f (mLetter D k)) = fun k => Ψ (cohLetters k) := by
    funext k; exact (hΨletter k).symm
  let yG : Fin n → ModelRing D := fun j => MvPolynomial.X (Sum.inl (some (Sum.inl j)))
  -- the native coefficients
  have hv : (fun j => Ψ (coframeVec D j)) = fun j => f (yG j) := by
    have hdet : (properMatrixOf (fun k => f (mLetter D k)) D).det ≠ 0 := by
      rw [hlet, properMatrixOf_map Ψ cohLetters D, ← RingHom.map_det]
      exact (map_ne_zero_iff _ hΨ).2 hT
    have e1 : properMatrixOf (fun k => f (mLetter D k)) D *ᵥ (fun j => Ψ (coframeVec D j)) =
        -(topVecOf (fun k => f (mLetter D k)) D) := by
      have h0 := properMatrix_mulVec_coframeVecOf cohLetters D hT
      rw [hlet, properMatrixOf_map Ψ cohLetters D, topVecOf_map]
      funext i
      have := congrArg Ψ (congrFun h0 i)
      rw [RingHom.map_mulVec, Pi.neg_apply, map_neg] at this
      exact this
    have e2 : properMatrixOf (fun k => f (mLetter D k)) D *ᵥ (fun j => f (yG j)) =
        -(topVecOf (fun k => f (mLetter D k)) D) := by
      have h0 := properMatrix_mLetter_mulVec D
      rw [properMatrixOf_map f (mLetter D) D, topVecOf_map]
      funext i
      have := congrArg f (congrFun h0 i)
      rw [RingHom.map_mulVec, Pi.neg_apply, map_neg] at this
      exact this
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet
      (v := (fun j => Ψ (coframeVec D j)) - fun j => f (yG j))
      (by rw [Matrix.mulVec_sub, e1, e2, sub_self])
    exact sub_eq_zero.mp this
  -- the model coframe maps to the coframe
  have hfromG : (mG D).map f = (coframe D).map Ψ := by
    change (uniPoly yG (colPos D)).map f =
      (uniPoly (coframeVec D) (colPos D)).map Ψ
    rw [uniPoly_map, uniPoly_map]
    congr 1
    exact hv.symm
  have hseries : PowerSeries.map Ψ (seriesOf cohLetters) =
      PowerSeries.map f (seriesOf (mLetter D)) := by
    ext k
    simp only [PowerSeries.coeff_map, seriesOf, PowerSeries.coeff_mk]
    exact (hΨletter k)
  have hnum : ∀ i : FreeRows D, Ψ ((numerator D).coeff i.1) =
      f (MvPolynomial.X (Sum.inl (some (Sum.inr i)))) := by
    intro i
    obtain ⟨i, hc⟩ := i
    have e1 : (numerator D).coeff i =
        PowerSeries.coeff i (seriesOf cohLetters * (coframe D : PowerSeries CohField)) := by
      unfold numerator
      rw [numeratorOf_coeff, ite_eq_left hc.2.1]
      rfl
    have e2 : PowerSeries.map Ψ (coframe D : PowerSeries CohField) =
        PowerSeries.map f (mG D : PowerSeries (ModelRing D)) := by
      rw [← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, hfromG]
    have h3 : mNum D i = MvPolynomial.X (Sum.inl (some (Sum.inr ⟨i, hc⟩))) := by
      unfold mNum
      rw [ite_eq_right hc.1.ne', dite_eq_left hc]
    have h4 := coeff_mLetter_mul_mG D hc.2.1
    rw [h3] at h4
    calc Ψ ((numerator D).coeff i)
        = PowerSeries.coeff i (PowerSeries.map Ψ (seriesOf cohLetters *
            (coframe D : PowerSeries CohField))) := by rw [e1, PowerSeries.coeff_map]
      _ = PowerSeries.coeff i (PowerSeries.map f (seriesOf (mLetter D) *
            (mG D : PowerSeries (ModelRing D)))) := by
          rw [map_mul (PowerSeries.map Ψ), hseries, e2, map_mul (PowerSeries.map f)]
      _ = f (MvPolynomial.X (Sum.inl (some (Sum.inr ⟨i, hc⟩)))) := by
          rw [PowerSeries.coeff_map, h4]
  have hcomp : Ψ.comp (toField D : ModelRing D →+* CohField) = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have : ((Ψ.comp (toField D : ModelRing D →+* CohField)).comp MvPolynomial.C) =
          f.comp MvPolynomial.C := RingHom.ext_rat _ _
      exact congrArg (fun g => g r) this
    · intro w
      rw [RingHom.comp_apply, toField_ringHom_apply, toField_X]
      rcases w with (_ | j | i) | k
      · change Ψ (cohLetters 0) = f (MvPolynomial.X (Sum.inl none))
        rw [hΨletter, mLetter_zero]
      · change Ψ (coframeVec D j) = f (yG j)
        exact congrFun hv j
      · exact hnum i
      · change Ψ (cohLetters k.1) = f (MvPolynomial.X (Sum.inr k))
        rw [hΨletter, mLetter_of_ge D k.2]
  intro a b hab
  apply hf
  rw [← hcomp]
  change Ψ (toField D a) = Ψ (toField D b)
  rw [hab]

section Generation

/-- The subalgebra generated by the atlas variables of the model ring. -/
noncomputable def atlasSub : Subalgebra ℚ (ModelRing D) :=
  Algebra.adjoin ℚ (Set.range fun w : AtlasIdx D => (MvPolynomial.X (Sum.inl w) : ModelRing D))

theorem coeff_mul_mem {A : Subalgebra ℚ (ModelRing D)} {φ ψ : PowerSeries (ModelRing D)}
    (hφ : ∀ k, PowerSeries.coeff k φ ∈ A) (hψ : ∀ k, PowerSeries.coeff k ψ ∈ A) (k : ℕ) :
    PowerSeries.coeff k (φ * ψ) ∈ A := by
  rw [PowerSeries.coeff_mul]
  exact Subalgebra.sum_mem _ fun p _ => A.mul_mem (hφ _) (hψ _)

theorem coeff_invOfUnit_mem {A : Subalgebra ℚ (ModelRing D)} {φ : PowerSeries (ModelRing D)}
    (hφ : ∀ k, PowerSeries.coeff k φ ∈ A) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit φ 1) ∈ A := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hk
    · simp [A.one_mem]
    · refine A.mul_mem (by simp) (Subalgebra.sum_mem _ fun p hp => ?_)
      split_ifs with h
      · refine A.mul_mem (hφ _) (ih _ h)
      · exact A.zero_mem

theorem mG_coeff_mem (k : ℕ) : PowerSeries.coeff k (mG D : PowerSeries (ModelRing D)) ∈
    atlasSub D := by
  rw [Polynomial.coeff_coe, mG, uniPoly_coeff]
  refine Subalgebra.add_mem _ (by split_ifs <;> simp)
    (Subalgebra.sum_mem _ fun j _ => ?_)
  split_ifs
  · exact Algebra.subset_adjoin ⟨some (Sum.inl j), rfl⟩
  · exact Subalgebra.zero_mem _

theorem mP_coeff_mem (k : ℕ) : PowerSeries.coeff k (mP D : PowerSeries (ModelRing D)) ∈
    atlasSub D := by
  rw [Polynomial.coeff_coe, mP_coeff]
  split_ifs with h
  · unfold mNum
    split_ifs with h0 h1
    · exact Algebra.subset_adjoin ⟨none, rfl⟩
    · exact Algebra.subset_adjoin ⟨some (Sum.inr ⟨k, h1⟩), rfl⟩
    · exact Subalgebra.zero_mem _
  · exact Subalgebra.zero_mem _

theorem mLetter_mem {k : ℕ} (hk : k < span D) : mLetter D k ∈ atlasSub D := by
  rw [mLetter_of_lt D hk]
  exact coeff_mul_mem D (mP_coeff_mem D) (coeff_invOfUnit_mem D (mG_coeff_mem D)) k

/-- Each letter below the span is a polynomial in the atlas coordinates. -/
theorem letter_mem_adjoin (hT : (properMatrixOf cohLetters D).det ≠ 0) {j : ℕ}
    (hj : j < span D) : cohLetters j ∈ Algebra.adjoin ℚ (Set.range (atlasCoords D)) := by
  rw [← toField_mLetter D hT j]
  have h1 : toField D (mLetter D j) ∈ (atlasSub D).map (toField D) := ⟨_, mLetter_mem D hj, rfl⟩
  unfold atlasSub at h1
  rw [AlgHom.map_adjoin] at h1
  convert h1 using 2
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, ⟨w, rfl⟩, by rw [toField_X]; rfl⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, by rw [toField_X]; rfl⟩

end Generation

end SkewCoframeRigidity.Coframe
