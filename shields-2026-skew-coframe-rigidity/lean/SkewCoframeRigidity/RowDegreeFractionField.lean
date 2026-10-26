/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.RowDegreeCoherent
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Row degree: irreducibility over the fraction field `ℚ(ϑ)`

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:row-degree`: the coherent
homogenization, read as a polynomial in the positive letters `H₁, H₂, …` over `ℚ[ϑ]`, is
primitive, irreducible over `ℚ(ϑ)`, and relatively prime to its proper corner there.

The first part is Gauss's lemma for `MvPolynomial σ R` with `R` factorial and `K = Frac R`
(`irreducible_map_of_primitive`, `dvd_of_map_dvd_map`).  The second identifies the coherent ring
`ℚ[ϑ, H₁, H₂, …]` with `MvPolynomial ℕ+ ℚ[ϑ]` (`cohEquiv`) and transports the results of
`RowDegreeCoherent`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence MvPolynomial

section Gauss

variable {σ R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

private theorem map_injective' :
    Function.Injective (map (algebraMap R K) : MvPolynomial σ R → MvPolynomial σ K) :=
  MvPolynomial.map_injective _ (IsFractionRing.injective R K)

/-- Clearing denominators: every element of `K[σ]` times a nonzero constant of `R` comes from
`R[σ]`. -/
private theorem exists_clear (z : MvPolynomial σ K) :
    ∃ (s : R) (x : MvPolynomial σ R), s ≠ 0 ∧
      z * C (algebraMap R K s) = map (algebraMap R K) x := by
  letI : Algebra (MvPolynomial σ R) (MvPolynomial σ K) := MvPolynomial.algebraMvPolynomial
  haveI : IsLocalization ((nonZeroDivisors R).map (C (σ := σ))) (MvPolynomial σ K) :=
    MvPolynomial.isLocalization (nonZeroDivisors R) K
  obtain ⟨⟨x, m⟩, h⟩ := IsLocalization.surj ((nonZeroDivisors R).map (C (σ := σ))) z
  obtain ⟨s, hs, hsm⟩ := Submonoid.mem_map.mp m.2
  refine ⟨s, x, nonZeroDivisors.ne_zero hs, ?_⟩
  have h1 : (algebraMap (MvPolynomial σ R) (MvPolynomial σ K)) x = map (algebraMap R K) x := rfl
  have h2 : (algebraMap (MvPolynomial σ R) (MvPolynomial σ K)) (m : MvPolynomial σ R) =
      C (algebraMap R K s) := by
    rw [← hsm]; exact (map_C _ _)
  rw [← h2, ← h1]
  exact h

private theorem isUnit_C_map {s : R} (hs : s ≠ 0) :
    IsUnit (C (algebraMap R K s) : MvPolynomial σ K) := by
  refine (isUnit_iff_ne_zero.2 ?_).map C
  exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hs

/-- A prime of `R[σ]` that is primitive over `R` divides no nonzero constant. -/
private theorem not_dvd_C {f : MvPolynomial σ R} (hf : Prime f)
    (hprim : ∀ r : R, C r ∣ f → IsUnit r) : ∀ s : R, s ≠ 0 → ¬ f ∣ C s := by
  intro s
  refine UniqueFactorizationMonoid.induction_on_prime s (fun h => absurd rfl h) ?_ ?_
  · intro u hu _ hd
    exact hf.not_isUnit (isUnit_of_dvd_unit hd (hu.map C))
  · intro a p ha hp ih _ hd
    rw [map_mul] at hd
    rcases hf.dvd_or_dvd hd with h | h
    · have hpr : Irreducible (C p : MvPolynomial σ R) :=
        ((prime_C_iff (σ := σ)).2 hp).irreducible
      obtain ⟨g, hg⟩ := h
      rcases hpr.isUnit_or_isUnit hg with h' | h'
      · exact hf.not_isUnit h'
      · exact hp.not_isUnit (hprim p ⟨(↑h'.unit⁻¹ : MvPolynomial σ R), by
          calc f = f * (g * ↑h'.unit⁻¹) := by simp
            _ = C p * ↑h'.unit⁻¹ := by rw [← mul_assoc, ← hg]
            ⟩)
    · exact ih ha h

/-- Gauss: an irreducible `f ∈ R[σ]` that is primitive over `R` stays irreducible over
`K = Frac R`. -/
theorem irreducible_map_of_primitive {f : MvPolynomial σ R} (hf : Irreducible f)
    (hprim : ∀ r : R, C r ∣ f → IsUnit r) :
    Irreducible (map (algebraMap R K) f) := by
  have hfp : Prime f := hf.prime
  have hnd := not_dvd_C hfp hprim
  have hmapC : ∀ s : R, (map (algebraMap R K) (C s : MvPolynomial σ R)) =
      C (algebraMap R K s) := fun s => map_C _ _
  refine ⟨?_, fun a b hab => ?_⟩
  · intro hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    obtain ⟨s, x, hs, hx⟩ := exists_clear (σ := σ) (R := R) K z
    have : f * x = C s := by
      apply map_injective' (σ := σ) (R := R) K
      rw [map_mul, ← hx, hmapC, ← mul_assoc, hz, one_mul]
    exact hnd s hs ⟨x, this.symm⟩
  · obtain ⟨s, x, hs, hx⟩ := exists_clear (σ := σ) (R := R) K a
    obtain ⟨t, y, ht, hy⟩ := exists_clear (σ := σ) (R := R) K b
    have key : C (s * t) * f = x * y := by
      apply map_injective' (σ := σ) (R := R) K
      simp only [map_mul, map_C]
      rw [hab, ← hx, ← hy]
      ring
    have main : ∀ r : R, r ≠ 0 → ∀ x y : MvPolynomial σ R, C r * f = x * y →
        IsUnit (map (algebraMap R K) x) ∨ IsUnit (map (algebraMap R K) y) := by
      intro r
      refine UniqueFactorizationMonoid.induction_on_prime r (fun h => absurd rfl h) ?_ ?_
      · intro u hu _ x y h
        obtain ⟨v, rfl⟩ := hu
        have e : f = (C (↑v⁻¹ : R) * x) * y := by
          calc f = C (↑v⁻¹ : R) * (C (↑v : R) * f) := by
                rw [← mul_assoc, ← map_mul]; simp
            _ = _ := by rw [h]; ring
        rcases hf.isUnit_or_isUnit e with h1 | h1
        · left
          exact (isUnit_of_mul_isUnit_right h1).map _
        · right; exact h1.map _
      · intro r' p hr' hp ih _ x y h
        have hCp : Prime (C p : MvPolynomial σ R) := (prime_C_iff (σ := σ)).2 hp
        have hd : C p ∣ x * y := ⟨C r' * f, by rw [← h, map_mul]; ring⟩
        have hpK : IsUnit (map (algebraMap R K) (C p : MvPolynomial σ R)) := by
          rw [hmapC]; exact isUnit_C_map K hp.ne_zero
        rcases hCp.dvd_or_dvd hd with ⟨x', hx'⟩ | ⟨y', hy'⟩
        · have : C r' * f = x' * y := by
            apply mul_left_cancel₀ hCp.ne_zero
            rw [map_mul] at h
            rw [hx'] at h; linear_combination h
          rcases ih hr' x' y this with h1 | h1
          · left; rw [hx', map_mul]; exact hpK.mul h1
          · exact Or.inr h1
        · have : C r' * f = x * y' := by
            apply mul_left_cancel₀ hCp.ne_zero
            rw [map_mul] at h
            rw [hy'] at h; linear_combination h
          rcases ih hr' x y' this with h1 | h1
          · exact Or.inl h1
          · right; rw [hy', map_mul]; exact hpK.mul h1
    have hst : s * t ≠ 0 := mul_ne_zero hs ht
    rcases main (s * t) hst x y key with h | h
    · left
      rw [← hx] at h
      exact isUnit_of_mul_isUnit_left h
    · right
      rw [← hy] at h
      exact isUnit_of_mul_isUnit_left h

/-- Over the fraction field, divisibility of images descends to `R[σ]`. -/
theorem dvd_of_map_dvd_map {f g : MvPolynomial σ R} (hf : Irreducible f)
    (hprim : ∀ r : R, C r ∣ f → IsUnit r)
    (h : map (algebraMap R K) f ∣ map (algebraMap R K) g) : f ∣ g := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨s, x, hs, hx⟩ := exists_clear (σ := σ) (R := R) K z
  have : C s * g = f * x := by
    apply map_injective' (σ := σ) (R := R) K
    rw [map_mul, map_mul, map_C, ← hx, hz]
    ring
  have hfp : Prime f := hf.prime
  rcases hfp.dvd_or_dvd ⟨x, this⟩ with h1 | h1
  · exact absurd h1 (not_dvd_C hfp hprim s hs)
  · exact h1

end Gauss

section Transport

open scoped Polynomial

/-- The letters indexed from zero are `ϑ` and the positive letters. -/
def letterEquiv : ℕ ≃ Option ℕ+ where
  toFun n := if h : n = 0 then none else some ⟨n, Nat.pos_of_ne_zero h⟩
  invFun o := o.elim 0 (fun k => (k : ℕ))
  left_inv n := by
    by_cases h : n = 0
    · simp [h]
    · simp [h]; rfl
  right_inv o := by
    cases o with
    | none => simp
    | some k => simp [k.ne_zero]; rfl

/-- The coherent ring as polynomials in the positive letters over `ℚ[ϑ]`. -/
noncomputable def cohEquiv : CohRing ≃ₐ[ℚ] MvPolynomial ℕ+ ℚ[X] :=
  (renameEquiv ℚ letterEquiv).trans (optionEquivRight ℚ ℕ+)

theorem cohEquiv_X_zero : cohEquiv (X 0 : CohRing) = C Polynomial.X := by
  simp [cohEquiv, letterEquiv]

theorem cohEquiv_C_poly (q : ℚ[X]) :
    cohEquiv (Polynomial.aeval (X 0 : CohRing) q) = C q := by
  have : (cohEquiv : CohRing →ₐ[ℚ] _).comp (Polynomial.aeval (X 0 : CohRing)) =
      (IsScalarTower.toAlgHom ℚ ℚ[X] (MvPolynomial ℕ+ ℚ[X])) := by
    apply Polynomial.algHom_ext
    simpa using cohEquiv_X_zero
  have h := congrArg (fun F => F q) this
  simpa using h

/-- The coherent homogenization over `ℚ(ϑ)`: `cohSchur D` as a polynomial in the positive
letters with coefficients in `ℚ(ϑ) = FractionRing ℚ[ϑ]`. -/
noncomputable def cohSchurFrac {n : ℕ} (D : BetaDiagram n) :
    MvPolynomial ℕ+ (FractionRing ℚ[X]) :=
  map (algebraMap ℚ[X] (FractionRing ℚ[X])) (cohEquiv (cohSchur D))

/-- The coherent proper corner over `ℚ(ϑ)`. -/
noncomputable def cohCornerFrac {n : ℕ} (D : BetaDiagram (n + 1)) :
    MvPolynomial ℕ+ (FractionRing ℚ[X]) :=
  map (algebraMap ℚ[X] (FractionRing ℚ[X])) (cohEquiv (cohCorner D))

/-- A connected coherent homogenization is primitive over `ℚ[ϑ]`: a constant dividing it is a
unit (`sc:row-degree`). -/
theorem cohSchur_primitive {n : ℕ} (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    ∀ r : ℚ[X], C r ∣ cohEquiv (cohSchur D) → IsUnit r := by
  intro r ⟨g, hg⟩
  have hirr : Irreducible (cohEquiv (cohSchur D)) :=
    (MulEquiv.irreducible_iff (cohEquiv : CohRing ≃ₐ[ℚ] _).toMulEquiv).2
      (cohSchur_irreducible D hD)
  rcases hirr.isUnit_or_isUnit hg with h | h
  · simpa using h.map (MvPolynomial.constantCoeff (σ := ℕ+) (R := ℚ[X]))
  · exfalso
    obtain ⟨c, _, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 h
    have e : cohSchur D = Polynomial.aeval (X 0 : CohRing) (r * c) := by
      apply cohEquiv.injective
      rw [cohEquiv_C_poly, hg, hc, map_mul]
    have h1 : physSpec (cohSchur D) = physInclude D.schur := physSpec_schurOf D
    have h2 : physSpec (Polynomial.aeval (X 0 : CohRing) (r * c)) =
        C ((r * c).eval 1) := by
      have hh : (physSpec : CohRing →ₐ[ℚ] CohRing).comp (Polynomial.aeval (X 0 : CohRing)) =
          Polynomial.aeval (1 : CohRing) := by
        apply Polynomial.algHom_ext
        simp [physSpec]
      have h3 := congrArg (fun F => F (r * c)) hh
      simp only [AlgHom.comp_apply] at h3
      rw [h3, show (1 : CohRing) = algebraMap ℚ CohRing 1 by simp,
        Polynomial.aeval_algebraMap_apply]
      simp
    have h4 := totalDegree_le_physInclude D.schur
    have h5 : D.schur.totalDegree = n + 1 := BetaDiagram.rowDegree D
    rw [e, h2] at h1
    rw [← h1, totalDegree_C] at h4
    omega

/-- A connected coherent homogenization is irreducible over `ℚ(ϑ)`, as a polynomial in the
positive letters (`sc:row-degree`). -/
theorem cohSchurFrac_irreducible {n : ℕ} (D : BetaDiagram (n + 1)) (hD : D.Connected) :
    Irreducible (cohSchurFrac D) :=
  irreducible_map_of_primitive (FractionRing ℚ[X])
    ((MulEquiv.irreducible_iff (cohEquiv : CohRing ≃ₐ[ℚ] _).toMulEquiv).2
      (cohSchur_irreducible D hD)) (cohSchur_primitive D hD)

/-- The coherent homogenization of a connected diagram is relatively prime to its proper
corner over `ℚ(ϑ)` (`sc:row-degree`). -/
theorem cohSchurFrac_isRelPrime_cohCornerFrac {n : ℕ} (D : BetaDiagram (n + 1))
    (hD : D.Connected) : IsRelPrime (cohSchurFrac D) (cohCornerFrac D) := by
  refine (cohSchurFrac_irreducible D hD).isRelPrime_iff_not_dvd.2 fun h => ?_
  have hirr : Irreducible (cohEquiv (cohSchur D)) :=
    (MulEquiv.irreducible_iff (cohEquiv : CohRing ≃ₐ[ℚ] _).toMulEquiv).2
      (cohSchur_irreducible D hD)
  have h1 := dvd_of_map_dvd_map (FractionRing ℚ[X]) hirr (cohSchur_primitive D hD) h
  obtain ⟨q, hq⟩ := h1
  have h2 : cohSchur D ∣ cohCorner D := ⟨cohEquiv.symm q, by
    apply cohEquiv.injective
    rw [map_mul]; simpa using hq⟩
  exact (cohSchur_irreducible D hD).not_isUnit
    ((cohSchur_isRelPrime_cohCorner D hD) dvd_rfl h2)

end Transport

end SkewCoframeRigidity.Coframe
