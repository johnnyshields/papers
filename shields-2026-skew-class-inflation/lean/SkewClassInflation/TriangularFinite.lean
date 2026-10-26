/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.TriangularDegree
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Finite triangular polynomial substitutions

The finite induction in `lem:triangular-substitution` of
`shields-2026-skew-class-inflation.tex`.  The newest polynomial has
variable degree one at its pivot; all older polynomials have degree
zero there.  Mapping the coefficients preserves their nonvanishing,
and the new-variable degree lemma closes the induction in arbitrary
characteristic.  Sorry-free.
-/

namespace SkewClassInflation

open MvPolynomial

/-- A substitution whose values avoid a variable cannot create that variable. -/
theorem degreeOf_aeval_zero {ι σ K : Type*} [CommRing K]
    (B : ι → MvPolynomial σ K) (x : σ) (hB : ∀ i, (B i).degreeOf x = 0)
    (p : MvPolynomial ι K) : (aeval B p).degreeOf x = 0 := by
  classical
  by_contra hn
  have hx : x ∈ (aeval B p).vars := mem_vars_iff_degreeOf_ne_zero.mpr hn
  change x ∈ (bind₁ B p).vars at hx
  obtain ⟨i, _, hi⟩ := mem_vars_bind₁ B p hx
  exact (mem_vars_iff_degreeOf_ne_zero.mp hi) (hB i)

/-- Splitting the first variable is polynomial evaluation after mapping the old coefficients. -/
theorem aeval_fin_split {n : ℕ} {σ K : Type*} [CommRing K]
    (B : Fin (n + 1) → MvPolynomial σ K) (p : MvPolynomial (Fin (n + 1)) K) :
    aeval B p =
      (Polynomial.map (aeval (fun i : Fin n => B i.succ)).toRingHom
        (finSuccEquiv K n p)).eval (B 0) := by
  let E := finSuccEquiv K n
  let old : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial σ K :=
    aeval (fun i : Fin n => B i.succ)
  let e : Polynomial (MvPolynomial σ K) →ₐ[K] MvPolynomial σ K :=
    { Polynomial.evalRingHom (B 0) with commutes' := by intro a; simp }
  have hcomp : aeval B = e.comp ((Polynomial.mapAlgHom old).comp E.toAlgHom) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, E,
        finSuccEquiv_X_zero, Polynomial.coe_mapAlgHom, Polynomial.map_X]
      change B 0 = Polynomial.eval (B 0) Polynomial.X
      simp
    · simp only [aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, E,
        finSuccEquiv_X_succ, Polynomial.coe_mapAlgHom, Polynomial.map_C, old]
      change B j.succ = Polynomial.eval (B 0) (Polynomial.C (old (X j)))
      have hx : old (X j) = B j.succ := aeval_X _ _
      rw [hx, Polynomial.eval_C]
  exact DFunLike.congr_fun hcomp p

/-- Every nonzero polynomial stays nonzero under a finite triangular substitution. -/
theorem triangular_finite_nonzero {σ K : Type*} [CommRing K] [IsDomain K]
    (n : ℕ) (B : Fin n → MvPolynomial σ K) (N : Fin n → σ)
    (hdiag : ∀ i, (B i).degreeOf (N i) = 1)
    (hoff : ∀ i j, i < j → (B j).degreeOf (N i) = 0)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) : aeval B p ≠ 0 := by
  classical
  induction n with
  | zero =>
    have hc : p.coeff 0 ≠ 0 := by
      intro he
      apply hp
      rw [p.eq_C_of_isEmpty, he, C_0]
    rw [p.eq_C_of_isEmpty, aeval_C]
    exact C_ne_zero.mpr hc
  | succ n ih =>
    let old : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial σ K :=
      aeval (fun i : Fin n => B i.succ)
    let P := finSuccEquiv K n p
    let Q := P.map old.toRingHom
    have hP : P ≠ 0 := by
      intro he
      apply hp
      exact (finSuccEquiv K n).injective (he.trans (map_zero _).symm)
    have hold (q : MvPolynomial (Fin n) K) (hq : q ≠ 0) : old q ≠ 0 :=
      ih (fun i => B i.succ) (fun i => N i.succ) (fun i => hdiag i.succ)
        (fun i j hij => hoff i.succ j.succ (by simpa only [Fin.succ_lt_succ_iff] using hij)) q hq
    have hQ : Q ≠ 0 := by
      intro he
      have hc := congrArg (fun q : Polynomial (MvPolynomial σ K) => q.coeff P.natDegree) he
      dsimp only [Q] at hc
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
      exact hold (P.coeff P.natDegree) (Polynomial.leadingCoeff_ne_zero.mpr hP) hc
    have hcoeff (i : ℕ) : (Q.coeff i).degreeOf (N 0) = 0 := by
      dsimp only [Q]
      rw [Polynomial.coeff_map]
      apply degreeOf_aeval_zero
      intro j
      exact hoff 0 j.succ (by simp)
    rw [aeval_fin_split]
    exact eval_ne_zero_of_new_variable (N 0) (B 0) (hdiag 0) Q hQ hcoeff

/-- Finite triangular families induce an injective algebra homomorphism. -/
theorem triangular_finite_injective {σ K : Type*} [CommRing K] [IsDomain K]
    (n : ℕ) (B : Fin n → MvPolynomial σ K) (N : Fin n → σ)
    (hdiag : ∀ i, (B i).degreeOf (N i) = 1)
    (hoff : ∀ i j, i < j → (B j).degreeOf (N i) = 0) :
    Function.Injective (aeval B : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial σ K) := by
  apply (injective_iff_map_eq_zero (aeval B).toRingHom).mpr
  intro p hp
  by_contra hn
  exact triangular_finite_nonzero n B N hdiag hoff p hn hp

end SkewClassInflation
