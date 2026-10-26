/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.TriangularFinite
import Mathlib.Data.PNat.Basic

/-!
# Injective triangular substitutions in infinitely many variables

Formalizes `lem:triangular-substitution` in
`shields-2026-skew-class-inflation.tex`.  Every relation uses finitely
many source variables, which are reordered with the newest pivot first.
The coefficient domain may be any integral domain, not only a field;
no characteristic-zero hypothesis or unit leading coefficient is used.
Sorry-free.
-/

namespace SkewClassInflation

open MvPolynomial

/-- Infinite triangular families are injective since each relation uses finitely many variables. -/
theorem triangular_nat_injective {σ K : Type*} [CommRing K] [IsDomain K]
    (B : ℕ → MvPolynomial σ K) (N : ℕ → σ)
    (hdiag : ∀ i, (B i).degreeOf (N i) = 1)
    (hoff : ∀ i j, i < j → (B i).degreeOf (N j) = 0) :
    Function.Injective (aeval B : MvPolynomial ℕ K →ₐ[K] MvPolynomial σ K) := by
  classical
  apply (injective_iff_map_eq_zero (aeval B).toRingHom).mpr
  intro p hp
  by_contra hn
  let n := p.vars.sup (fun k => k) + 1
  let φ : Fin n → ℕ := fun i => i.rev.val
  have hφ : Function.Injective φ := by
    intro i j he
    have hh : i.rev = j.rev := Fin.ext he
    have hrev := congrArg Fin.rev hh
    simpa only [Fin.rev_rev] using hrev
  have hbound : (↑p.vars : Set ℕ) ⊆ Set.range φ := by
    intro k hk
    have hkn : k < n := by
      have hh := Finset.le_sup (f := fun k : ℕ => k) hk
      dsimp [n]
      omega
    exact ⟨(⟨k, hkn⟩ : Fin n).rev, by simp only [φ, Fin.rev_rev]⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range p φ hφ hbound
  have hq0 : q ≠ 0 := by
    intro he
    apply hn
    rw [← hq, he, map_zero]
  have hfin : aeval (B ∘ φ) q ≠ 0 := by
    apply triangular_finite_nonzero n (B ∘ φ) (N ∘ φ) (fun i => hdiag (φ i))
    · intro i j hij
      have hlt : φ j < φ i := by
        dsimp [φ]
        have hi := i.isLt
        have hj := j.isLt
        change i.val < j.val at hij
        omega
      exact hoff (φ j) (φ i) hlt
    · exact hq0
  apply hfin
  rw [← aeval_rename, hq]
  exact hp

/-- Positive generator indices have the same triangular injectivity criterion. -/
theorem triangular_pnat_injective {σ K : Type*} [CommRing K] [IsDomain K]
    (B : ℕ+ → MvPolynomial σ K) (N : ℕ+ → σ)
    (hdiag : ∀ i, (B i).degreeOf (N i) = 1)
    (hoff : ∀ i j, i < j → (B i).degreeOf (N j) = 0) :
    Function.Injective (aeval B : MvPolynomial ℕ+ K →ₐ[K] MvPolynomial σ K) := by
  let e : ℕ ≃o ℕ+ := OrderIso.pnatIsoNat.symm
  have hi := triangular_nat_injective (fun i => B (e i)) (fun i => N (e i))
    (fun i => hdiag (e i)) (fun i j hij => hoff (e i) (e j) (e.strictMono hij))
  intro p q hpq
  apply MvPolynomial.rename_injective e.symm e.symm.injective
  apply hi
  simpa only [aeval_rename, Function.comp_def, OrderIso.apply_symm_apply] using hpq

/-- A variable absent from the strict support bound has degree zero. -/
theorem degreeOf_zero_of_vars_lt {σ K : Type*} [Preorder σ] [CommRing K]
    (p : MvPolynomial σ K) (x : σ) (h : ∀ j ∈ p.vars, j < x) : p.degreeOf x = 0 := by
  by_contra hn
  have hm : x ∈ p.vars := mem_vars_iff_degreeOf_ne_zero.mpr hn
  exact (lt_irrefl x) (h x hm)

/-- Nonzero lower-variable coefficients and linear pivots give an injective substitution. -/
theorem triangular_substitution_injective {K : Type*} [CommRing K] [IsDomain K]
    (N : ℕ → ℕ) (hN : StrictMono N) (c d : ℕ → MvPolynomial ℕ K)
    (hc : ∀ i, c i ≠ 0)
    (hcv : ∀ i j, j ∈ (c i).vars → j < N i)
    (hdv : ∀ i j, j ∈ (d i).vars → j < N i) :
    Function.Injective (aeval (fun i => c i * X (N i) + d i) :
      MvPolynomial ℕ K →ₐ[K] MvPolynomial ℕ K) := by
  classical
  apply triangular_nat_injective (fun i => c i * X (N i) + d i) N
  · intro i
    have hci := degreeOf_zero_of_vars_lt (c i) (N i) (hcv i)
    have hdi := degreeOf_zero_of_vars_lt (d i) (N i) (hdv i)
    have hprod : (c i * X (N i)).degreeOf (N i) = 1 := by
      rw [degreeOf_mul_eq (hc i) (X_ne_zero _), hci, degreeOf_X_self, zero_add]
    rw [degreeOf_add_eq_of_degreeOf_lt (by rw [hdi, hprod]; decide), hprod]
  · intro i j hij
    have hci := degreeOf_zero_of_vars_lt (c i) (N j)
      (fun k hk => (hcv i k hk).trans (hN hij))
    have hdi := degreeOf_zero_of_vars_lt (d i) (N j)
      (fun k hk => (hdv i k hk).trans (hN hij))
    have hX : (X (N i) : MvPolynomial ℕ K).degreeOf (N j) = 0 := by
      rw [degreeOf_X, ite_eq_right (ne_of_gt (hN hij))]
    have hm := degreeOf_mul_le (N j) (c i) (X (N i))
    rw [hci, hX, zero_add] at hm
    have ha := degreeOf_add_le (N j) (c i * X (N i)) (d i)
    rw [hdi] at ha
    omega

end SkewClassInflation
