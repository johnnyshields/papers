/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/Homogenization.lean
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Common
import Mathlib.Tactic.FieldSimp
import SkewMarkedFactor.Gluing.SchurFunction

/-!
# Homogenization of `Λ` by a unit variable

Formalizes `shields-2026-skew-gluing.tex`, «Local common-factor gluing» (`sec:gluing`),
the proof of `lem:gluing-row-transport`: the substitution on `Λ` is understood after
homogenizing with an independent unit variable `h̃₀`, and specializing `h̃₀ = 1` loses no
information at fixed homogeneous degree.

The homogenized ring is `HomLambda = ℚ[h̃₀, h̃₁, h̃₂, …]` (`MvPolynomial ℕ ℚ`), with `h̃_j = 0` for
`j < 0` (`hTilde`).  The specialization `h̃₀ ↦ 1` is `dehom`.  This file proves that `dehom` is
injective on the homogeneous polynomials of any one degree (`dehom_injOn_isHomogeneous`) and that
the homogenized Jacobi--Trudi determinant of a profile with `n + 1` rows is homogeneous of degree
`n + 1` and specializes to its skew Schur function (`Profile.schurHom`).

Sorry-free.
-/

namespace SkewMarkedFactor.Gluing

open MvPolynomial

/-- The ring `ℚ[h̃₀, h̃₁, h̃₂, …]` obtained from `Λ` by adjoining the unit variable `h̃₀`. -/
abbrev HomLambda : Type := MvPolynomial ℕ ℚ

/-- The homogenized complete function `h̃_j`: the variable `h̃_j` for `j ≥ 0`, and zero for
`j < 0`. -/
noncomputable def hTilde (j : ℤ) : HomLambda := if j < 0 then 0 else X j.toNat

/-- The specialization `h̃₀ ↦ 1`, `h̃_j ↦ h_j`, from `HomLambda` to `Λ`. -/
noncomputable def dehom : HomLambda →ₐ[ℚ] Lambda := aeval fun k : ℕ => hPos k

theorem dehom_hTilde (j : ℤ) : dehom (hTilde j) = hh j := by
  unfold hTilde hh
  split_ifs with h
  · simp
  · simp [dehom, hPos]

theorem isHomogeneous_hTilde (j : ℤ) : (hTilde j).IsHomogeneous 1 := by
  unfold hTilde
  split_ifs
  · exact isHomogeneous_zero _ _ _
  · exact isHomogeneous_X _ _

/-- The monomial-by-monomial form of the specialization: evaluating a monomial `m` of degree `d`
at `x` is `x₀ ^ d` times evaluating its specialization at `x_k / x₀`. -/
theorem eval_monomial_eq_pow_mul_eval_dehom (x : ℕ → ℚ) (hx : x 0 ≠ 0) (m : ℕ →₀ ℕ) (c : ℚ) :
    eval x (monomial m c)
      = x 0 ^ m.degree * eval (fun k : ℕ+ => x k / x 0) (dehom (monomial m c)) := by
  have hev : ∀ j : ℕ, eval (fun k : ℕ+ => x k / x 0) (hPos j) = x j / x 0 := by
    intro j
    by_cases hj : 0 < j
    · have h := hPos_pnat ⟨j, hj⟩
      simp only [PNat.mk_coe] at h
      rw [h]
      exact eval_X (⟨j, hj⟩ : ℕ+)
    · obtain rfl : j = 0 := by omega
      simp [hPos, hx]
  rw [dehom, aeval_monomial, eval_monomial, map_mul, map_finsuppProd]
  simp only [map_pow, hev, eval_C, algebraMap_eq]
  rw [Finsupp.prod, Finsupp.prod]
  simp only [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  field_simp

/-- **`dehom` is injective on the homogeneous polynomials of one degree.** -/
theorem dehom_injOn_isHomogeneous {N : ℕ} {p q : HomLambda} (hp : p.IsHomogeneous N)
    (hq : q.IsHomogeneous N) (h : dehom p = dehom q) : p = q := by
  have hr : (p - q).IsHomogeneous N := hp.sub hq
  have hd : dehom (p - q) = 0 := by rw [map_sub, h, sub_self]
  suffices hz : p - q = 0 from sub_eq_zero.mp hz
  set r := p - q with hrdef
  have key : ∀ x : ℕ → ℚ, eval x (X 0 * r) = eval x 0 := by
    intro x
    by_cases hx : x 0 = 0
    · simp [hx]
    · have hrx : eval x r = 0 := by
        conv_lhs => rw [r.as_sum]
        rw [map_sum]
        have : ∀ m ∈ r.support, eval x (monomial m (r.coeff m))
            = x 0 ^ N * eval (fun k : ℕ+ => x k / x 0) (dehom (monomial m (r.coeff m))) := by
          intro m hm
          rw [eval_monomial_eq_pow_mul_eval_dehom x hx]
          have hdeg : m.degree = N := by
            have := hr (mem_support_iff.mp hm)
            rwa [Finsupp.degree_eq_weight_one]
          rw [hdeg]
        rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← map_sum, ← map_sum, ← r.as_sum, hd]
        simp
      simp [hrx]
  have := MvPolynomial.funext key
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (X_ne_zero 0)
  · exact h0

namespace Profile

variable {n : ℕ}

/-- The homogenized Jacobi--Trudi determinant `det (h̃_{ξ_i - ζ_j})` of a profile. -/
noncomputable def schurHom (P : Profile n) : HomLambda :=
  (Matrix.of fun i j : Fin (n + 1) => hTilde (P.xi i - P.zeta j)).det

/-- Specializing `h̃₀ = 1` in `schurHom` gives `schur`. -/
theorem dehom_schurHom (P : Profile n) : dehom P.schurHom = P.schur := by
  rw [schurHom, schur, AlgHom.map_det]
  congr 1
  ext i j
  simp [dehom_hTilde]

/-- The homogenized determinant of a profile with `n + 1` rows is homogeneous of degree
`n + 1`. -/
theorem isHomogeneous_schurHom (P : Profile n) : P.schurHom.IsHomogeneous (n + 1) := by
  rw [schurHom, Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : HomLambda)).IsHomogeneous 0 := by
    rw [show ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : HomLambda)) =
      C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) by simp]
    exact isHomogeneous_C _ _
  have h2 : (∏ i : Fin (n + 1), (Matrix.of fun i j : Fin (n + 1) =>
      hTilde (P.xi i - P.zeta j)) (σ i) i).IsHomogeneous (n + 1) := by
    have := IsHomogeneous.prod Finset.univ
      (fun i : Fin (n + 1) => (Matrix.of fun i j : Fin (n + 1) =>
        hTilde (P.xi i - P.zeta j)) (σ i) i) (fun _ => 1) (fun i _ => isHomogeneous_hTilde _)
    simpa using this
  simpa using h1.mul h2

/-- Two profiles with the same number of rows have the same skew Schur function exactly when
they have the same homogenized one. -/
theorem schur_eq_iff_schurHom_eq (P Q : Profile n) : P.schur = Q.schur ↔ P.schurHom = Q.schurHom :=
  ⟨fun h => dehom_injOn_isHomogeneous P.isHomogeneous_schurHom Q.isHomogeneous_schurHom
      (by rw [dehom_schurHom, dehom_schurHom, h]),
    fun h => by rw [← dehom_schurHom, ← dehom_schurHom, h]⟩

end Profile

end SkewMarkedFactor.Gluing
