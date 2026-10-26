/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseContent

/-!
# Uniqueness of staircase monomial content

The uniqueness clause of `lem:staircase-content` in
`shields-2026-skew-jacobi-negative.tex`.  Alternative factors are actual
polynomials, and their monomial exponent may be any finitely supported
function on the complete generators.
-/

namespace SkewJacobiNegative.Staircase

open Gluing

set_option backward.isDefEq.respectTransparency false

/-- An internal-gap monomial cannot contain the private full-interval variable. -/
theorem full_not_mem_gap_supported_monomial {n : ℕ} (P : Profile n)
    (e : ℕ+ →₀ ℕ)
    (he : ∀ v ∈ e.support, ∃ j : Fin n, P.g j = v.val) :
    fullGenerator P ∉ (MvPolynomial.monomial e (1 : ℚ)).vars := by
  classical
  rw [MvPolynomial.vars_monomial (by norm_num : (1 : ℚ) ≠ 0)]
  intro hv
  obtain ⟨j, hj⟩ := he (fullGenerator P) hv
  have hlt := index_lt_full P j.succ j.castSucc (Or.inl (Fin.succ_ne_zero j))
  rw [P.xi_succ_sub_zeta_castSucc] at hlt
  have heq : (P.g j : ℤ) = fullIndex P := by
    calc
      (P.g j : ℤ) = ((fullGenerator P).val : ℤ) := congrArg (fun k : ℕ => (k : ℤ)) hj
      _ = fullIndex P := fullGenerator_int_coe P
  exact (ne_of_lt hlt) heq

/-- The full-interval primitive does not divide any monomial supported on
actual internal gaps. -/
theorem canonical_not_dvd_gap_supported_monomial {n : ℕ} {q : ℕ+}
    {P : Profile n} (hP : QComponent q P) (e : ℕ+ →₀ ℕ)
    (he : ∀ v ∈ e.support, ∃ j : Fin n, P.g j = v.val) :
    ¬ canonicalPrimitive hP ∣ MvPolynomial.monomial e (1 : ℚ) := by
  have hM : (MvPolynomial.monomial e (1 : ℚ) : CompleteRing) ≠ 0 := by
    intro hz
    exact (one_ne_zero : (1 : ℚ) ≠ 0)
      ((MvPolynomial.monomial_eq_zero (s := e) (b := (1 : ℚ))).mp hz)
  intro hd
  have hno := not_mem_vars_of_dvd hM hd (fullGenerator P)
    (full_not_mem_gap_supported_monomial P e he)
  exact hno (full_mem_canonicalPrimitive hP)

/-- The coefficient-one gap content and irreducible factor are unique among
all actual gap-supported monomial factorizations of the restriction. -/
theorem staircase_content_unique {n : ℕ} {q : ℕ+} {P : Profile n}
    (hP : QComponent q P) (e : ℕ+ →₀ ℕ) (L : CompleteRing)
    (he : ∀ v ∈ e.support, ∃ j : Fin n, P.g j = v.val)
    (hL : Irreducible L)
    (hfactor : restriction q P = MvPolynomial.monomial e 1 * L) :
    e = contentExponent hP ∧ L = monicPrimitive hP := by
  classical
  let M : CompleteRing := MvPolynomial.monomial e 1
  have hprime : Prime (canonicalPrimitive hP) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (canonicalPrimitive_irreducible hP)
  have hdiv : canonicalPrimitive hP ∣ M * L := by
    rw [← hfactor]
    exact canonicalPrimitive_dvd_restriction hP
  have hdivL : canonicalPrimitive hP ∣ L :=
    (hprime.dvd_or_dvd hdiv).resolve_left (canonical_not_dvd_gap_supported_monomial hP e he)
  have hcanL : Associated (canonicalPrimitive hP) L :=
    ((canonicalPrimitive_irreducible hP).dvd_irreducible_iff_associated hL).mp hdivL
  have hcanK : Associated (canonicalPrimitive hP) (monicPrimitive hP) :=
    associated_unit_mul_left (monicPrimitive hP) ((-1 : CompleteRing) ^ n)
      (isUnit_neg_one.pow n)
  have hKL : Associated (monicPrimitive hP) L := hcanK.symm.trans hcanL
  have hproduct : Associated (monicContent hP * monicPrimitive hP) (M * L) := by
    apply Associated.of_eq
    exact (restriction_eq_monicContent_mul hP).symm.trans hfactor
  have hGM : Associated (monicContent hP) M :=
    Associated.of_mul_right hproduct hKL (monicPrimitive_irreducible hP).ne_zero
  have hforward : contentExponent hP ≤ e :=
    MvPolynomial.monomial_one_dvd_monomial_one.mp hGM.dvd
  have hbackward : e ≤ contentExponent hP :=
    MvPolynomial.monomial_one_dvd_monomial_one.mp hGM.symm.dvd
  have heq : e = contentExponent hP := le_antisymm hbackward hforward
  have hfactor' : restriction q P = monicContent hP * L := by
    simpa only [heq, monicContent] using hfactor
  have hG : monicContent hP ≠ 0 := by
    change (MvPolynomial.monomial (contentExponent hP) (1 : ℚ) : CompleteRing) ≠ 0
    intro hz
    exact (one_ne_zero : (1 : ℚ) ≠ 0)
      ((MvPolynomial.monomial_eq_zero (s := contentExponent hP) (b := (1 : ℚ))).mp hz)
  have hK : monicPrimitive hP = L :=
    mul_left_cancel₀ hG ((restriction_eq_monicContent_mul hP).symm.trans hfactor')
  exact ⟨heq, hK.symm⟩

end SkewJacobiNegative.Staircase
