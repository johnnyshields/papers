/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# The panel-B coefficient polynomials

For `Q(t) = (1-t)(1-t/2)(1-t/4)`, `r = 1` and `N(t,z) = 1+z+z^2+t(2-z)`, the
coefficient comparison of `cor:panel-B-attractor` turns `N/(Q+zt) = ∑ P_m t^m`
into the three-term recurrence

  `P_m = -(z - 7/4) P_{m-1} - (7/8) P_{m-2} + (1/8) P_{m-3}`,  `P_{-1} = 0`,

from `P_0 = z^2+z+1` and `P_1 = -z^3 + (3/4)z^2 - (1/4)z + 15/4`.  `panelP` is
that sequence and `panelP_natDegree`, `panelP_leadingCoeff` are the corollary's
first assertion: `deg P_m = m+2` and `[z^{m+2}]P_m = (-1)^m`.  The term
`-z P_{m-1}` is inductively the unique one of top degree, which is exactly the
paper's argument.

## Implementation notes

Everything here is exact arithmetic over `ℚ`; the corollary's `P_m` are real
polynomials with rational coefficients, and degree and leading coefficient are
unchanged by the inclusion.  Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`, `cor:panel-B-attractor`).

## Tags

coefficient polynomial, rational generating function, zero attractor
-/

namespace ForgacsTran

open Polynomial

/-- Paper `cor:panel-B-attractor` — the coefficient polynomials `P_m` of
`N/(Q + zt)` for the panel-B data, given by the corollary's own recurrence.  The
`m = 2` clause is the recurrence read with `P_{-1} = 0`. -/
noncomputable def panelP : ℕ → ℚ[X]
  | 0 => X ^ 2 + X + 1
  | 1 => -X ^ 3 + C (3 / 4) * X ^ 2 - C (1 / 4) * X + C (15 / 4)
  | 2 => -(X - C (7 / 4)) * panelP 1 - C (7 / 8) * panelP 0
  | m + 3 =>
      -(X - C (7 / 4)) * panelP (m + 2) - C (7 / 8) * panelP (m + 1)
        + C (1 / 8) * panelP m

/-- Multiplying by `-(X - a)` raises the degree by one and negates the top
coefficient; a correction of degree at most `d` cannot reach `d + 1`. -/
private theorem coeff_top_step {p e : ℚ[X]} {d : ℕ} (hd : p.natDegree = d)
    (hc : p.coeff d ≠ 0) (he : e.natDegree ≤ d) (a : ℚ) :
    (-(X - C a) * p + e).natDegree = d + 1 ∧
      (-(X - C a) * p + e).coeff (d + 1) = -p.coeff d := by
  have hp0 : p ≠ 0 := fun h => hc (by simp [h])
  have hrw : -(X - C a) * p = -(X * p) + C a * p := by ring
  have hlow : p.coeff (d + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have he0 : e.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeff : (-(X - C a) * p + e).coeff (d + 1) = -p.coeff d := by
    rw [coeff_add, he0, hrw]
    simp [coeff_X_mul, hlow]
  refine ⟨le_antisymm ?_ ?_, hcoeff⟩
  · refine (natDegree_add_le _ _).trans (max_le ?_ (by omega))
    have h1 : (-(X - C a)).natDegree = 1 := by
      rw [natDegree_neg]; exact natDegree_X_sub_C _
    have hne : (-(X - C a) : ℚ[X]) ≠ 0 := by
      intro h
      rw [h] at h1
      simp at h1
    rw [natDegree_mul hne hp0, h1, hd]
    omega
  · refine le_natDegree_of_ne_zero ?_
    rw [hcoeff]
    simpa using hc

/-- **Paper `cor:panel-B-attractor`, first assertion.**  `deg P_m = m + 2` and
`[z^{m+2}] P_m = (-1)^m` for every `m ≥ 0`. -/
theorem panelP_natDegree_and_coeff (m : ℕ) :
    (panelP m).natDegree = m + 2 ∧ (panelP m).coeff (m + 2) = (-1) ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
      constructor
      · rw [show panelP 0 = X ^ 2 + X + 1 from rfl]
        compute_degree!
      · rw [show panelP 0 = X ^ 2 + X + 1 from rfl]
        simp [coeff_add, coeff_X_pow, coeff_one, Polynomial.coeff_X]
    | 1 =>
      constructor
      · rw [show panelP 1 = -X ^ 3 + C (3 / 4) * X ^ 2 - C (1 / 4) * X + C (15 / 4) from rfl]
        compute_degree!
      · rw [show panelP 1 = -X ^ 3 + C (3 / 4) * X ^ 2 - C (1 / 4) * X + C (15 / 4) from rfl]
        simp
    | 2 =>
      obtain ⟨hd, hc⟩ := ih 1 (by omega)
      have hne : (panelP 1).coeff 3 ≠ 0 := by rw [hc]; norm_num
      have hlow : (-(C (7 / 8) * panelP 0) : ℚ[X]).natDegree ≤ 3 := by
        have := (ih 0 (by omega)).1
        refine (natDegree_neg _).le.trans ?_
        exact (natDegree_C_mul_le _ _).trans (by omega)
      have key := coeff_top_step (p := panelP 1) (e := -(C (7 / 8) * panelP 0))
        (d := 3) hd hne hlow (7 / 4)
      have hEq : panelP 2 = -(X - C (7 / 4)) * panelP 1 + -(C (7 / 8) * panelP 0) := by
        rw [show panelP 2 = -(X - C (7 / 4)) * panelP 1 - C (7 / 8) * panelP 0 from rfl]
        ring
      rw [hEq]
      refine ⟨key.1, ?_⟩
      rw [key.2, hc]
      norm_num
    | m + 3 =>
      obtain ⟨hd, hc⟩ := ih (m + 2) (by omega)
      have hne : (panelP (m + 2)).coeff (m + 4) ≠ 0 := by
        rw [show m + 4 = m + 2 + 2 by omega, hc]
        exact pow_ne_zero _ (by norm_num)
      set e : ℚ[X] := -(C (7 / 8) * panelP (m + 1)) + C (1 / 8) * panelP m with he
      have hlow : e.natDegree ≤ m + 4 := by
        have h1 := (ih (m + 1) (by omega)).1
        have h2 := (ih m (by omega)).1
        refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_neg _).le.trans ?_
          exact (natDegree_C_mul_le _ _).trans (by omega)
        · exact (natDegree_C_mul_le _ _).trans (by omega)
      have hd' : (panelP (m + 2)).natDegree = m + 4 := by omega
      have key := coeff_top_step (p := panelP (m + 2)) (e := e) (d := m + 4) hd' hne hlow (7 / 4)
      have hEq : panelP (m + 3) = -(X - C (7 / 4)) * panelP (m + 2) + e := by
        rw [show panelP (m + 3) = -(X - C (7 / 4)) * panelP (m + 2)
              - C (7 / 8) * panelP (m + 1) + C (1 / 8) * panelP m from rfl, he]
        ring
      rw [hEq]
      refine ⟨by omega, ?_⟩
      rw [show m + 3 + 2 = m + 4 + 1 by omega, key.2,
        show m + 4 = m + 2 + 2 by omega, hc]
      ring


/-! ### The recurrence is the generating function

`panelP` is *defined* by the recurrence `cor:panel-B-attractor` derives.  What
grounds it in `N/(Q + zt)` is the convolution system of `prop:initial-data`:
with `d` the coefficient sequence of `Q(t) + zt` and `N_m` that of
`N(t,z) = (1+z+z^2) + t(2-z)`, the sequence `panelP` solves
`∑_{j≤m} d_j P_{m-j} = N_m`, which by `prop:initial-data` determines it
uniquely.
-/

/-- Paper `cor:panel-B-attractor` — the coefficients of the denominator
`Q(t) + zt = 1 + (z - 7/4)t + (7/8)t^2 - (1/8)t^3`. -/
noncomputable def panelDenomCoeff : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X - C (7 / 4)
  | 2 => C (7 / 8)
  | 3 => C (-1 / 8)
  | _ + 4 => 0

/-- Paper `cor:panel-B-attractor` — the coefficients of the numerator
`N(t,z) = (1 + z + z^2) + t(2 - z)`. -/
noncomputable def panelNumCoeff : ℕ → ℚ[X]
  | 0 => X ^ 2 + X + 1
  | 1 => C 2 - X
  | _ + 2 => 0

/-- **Paper `cor:panel-B-attractor`, the coefficient comparison.**  `panelP`
solves the denominator convolution system of `prop:initial-data` for the panel-B
numerator, so it is the coefficient sequence of `N/(Q + zt)`. -/
theorem panelP_denomConv (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), panelDenomCoeff j * panelP (m - j) = panelNumCoeff m := by
  match m with
  | 0 => simp [panelDenomCoeff, panelNumCoeff, panelP]
  | 1 =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, Nat.sub_zero]
    change (1 : ℚ[X]) * panelP 1 + (X - C (7 / 4)) * panelP 0 = panelNumCoeff 1
    rw [show panelP 0 = X ^ 2 + X + 1 from rfl,
      show panelP 1 = -X ^ 3 + C (3 / 4) * X ^ 2 - C (1 / 4) * X + C (15 / 4) from rfl,
      show panelNumCoeff 1 = C 2 - X from rfl]
    have hC2 : (C 2 : ℚ[X]) = 2 := map_ofNat C 2
    have hA : (C (3 / 4) : ℚ[X]) = C (7 / 4) - 1 := by rw [← C_1, ← C_sub]; norm_num
    have hB : (C (1 / 4) : ℚ[X]) = 2 - C (7 / 4) := by
      rw [← hC2, ← C_sub]; norm_num
    have hD : (C (15 / 4) : ℚ[X]) = C (7 / 4) + 2 := by
      rw [← hC2, ← C_add]; norm_num
    rw [hA, hB, hD, hC2]
    ring
  | 2 =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, Nat.sub_zero]
    change (1 : ℚ[X]) * panelP 2 + (X - C (7 / 4)) * panelP 1 + C (7 / 8) * panelP 0 = 0
    rw [show panelP 2 = -(X - C (7 / 4)) * panelP 1 - C (7 / 8) * panelP 0 from rfl]
    ring
  | k + 3 =>
    have hsub : Finset.range 4 ⊆ Finset.range (k + 3 + 1) :=
      by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    have hzero : ∀ j ∈ Finset.range (k + 3 + 1), j ∉ Finset.range 4 →
        panelDenomCoeff j * panelP (k + 3 - j) = 0 := by
      intro j _ hj
      have h4 : 4 ≤ j := by simpa using hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
      simp [panelDenomCoeff]
    rw [← Finset.sum_subset hsub hzero]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, Nat.sub_zero]
    change (1 : ℚ[X]) * panelP (k + 3) + (X - C (7 / 4)) * panelP (k + 2)
        + C (7 / 8) * panelP (k + 1) + C (-1 / 8) * panelP k = panelNumCoeff (k + 3)
    rw [show panelP (k + 3) = -(X - C (7 / 4)) * panelP (k + 2)
        - C (7 / 8) * panelP (k + 1) + C (1 / 8) * panelP k from rfl,
      show panelNumCoeff (k + 3) = 0 from rfl,
      show (C (-1 / 8) : ℚ[X]) = -C (1 / 8) by rw [← C_neg]; norm_num]
    ring

/-- Paper `cor:panel-B-attractor` — `deg P_m = m + 2`. -/
theorem panelP_natDegree (m : ℕ) : (panelP m).natDegree = m + 2 :=
  (panelP_natDegree_and_coeff m).1

/-- Paper `cor:panel-B-attractor` — `[z^{m+2}] P_m = (-1)^m`, so `P_m` has
leading coefficient `(-1)^m` and in particular is nonzero. -/
theorem panelP_coeff_top (m : ℕ) : (panelP m).coeff (m + 2) = (-1) ^ m :=
  (panelP_natDegree_and_coeff m).2

theorem panelP_leadingCoeff (m : ℕ) : (panelP m).leadingCoeff = (-1) ^ m := by
  rw [leadingCoeff, panelP_natDegree, panelP_coeff_top]

theorem panelP_ne_zero (m : ℕ) : panelP m ≠ 0 := by
  intro h
  have := panelP_coeff_top m
  rw [h] at this
  simp at this
  exact absurd this.symm (by positivity)

end ForgacsTran
