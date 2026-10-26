/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.FactorWindowMonotonicity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# First moments of reflected-balanced actual cut sets

The reflection-count shortcut in factor transport for `thm:sharp-inflation`
of `shields-2026-skew-class-inflation.tex`.  Equal cut counts and reflected
balance force equal sums of cut positions.  Together with ordered prefix
monotonicity, this identifies the actual first and last windows without a
large-part coefficient calculation.  Sorry-free.
-/

namespace SkewClassInflation

/-- A reflection-symmetric integer function of zero mass has zero first moment. -/
theorem reflected_zero_mass_moment (N : ℕ) (f : ℕ → ℤ)
    (href : ∀ x ∈ Finset.Ioo 0 N, f (N - x) = f x)
    (hmass : ∑ x ∈ Finset.Ioo 0 N, f x = 0) :
    ∑ x ∈ Finset.Ioo 0 N, (x : ℤ) * f x = 0 := by
  have hsum : (∑ x ∈ Finset.Ioo 0 N, (x : ℤ) * f x) =
      ∑ x ∈ Finset.Ioo 0 N, ((N : ℤ) - x) * f x := by
    refine Finset.sum_bij (fun x _ => N - x) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨h0, hN⟩ := Finset.mem_Ioo.mp hx
      exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
    · intro x hx y hy he
      have hb := Finset.mem_Ioo.mp hx
      have hc := Finset.mem_Ioo.mp hy
      omega
    · intro y hy
      have hb := Finset.mem_Ioo.mp hy
      exact ⟨N - y, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro x hx
      have hb := Finset.mem_Ioo.mp hx
      rw [href x hx, Nat.cast_sub hb.2.le]
      ring
  have hlinear : (∑ x ∈ Finset.Ioo 0 N, ((N : ℤ) - x) * f x) =
      (N : ℤ) * (∑ x ∈ Finset.Ioo 0 N, f x) -
        ∑ x ∈ Finset.Ioo 0 N, (x : ℤ) * f x := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hlinear, hmass, mul_zero] at hsum
  omega

/-- Equal-cardinality cut sets with reflected balance have the same first moment. -/
theorem reflected_balanced_cut_sum (N : ℕ) (A B : Finset ℕ)
    (hA : A ⊆ Finset.Ioo 0 N) (hB : B ⊆ Finset.Ioo 0 N)
    (hcard : A.card = B.card)
    (hbalance : ∀ x ∈ Finset.Ioo 0 N,
      (if x ∈ A then (1 : ℕ) else 0) + (if N - x ∈ B then 1 else 0) =
        (if N - x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0)) :
    (∑ x ∈ A, (x : ℤ)) = ∑ x ∈ B, (x : ℤ) := by
  classical
  let f := fun x => (if x ∈ A then (1 : ℤ) else 0) - (if x ∈ B then 1 else 0)
  have href : ∀ x ∈ Finset.Ioo 0 N, f (N - x) = f x := by
    intro x hx
    have hh := hbalance x hx
    dsimp only [f]
    split_ifs at * <;> omega
  have hmass : ∑ x ∈ Finset.Ioo 0 N, f x = 0 := by
    dsimp only [f]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hA, Finset.inter_eq_right.mpr hB]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact sub_eq_zero.mpr (congrArg (fun x : ℕ => (x : ℤ)) hcard)
  have hmoment := reflected_zero_mass_moment N f href hmass
  have hpoint (x : ℕ) : (x : ℤ) * f x =
      (if x ∈ A then (x : ℤ) else 0) - (if x ∈ B then (x : ℤ) else 0) := by
    dsimp only [f]
    split_ifs <;> ring
  simp_rw [hpoint] at hmoment
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hA, Finset.inter_eq_right.mpr hB] at hmoment
  exact sub_eq_zero.mp hmoment

end SkewClassInflation
