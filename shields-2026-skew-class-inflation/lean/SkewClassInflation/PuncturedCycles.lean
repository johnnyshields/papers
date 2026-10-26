/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.EquivFin

/-!
# Completing an invariant function across one deleted vertex

The punctured-cycle step in `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  Invariance away from a single
vertex implies equality of the two path endpoints by cancellation in
the finite permutation sum.  Reassigning only the deleted vertex then
produces an invariant function on the entire cycle system.  Sorry-free.
-/

namespace SkewClassInflation

open scoped BigOperators

/-- The two neighbors of a deleted vertex have equal values in every finite permutation cycle. -/
theorem punctured_cycle_endpoints {ι A : Type*} [Finite ι] [AddCommGroup A]
    (σ : Equiv.Perm ι) (z : ι) (f : ι → A)
    (h : ∀ x, x ≠ z → σ x ≠ z → f (σ x) = f x) :
    f (σ z) = f (σ.symm z) := by
  classical
  let _ := Fintype.ofFinite ι
  by_cases hz : σ z = z
  · have hw : σ.symm z = z := by
      apply σ.injective
      rw [σ.apply_symm_apply, hz]
    rw [hz, hw]
  have hzw : z ≠ σ.symm z := by
    intro he
    have hh := congrArg σ he
    rw [σ.apply_symm_apply] at hh
    exact hz hh
  have hsum : (∑ x, (f (σ x) - f x)) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
  have hterms (x : ι) : f (σ x) - f x =
      (if x = z then f (σ z) - f z else 0) +
        (if x = σ.symm z then f z - f (σ.symm z) else 0) := by
    by_cases hx : x = z
    · subst x
      simp only [ite_true, ite_eq_right hzw, add_zero]
    · by_cases hw : x = σ.symm z
      · subst x
        simp only [σ.apply_symm_apply, ite_eq_right hx, ite_true, zero_add]
      · have hs : σ x ≠ z := by
          intro he
          apply hw
          exact σ.injective (he.trans (σ.apply_symm_apply z).symm)
        rw [h x hx hs]
        simp only [sub_self, ite_eq_right hx, ite_eq_right hw, add_zero]
  have heSum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hterms x)
  replace hsum := heSum.symm.trans hsum
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  have hc : (f (σ z) - f z) + (f z - f (σ.symm z)) =
      f (σ z) - f (σ.symm z) := by abel
  rw [hc] at hsum
  exact sub_eq_zero.mp hsum

/-- Filling one deleted vertex extends punctured invariance to the whole finite permutation. -/
theorem punctured_cycle_completion {ι A : Type*} [Finite ι] [DecidableEq ι] [AddCommGroup A]
    (σ : Equiv.Perm ι) (z : ι) (f : ι → A)
    (h : ∀ x, x ≠ z → σ x ≠ z → f (σ x) = f x) :
    let g : ι → A := fun x => if x = z then f (σ z) else f x
    ∀ x, g (σ x) = g x := by
  classical
  intro g x
  have hend := punctured_cycle_endpoints σ z f h
  by_cases hx : x = z
  · subst x
    simp only [g, ite_true]
    split_ifs <;> rfl
  · by_cases hs : σ x = z
    · have hw : x = σ.symm z := by
        exact σ.injective (hs.trans (σ.apply_symm_apply z).symm)
      simp only [g, hs, ite_true, ite_eq_right hx]
      exact hend.trans (congrArg f hw).symm
    · simp only [g, ite_eq_right hx, ite_eq_right hs]
      exact h x hx hs

end SkewClassInflation
