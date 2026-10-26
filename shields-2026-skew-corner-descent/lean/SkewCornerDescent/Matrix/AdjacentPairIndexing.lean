/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergIntervalSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact original adjacent-pair enumeration

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
All original adjacent endpoints occur once, including the empty and one-state
boundaries. The endpoint list does not identify repeated values.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Adjacent endpoint pairs are exactly the consecutive original starts. -/
theorem adjacent_pair_sum {N : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Fin N → Fin N → R) :
    (∑ i : Fin N, ∑ j : Fin N, if j.val = i.val + 1 then f i j else 0) =
      ∑ i : Fin (N - 1),
        f ⟨i.val, by have := i.isLt; omega⟩
          ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  classical
  let pred := fun p : Fin N × Fin N => p.2.val = p.1.val + 1
  let e : Fin (N - 1) ≃ {p // pred p} :=
    { toFun := fun i => ⟨(⟨i.val, by have := i.isLt; omega⟩,
        ⟨i.val + 1, by have := i.isLt; omega⟩), rfl⟩
      invFun := fun p => ⟨p.1.1.val, by
        have hj := p.1.2.isLt
        have hp : p.1.2.val = p.1.1.val + 1 := p.2
        omega⟩
      left_inv := fun i => Fin.ext rfl
      right_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext rfl
        · exact Fin.ext p.2.symm }
  have he := Fintype.sum_equiv e
    (fun i => f ⟨i.val, by have := i.isLt; omega⟩
      ⟨i.val + 1, by have := i.isLt; omega⟩)
    (fun p => f p.1.1 p.1.2) (fun _ => rfl)
  have hsub : (∑ p : {p // pred p}, f p.1.1 p.1.2) =
      ∑ p ∈ Finset.univ.filter pred, f p.1 p.2 := by
    exact (Finset.sum_subtype (p := pred) (Finset.univ.filter pred)
      (fun p => by simp) (fun p => f p.1 p.2)).symm
  calc
    _ = ∑ p ∈ Finset.univ.filter pred, f p.1 p.2 := by
      simp only [Finset.sum_filter, Fintype.sum_prod_type, pred]
    _ = ∑ p : {p // pred p}, f p.1.1 p.1.2 := hsub.symm
    _ = _ := he.symm

/-- The closed interval of an actual adjacent pair contains exactly its two
endpoint weights, including finite index boundary pairs. -/
theorem adjacent_pair_interval_product {N : ℕ} {R : Type*} [CommMonoid R]
    (w : Fin N → R) (i j : Fin N) (hij : j.val = i.val + 1) :
    (∏ k ∈ Finset.Icc i j, w k) = w i * w j := by
  rw [Finset.prod_fin_Icc_eq_prod_nat_Icc, hij,
    Finset.prod_Icc_succ_top (by omega), Finset.Icc_self, Finset.prod_singleton]
  have hj : i.val + 1 < N := by have := j.isLt; omega
  rw [dite_eq_left i.isLt, dite_eq_left hj]
  exact congrArg (fun k => w i * w k) (Fin.ext hij.symm)

end SkewCornerDescent.Matrix
