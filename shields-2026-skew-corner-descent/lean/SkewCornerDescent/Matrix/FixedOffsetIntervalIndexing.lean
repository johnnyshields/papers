/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ConsecutiveMatrixWindows

/-!
# Exact finite interval starts and complete window products

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every bounded ordered interval is enumerated once by its genuine start,
including zero-length and empty finite boundaries.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Ordered endpoint pairs of fixed displacement are precisely the valid starts. -/
theorem fixed_offset_pair_sum {N : ℕ} (d : ℕ) {R : Type*} [AddCommMonoid R]
    (f : Fin N → Fin N → R) :
    (∑ i : Fin N, ∑ j : Fin N, if j.val = i.val + d then f i j else 0) =
      ∑ i : Fin (N - d),
        f ⟨i.val, by have := i.isLt; omega⟩
          ⟨i.val + d, by have := i.isLt; omega⟩ := by
  classical
  let pred := fun p : Fin N × Fin N => p.2.val = p.1.val + d
  let e : Fin (N - d) ≃ {p // pred p} :=
    { toFun := fun i => ⟨(⟨i.val, by have := i.isLt; omega⟩,
        ⟨i.val + d, by have := i.isLt; omega⟩), rfl⟩
      invFun := fun p => ⟨p.1.1.val, by
        have hj := p.1.2.isLt
        have hp : p.1.2.val = p.1.1.val + d := p.2
        omega⟩
      left_inv := fun i => Fin.ext rfl
      right_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext rfl
        · exact Fin.ext p.2.symm }
  have he := Fintype.sum_equiv e
    (fun i => f ⟨i.val, by have := i.isLt; omega⟩
      ⟨i.val + d, by have := i.isLt; omega⟩)
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

/-- Positive truncated differences do not introduce backward endpoint pairs. -/
theorem positive_difference_pair_sum {N d : ℕ} (hd : 0 < d)
    {R : Type*} [AddCommMonoid R] (f : Fin N → Fin N → R) :
    (∑ i : Fin N, ∑ j : Fin N, if j.val - i.val = d then f i j else 0) =
      ∑ i : Fin (N - d), f ⟨i.val, by have := i.isLt; omega⟩
        ⟨i.val + d, by have := i.isLt; omega⟩ := by
  have hp (i j : Fin N) : j.val - i.val = d ↔ j.val = i.val + d := by omega
  simp only [hp]
  exact fixed_offset_pair_sum d f

/-- Explicit ordering also permits the zero-displacement interval. -/
theorem ordered_difference_pair_sum {N : ℕ} (d : ℕ)
    {R : Type*} [AddCommMonoid R] (f : Fin N → Fin N → R) :
    (∑ i : Fin N, ∑ j : Fin N,
      if i.val ≤ j.val ∧ j.val - i.val = d then f i j else 0) =
      ∑ i : Fin (N - d), f ⟨i.val, by have := i.isLt; omega⟩
        ⟨i.val + d, by have := i.isLt; omega⟩ := by
  have hp (i j : Fin N) :
      i.val ≤ j.val ∧ j.val - i.val = d ↔ j.val = i.val + d := by omega
  simp only [hp]
  exact fixed_offset_pair_sum d f

/-- A full finite interval product is the product of its consecutive window
entries. No missing index is filled by a default value. -/
@[to_additive fixed_interval_sum]
theorem fixed_interval_product {N d : ℕ} {R : Type*} [CommMonoid R]
    (w : Fin N → R) (s : Fin (N - d)) :
    (∏ k ∈ Finset.Icc (⟨s.val, by have := s.isLt; omega⟩ : Fin N)
      ⟨s.val + d, by have := s.isLt; omega⟩, w k) =
      ∏ k : Fin (d + 1), w ⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩ := by
  classical
  symm
  apply Finset.prod_bij (fun k _ =>
    (⟨s.val + k.val, by have := s.isLt; have := k.isLt; omega⟩ : Fin N))
  · intro k _
    rw [Finset.mem_Icc]
    constructor
    · change s.val ≤ s.val + k.val
      omega
    · change s.val + k.val ≤ s.val + d
      have := k.isLt
      omega
  · intro a _ b _ hab
    apply Fin.ext
    have he := congrArg Fin.val hab
    change s.val + a.val = s.val + b.val at he
    omega
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hlo, hhi⟩
    change s.val ≤ k.val at hlo
    change k.val ≤ s.val + d at hhi
    refine ⟨⟨k.val - s.val, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change s.val + (k.val - s.val) = k.val
    omega
  · intro k _
    rfl

end SkewCornerDescent.Matrix
