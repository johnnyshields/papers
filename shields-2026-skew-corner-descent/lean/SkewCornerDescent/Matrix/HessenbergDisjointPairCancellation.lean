/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergOneShyIndexing

/-!
# Exact positional cancellation of disjoint marked pair activities

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
All long intervals and adjacent pairs are indexed by their original endpoints.
Cost-two pairs keep both possible marks; no unordered quotient is taken.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Every complete disjoint marked interval pair corresponds to exactly its
four original endpoints, with no multiplicity discarded. -/
theorem one_shy_pair_sum_eq_filtered {N m : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Fin N → Fin N → Fin N → Fin N → R) :
    (∑ p : OneShyIntervalPair N m, f p.longStart p.longEnd p.pairStart p.pairEnd) =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
          Disjoint (Finset.Icc i j) (Finset.Icc k l) then f i j k l else 0 := by
  classical
  let pred := fun x : (Fin N × Fin N) × (Fin N × Fin N) =>
    x.1.2.val - x.1.1.val = m - 1 ∧ x.2.2.val = x.2.1.val + 1 ∧
      Disjoint (Finset.Icc x.1.1 x.1.2) (Finset.Icc x.2.1 x.2.2)
  let e : OneShyIntervalPair N m ≃ {x // pred x} :=
    { toFun := fun p => ⟨((p.longStart, p.longEnd), (p.pairStart, p.pairEnd)),
        ⟨p.longLength, p.pairLength, p.disjoint⟩⟩
      invFun := fun x => ⟨x.1.1.1, x.1.1.2, x.1.2.1, x.1.2.2,
        x.2.1, x.2.2.1, x.2.2.2⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun x => by rcases x with ⟨⟨⟨i,j⟩,⟨k,l⟩⟩,h⟩; rfl }
  have he := Fintype.sum_equiv e
    (fun p => f p.longStart p.longEnd p.pairStart p.pairEnd)
    (fun x => f x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2) (fun _ => rfl)
  rw [he]
  have hsub : (∑ x : {x // pred x}, f x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2) =
      ∑ x ∈ Finset.univ.filter pred, f x.1.1 x.1.2 x.2.1 x.2.2 := by
    exact (Finset.sum_subtype (p := pred) (Finset.univ.filter pred)
      (fun x => by simp) (fun x => f x.1.1 x.1.2 x.2.1 x.2.2)).symm
  rw [hsub, Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]

/-- Subtracting all pair products cancels exactly the disjoint marked activities
and leaves the negative sum over overlapping intervals, with ordered marks retained. -/
theorem one_shy_disjoint_pair_cancellation {N m : ℕ} {R : Type*} [CommRing R]
    (L Q : Fin N → Fin N → R) :
    (∑ p : OneShyIntervalPair N m, L p.longStart p.longEnd * Q p.pairStart p.pairEnd) -
      (∑ i : Fin N, ∑ j : Fin N, if j.val - i.val = m - 1 then L i j else 0) *
        (∑ k : Fin N, ∑ l : Fin N, if l.val = k.val + 1 then Q k l else 0) =
    -(∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
      if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
        ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then L i j * Q k l else 0) := by
  classical
  have hs : (∑ p : OneShyIntervalPair N m,
      L p.longStart p.longEnd * Q p.pairStart p.pairEnd) +
      (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
          ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then L i j * Q k l else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if j.val - i.val = m - 1 then L i j else 0) *
        (∑ k : Fin N, ∑ l : Fin N, if l.val = k.val + 1 then Q k l else 0) := by
    rw [one_shy_pair_sum_eq_filtered (N := N) (m := m) (fun i j k l => L i j * Q k l)]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hlong : j.val - i.val = m - 1 <;>
      by_cases hpair : l.val = k.val + 1 <;>
      by_cases hd : Disjoint (Finset.Icc i j) (Finset.Icc k l) <;>
      simp [hlong, hpair, hd]
  linear_combination hs

/-- The exact selected-cost signs convert the full first-partition subtraction
into the negative overlapping-pair charge. No unordered identification is made,
including at cost two. -/
theorem signed_disjoint_pair_log_cancellation {N m : ℕ} (hm : 0 < m)
    {R : Type*} [CommRing R] (b γ : R) (L Q : Fin N → Fin N → R) :
    let lower := ∑ i : Fin N, ∑ j : Fin N,
      if j.val - i.val = m - 1 then L i j else 0
    let pairs := ∑ k : Fin N, ∑ l : Fin N,
      if l.val = k.val + 1 then Q k l else 0
    (-1 : R) ^ m * b ^ m * γ *
        (∑ p : OneShyIntervalPair N m, L p.longStart p.longEnd * Q p.pairStart p.pairEnd) -
      (-1 : R) ^ (m - 1) * b ^ (m - 1) * (-b * pairs) * (γ * lower) =
    -((-1 : R) ^ m * b ^ m) * γ *
      (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        if j.val - i.val = m - 1 ∧ l.val = k.val + 1 ∧
          ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then L i j * Q k l else 0) := by
  have hstep : m - 1 + 1 = m := by omega
  have hsign : (-1 : R) ^ (m - 1) * b ^ (m - 1) * b = -((-1 : R) ^ m * b ^ m) := by
    conv_rhs => rw [← hstep, pow_succ, pow_succ]
    ring
  have h := one_shy_disjoint_pair_cancellation (m := m) L Q
  dsimp only
  linear_combination
    ((-1 : R) ^ m * b ^ m * γ) * h +
    (γ * (∑ i : Fin N, ∑ j : Fin N, if j.val - i.val = m - 1 then L i j else 0) *
      (∑ k : Fin N, ∑ l : Fin N, if l.val = k.val + 1 then Q k l else 0)) * hsign

end SkewCornerDescent.Matrix
