/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.CornerMinors

/-!
# Differentiating a private determinant entry

The private-label coefficient calculation in `lem:exterior-gaps` is a
Laplace expansion followed by differentiation.  The minor and residual
are proved to avoid the generator from their actual matrix entries.
-/

namespace SkewCofactorIndependence

open scoped BigOperators

/-- Entrywise derivative-zero hypotheses propagate through a finite product. -/
theorem pderiv_prod_eq_zero {ι : Type*} (s : Finset ι) (f : ι → CompleteRing)
    (v : ℕ+) (h : ∀ i ∈ s, MvPolynomial.pderiv v (f i) = 0) :
    MvPolynomial.pderiv v (∏ i ∈ s, f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul,
        h i (Finset.mem_insert_self _ _),
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
      simp

set_option backward.isDefEq.respectTransparency false in
/-- An actual determinant has derivative zero when all its entries do. -/
theorem pderiv_det_eq_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) CompleteRing) (v : ℕ+)
    (h : ∀ i j, MvPolynomial.pderiv v (M i j) = 0) :
    MvPolynomial.pderiv v M.det = 0 := by
  classical
  rw [AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook, map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  have hp := pderiv_prod_eq_zero Finset.univ (fun i => M i (σ i)) v
    (fun i _ => h i (σ i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using congrArg Neg.neg hp

set_option backward.isDefEq.respectTransparency false in
/-- The private-variable coefficient under entrywise derivative-zero assumptions. -/
theorem pderiv_det_private_of_derivative_zero {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing)
    (v : ℕ+) (r c : Fin (n + 1)) (he : M r c = MvPolynomial.X v)
    (hprivate : ∀ a b, a ≠ r ∨ b ≠ c →
      MvPolynomial.pderiv v (M a b) = 0) :
    MvPolynomial.pderiv v M.det =
      (-1) ^ (r.val + c.val) * (M.submatrix r.succAbove c.succAbove).det := by
  classical
  rw [Matrix.det_succ_row M r, map_sum]
  have hminor : ∀ j : Fin (n + 1),
      MvPolynomial.pderiv v (M.submatrix r.succAbove j.succAbove).det = 0 := by
    intro j
    apply pderiv_det_eq_zero
    intro a b
    exact hprivate _ _ (Or.inl (Fin.succAbove_ne r a))
  have hsign : ∀ j : Fin (n + 1),
      MvPolynomial.pderiv v ((-1 : CompleteRing) ^ (r.val + j.val)) = 0 := by
    intro j
    have hC : (-1 : CompleteRing) ^ (r.val + j.val) =
        MvPolynomial.C ((-1 : ℚ) ^ (r.val + j.val)) := by simp
    rw [hC]
    exact MvPolynomial.pderiv_C
  calc
    (∑ j, MvPolynomial.pderiv v
      ((-1) ^ (r.val + j.val) * M r j * (M.submatrix r.succAbove j.succAbove).det)) =
        MvPolynomial.pderiv v
          ((-1) ^ (r.val + c.val) * M r c * (M.submatrix r.succAbove c.succAbove).det) := by
      apply Finset.sum_eq_single c
      · intro j _ hj
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
          hsign, hminor, hprivate r j (Or.inr hj)]
        ring
      · intro h
        exact False.elim (h (Finset.mem_univ c))
    _ = _ := by
      rw [he, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
        hsign, hminor, MvPolynomial.pderiv_X_self]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- Public adjugate form: differentiating entry `(r,c)` gives adjugate entry `(c,r)`. -/
theorem pderiv_det_eq_adjugate_of_private {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing)
    (v : ℕ+) (r c : Fin (n + 1)) (he : M r c = MvPolynomial.X v)
    (hprivate : ∀ a b, a ≠ r ∨ b ≠ c →
      MvPolynomial.pderiv v (M a b) = 0) :
    MvPolynomial.pderiv v M.det = M.adjugate c r := by
  rw [pderiv_det_private_of_derivative_zero M v r c he hprivate,
    Matrix.adjugate_fin_succ_eq_det_submatrix]

set_option backward.isDefEq.respectTransparency false in
/-- A determinant with one private linear entry has no quadratic coefficient in that generator. -/
theorem pderiv_twice_det_private_eq_zero {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing)
    (v : ℕ+) (r c : Fin (n + 1)) (he : M r c = MvPolynomial.X v)
    (hprivate : ∀ a b, a ≠ r ∨ b ≠ c →
      MvPolynomial.pderiv v (M a b) = 0) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv v M.det) = 0 := by
  rw [pderiv_det_private_of_derivative_zero M v r c he hprivate,
    MvPolynomial.pderiv_mul]
  have hs : MvPolynomial.pderiv v ((-1 : CompleteRing) ^ (r.val + c.val)) = 0 := by
    have he : (-1 : CompleteRing) ^ (r.val + c.val) =
        MvPolynomial.C ((-1 : ℚ) ^ (r.val + c.val)) := by simp
    rw [he]
    exact MvPolynomial.pderiv_C
  have hm : MvPolynomial.pderiv v (M.submatrix r.succAbove c.succAbove).det = 0 := by
    apply pderiv_det_eq_zero
    intro a b
    exact hprivate _ _ (Or.inl (Fin.succAbove_ne r a))
  rw [hs, hm]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- A constant factor and two linear factors give the exact second product derivative. -/
theorem pderiv_twice_three_mul (v : ℕ+) (a f g : CompleteRing)
    (ha : MvPolynomial.pderiv v a = 0)
    (hf : MvPolynomial.pderiv v (MvPolynomial.pderiv v f) = 0)
    (hg : MvPolynomial.pderiv v (MvPolynomial.pderiv v g) = 0) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv v (a * f * g)) =
      2 * a * MvPolynomial.pderiv v f * MvPolynomial.pderiv v g := by
  have h₁ : MvPolynomial.pderiv v (a * f * g) =
      a * MvPolynomial.pderiv v f * g + a * f * MvPolynomial.pderiv v g := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, ha]
    ring
  have h₂ : MvPolynomial.pderiv v (a * MvPolynomial.pderiv v f * g) =
      a * MvPolynomial.pderiv v f * MvPolynomial.pderiv v g := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, ha, hf]
    ring
  have h₃ : MvPolynomial.pderiv v (a * f * MvPolynomial.pderiv v g) =
      a * MvPolynomial.pderiv v f * MvPolynomial.pderiv v g := by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, ha, hg]
    ring
  rw [h₁, map_add, h₂, h₃]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Two exterior occurrences give exactly twice the doubly complementary determinant. -/
theorem pderiv_twice_det_exterior_pair {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) CompleteRing) (v : ℕ+)
    (ht : M 0 (Fin.last n).castSucc = MvPolynomial.X v)
    (hb : M (0 : Fin (n + 1)).succ (Fin.last (n + 1)) = MvPolynomial.X v)
    (hprivate : ∀ a b,
      (a ≠ 0 ∨ b ≠ (Fin.last n).castSucc) →
      (a ≠ (0 : Fin (n + 1)).succ ∨ b ≠ Fin.last (n + 1)) →
      MvPolynomial.pderiv v (M a b) = 0) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv v M.det) =
      2 * (M.submatrix (fun i : Fin n => i.succ.succ)
        (fun j : Fin n => j.castSucc.castSucc)).det := by
  classical
  let B (j : Fin (n + 2)) := M.submatrix Fin.succ j.succAbove
  have hrow : ∀ j : Fin (n + 2), j ≠ (Fin.last n).castSucc →
      MvPolynomial.pderiv v (M 0 j) = 0 := by
    intro j hj
    exact hprivate 0 j (Or.inr hj)
      (Or.inl (by simp))
  have hminor_private : ∀ j : Fin (n + 2), j ≠ Fin.last (n + 1) →
      ∀ a b : Fin (n + 1), a ≠ 0 ∨ b ≠ Fin.last n →
      MvPolynomial.pderiv v (B j a b) = 0 := by
    intro j hj a b hab
    apply hprivate a.succ (j.succAbove b)
      (Or.inl (Fin.succ_ne_zero a))
    rcases hab with ha | hb'
    · left
      intro he
      exact ha (Fin.succ_injective _ he)
    · right
      intro he
      have hl : j.succAbove (Fin.last n) = Fin.last (n + 1) :=
        Fin.succAbove_ne_last_last hj
      exact hb' (Fin.succAbove_right_injective (he.trans hl.symm))
  have hlast_zero : ∀ a b : Fin (n + 1),
      MvPolynomial.pderiv v (B (Fin.last (n + 1)) a b) = 0 := by
    intro a b
    exact hprivate _ _ (Or.inl (Fin.succ_ne_zero a))
      (Or.inr (Fin.succAbove_ne _ _))
  have hminor_entry : ∀ j : Fin (n + 2), j ≠ Fin.last (n + 1) →
      B j 0 (Fin.last n) = MvPolynomial.X v := by
    intro j hj
    have hl : j.succAbove (Fin.last n) = Fin.last (n + 1) :=
      Fin.succAbove_ne_last_last hj
    simpa only [B, Matrix.submatrix_apply, hl] using hb
  have hminor2 : ∀ j : Fin (n + 2),
      MvPolynomial.pderiv v (MvPolynomial.pderiv v (B j).det) = 0 := by
    intro j
    by_cases hj : j = Fin.last (n + 1)
    · subst j
      rw [pderiv_det_eq_zero _ _ hlast_zero]
      simp
    · exact pderiv_twice_det_private_eq_zero (B j) v 0 (Fin.last n)
        (hminor_entry j hj) (hminor_private j hj)
  have hsign : ∀ j : Fin (n + 2),
      MvPolynomial.pderiv v ((-1 : CompleteRing) ^ j.val) = 0 := by
    intro j
    have hc : (-1 : CompleteRing) ^ j.val = MvPolynomial.C ((-1 : ℚ) ^ j.val) := by simp
    rw [hc]
    exact MvPolynomial.pderiv_C
  have hrow2 : ∀ j : Fin (n + 2),
      MvPolynomial.pderiv v (MvPolynomial.pderiv v (M 0 j)) = 0 := by
    intro j
    by_cases hj : j = (Fin.last n).castSucc
    · subst j
      rw [ht, MvPolynomial.pderiv_X_self]
      exact MvPolynomial.pderiv_one
    · rw [hrow j hj]
      exact map_zero _
  have hterm : ∀ j : Fin (n + 2),
      MvPolynomial.pderiv v (MvPolynomial.pderiv v
        ((-1) ^ j.val * M 0 j * (B j).det)) =
        2 * (-1) ^ j.val * MvPolynomial.pderiv v (M 0 j) *
          MvPolynomial.pderiv v (B j).det := by
    intro j
    exact pderiv_twice_three_mul v _ _ _ (hsign j) (hrow2 j) (hminor2 j)
  rw [Matrix.det_succ_row_zero M, map_sum, map_sum]
  change (∑ j : Fin (n + 2), MvPolynomial.pderiv v (MvPolynomial.pderiv v
    ((-1) ^ j.val * M 0 j * (B j).det))) = _
  simp only [hterm]
  rw [Finset.sum_eq_single (Fin.last n).castSucc]
  · rw [ht, MvPolynomial.pderiv_X_self]
    have hj : (Fin.last n).castSucc ≠ Fin.last (n + 1) := by simp [Fin.ext_iff]
    rw [pderiv_det_private_of_derivative_zero (B (Fin.last n).castSucc) v 0
      (Fin.last n) (hminor_entry _ hj) (hminor_private _ hj)]
    have hm : (B (Fin.last n).castSucc).submatrix
        (0 : Fin (n + 1)).succAbove (Fin.last n).succAbove =
        M.submatrix (fun i : Fin n => i.succ.succ)
          (fun j : Fin n => j.castSucc.castSucc) := by
      ext i j
      simp [B, Fin.succAbove_last, Fin.succAbove,
        Matrix.submatrix_apply]
    rw [hm]
    have hs : (-1 : CompleteRing) ^ n * (-1) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    simp only [Fin.val_zero, Fin.val_last, Fin.val_castSucc, zero_add, mul_one]
    calc
      2 * (-1 : CompleteRing) ^ n *
          ((-1) ^ n * (M.submatrix (fun i : Fin n => i.succ.succ)
            (fun j : Fin n => j.castSucc.castSucc)).det) =
          2 * ((-1 : CompleteRing) ^ n * (-1) ^ n) *
            (M.submatrix (fun i : Fin n => i.succ.succ)
              (fun j : Fin n => j.castSucc.castSucc)).det := by ring
      _ = _ := by rw [hs, mul_one]
  · intro j _ hj
    rw [hrow j hj]
    simp only [mul_zero, zero_mul]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

set_option backward.isDefEq.respectTransparency false in
/-- An actual private independent variable differentiates to its signed complementary minor. -/
theorem pderiv_det_private {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing)
    (v : ℕ+) (i j : Fin (n + 1)) (he : M i j = MvPolynomial.X v)
    (hprivate : ∀ a b, a ≠ i ∨ b ≠ j → v ∉ (M a b).vars) :
    MvPolynomial.pderiv v M.det =
      (-1) ^ (i.val + j.val) * (M.submatrix i.succAbove j.succAbove).det := by
  apply pderiv_det_private_of_derivative_zero M v i j he
  intro a b hab
  exact MvPolynomial.pderiv_eq_zero_of_notMem_vars (hprivate a b hab)

/-- The ring homomorphism specializing one independent generator to zero. -/
noncomputable def eraseGenerator (v : ℕ+) : CompleteRing →+* CompleteRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if j = v then 0 else MvPolynomial.X j)

set_option backward.isDefEq.respectTransparency false in
/-- Specialization fixes an actual polynomial whose variables avoid the erased generator. -/
theorem eraseGenerator_eq_self (v : ℕ+) (p : CompleteRing) (hp : v ∉ p.vars) :
    eraseGenerator v p = p := by
  classical
  have h : eraseGenerator v p =
      MvPolynomial.eval₂Hom MvPolynomial.C MvPolynomial.X p := by
    apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
    intro j hj _
    have hne : j ≠ v := by rintro rfl; exact hp hj
    simp [hne]
  simpa using h

/-- Erasure acts entrywise on the actual determinant. -/
theorem eraseGenerator_det {n : ℕ} (v : ℕ+)
    (M : Matrix (Fin n) (Fin n) CompleteRing) :
    eraseGenerator v M.det = (M.map (eraseGenerator v)).det :=
  (eraseGenerator v).map_det M

set_option backward.isDefEq.respectTransparency false in
/-- Entrywise erased private labels retain all other positive generators. -/
theorem eraseGenerator_complete (v : ℕ+) (k : ℤ) :
    eraseGenerator v (complete k) = if k = (v.val : ℤ) then 0 else complete k := by
  classical
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hne : k ≠ (v.val : ℤ) := by have := v.pos; omega
    simp only [complete_of_neg hk, map_zero, hne, ite_false]
  · subst k
    have hne : (0 : ℤ) ≠ (v.val : ℤ) := by have := v.pos; omega
    simp only [complete_zero, map_one, hne, ite_false]
  · let w : ℕ+ := ⟨k.toNat, by omega⟩
    have hc : complete k = (MvPolynomial.X w : CompleteRing) := complete_of_pos hk
    have hw : w = v ↔ k = (v.val : ℤ) := by
      constructor
      · intro h
        have he := congrArg (fun z : ℕ+ => z.val) h
        change k.toNat = v.val at he
        omega
      · intro h
        apply Subtype.ext
        change k.toNat = v.val
        omega
    rw [hc]
    simp only [eraseGenerator, MvPolynomial.eval₂Hom_X']
    change (if w = v then 0 else (MvPolynomial.X w : CompleteRing)) =
      if k = (v.val : ℤ) then 0 else MvPolynomial.X w
    simp only [hw]

end SkewCofactorIndependence
