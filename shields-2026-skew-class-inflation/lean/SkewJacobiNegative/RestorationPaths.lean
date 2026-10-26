/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/RestorationPaths.lean

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic

/-!
# Terminating restoration algebra

The generic ring identities underlying `prop:path-expansion`,
`eq:schur-complement`, and `eq:first-components` in
`shields-2026-skew-cofactor-independence.tex`.  The marking parameter is an
ordinary polynomial variable.  Neither the block identity nor its coefficient
producer assumes that the residual matrix is invertible.  These identities do
not assemble the sorted beta lists or prove their connectedness.
-/

namespace SkewJacobiNegative
namespace RestorationPaths

open scoped BigOperators
open Matrix Polynomial

variable {R : Type*} [CommRing R] {k m : ℕ}

/-- Strict upper triangularity, including a zero diagonal. -/
def StrictUpper (T : Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ i j, ¬ i < j → T i j = 0

/-- A product of `r` strict steps can only reach a column at least `r` positions later. -/
theorem pow_entry_eq_zero (T : Matrix (Fin m) (Fin m) R) (hT : StrictUpper T)
    (r : ℕ) (i j : Fin m) (hij : j.val < i.val + r) :
    (T ^ r) i j = 0 := by
  induction r generalizing i j with
  | zero =>
      have hne : i ≠ j := by intro h; subst j; omega
      simp [hne]
  | succ r ih =>
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro u hu
      by_cases hiu : i < u
      · have huj : j.val < u.val + r := by
          have : i.val < u.val := hiu
          omega
        rw [ih u j huj, mul_zero]
      · rw [hT i u hiu, zero_mul]

/-- The nilpotence exponent is the size of the common-beta block. -/
theorem strict_upper_pow_eq_zero (T : Matrix (Fin m) (Fin m) R)
    (hT : StrictUpper T) : T ^ m = 0 := by
  ext i j
  exact pow_entry_eq_zero T hT m i j (by have := j.isLt; omega)

/-- The explicit finite geometric inverse; no division is used. -/
noncomputable def finiteInverse (t : R) (T : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin m) (Fin m) R :=
  ∑ r ∈ Finset.range m, (-t • T) ^ r

/-- The displayed alternating-power form of the finite inverse. -/
theorem finiteInverse_eq_sum (t : R) (T : Matrix (Fin m) (Fin m) R) :
    finiteInverse t T = ∑ r ∈ Finset.range m, (-t) ^ r • T ^ r := by
  unfold finiteInverse
  apply Finset.sum_congr rfl
  intro r hr
  exact smul_pow (-t) T r

/-- Left cancellation for the finite inverse, including an empty common-beta block. -/
theorem one_add_mul_finiteInverse (t : R) (T : Matrix (Fin m) (Fin m) R)
    (hT : StrictUpper T) : (1 + t • T) * finiteInverse t T = 1 := by
  have hn : (-t • T) ^ m = 0 := by
    rw [smul_pow, strict_upper_pow_eq_zero T hT, smul_zero]
  have h := mul_neg_geom_sum (-t • T) m
  rw [hn] at h
  simpa [finiteInverse, sub_eq_add_neg] using h

/-- Right cancellation for the same explicit inverse. -/
theorem finiteInverse_mul_one_add (t : R) (T : Matrix (Fin m) (Fin m) R)
    (hT : StrictUpper T) : finiteInverse t T * (1 + t • T) = 1 := by
  have hn : (-t • T) ^ m = 0 := by
    rw [smul_pow, strict_upper_pow_eq_zero T hT, smul_zero]
  have h := geom_sum_mul_neg (-t • T) m
  rw [hn] at h
  simpa [finiteInverse, sub_eq_add_neg] using h

/-- The unitriangular common-beta block has determinant one. -/
theorem det_one_add (t : R) (T : Matrix (Fin m) (Fin m) R)
    (hT : StrictUpper T) : (1 + t • T).det = 1 := by
  have hu : (1 + t • T).IsUpperTriangular := by
    intro i j hji
    have hne : i ≠ j := ne_of_gt hji
    have hzero := hT i j (not_lt.mpr (le_of_lt hji))
    simp [hne, hzero]
  rw [Matrix.det_of_isUpperTriangular hu]
  apply Finset.prod_eq_one
  intro i hi
  simp [hT i i (lt_irrefl i)]

/-- The reduced matrix before the overall marking factor is extracted. -/
noncomputable def reduced (t : R) (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) : Matrix (Fin k) (Fin k) R :=
  L - t • (P * finiteInverse t T * Q)

/-- The exact terminating Schur-complement identity (`eq:schur-complement`).
The proof eliminates the upper-right block by a determinant-one multiplier;
it never assumes an inverse for `L`. -/
theorem block_det (t : R) (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) (hT : StrictUpper T) :
    (Matrix.fromBlocks (t • L) (t • P) (t • Q) (1 + t • T)).det =
      t ^ k * (reduced t L P Q T).det := by
  let D : Matrix (Fin m) (Fin m) R := 1 + t • T
  let B : Matrix (Fin k) (Fin m) R := t • P
  let V := finiteInverse t T
  let E : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) R :=
    Matrix.fromBlocks 1 (-(B * V)) 0 1
  have hE : E.det = 1 := by simp [E]
  have hVD : V * D = 1 := finiteInverse_mul_one_add t T hT
  have hBD : B + (-(B * V)) * D = 0 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hVD, Matrix.mul_one, add_neg_cancel]
  have hleft : t • L + (-(B * V)) * (t • Q) =
      t • reduced t L P Q T := by
    ext i j
    simp only [B, V, reduced, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  have hprod : E * Matrix.fromBlocks (t • L) B (t • Q) D =
      Matrix.fromBlocks (t • reduced t L P Q T) 0 (t • Q) D := by
    change Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) R) (-(B * V))
      (0 : Matrix (Fin m) (Fin k) R) (1 : Matrix (Fin m) (Fin m) R) *
        Matrix.fromBlocks (t • L) B (t • Q) D =
          Matrix.fromBlocks (t • reduced t L P Q T) 0 (t • Q) D
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, zero_add, hBD, hleft]
  have hd := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hE, one_mul, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_smul, Fintype.card_fin] at hd
  simpa [B, D, det_one_add t T hT] using hd

/-- The reduced matrix is the alternating finite path series. -/
theorem reduced_eq_sum (t : R) (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) :
    reduced t L P Q T =
      L + ∑ r ∈ Finset.range m, (-t) ^ (r + 1) • (P * T ^ r * Q) := by
  rw [reduced, finiteInverse_eq_sum]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Finset.smul_sum, smul_smul]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [← neg_smul, pow_succ']
  congr 1
  ring

/-- The block identity with the terminating series displayed in its determinant. -/
theorem block_det_eq_finite_series (t : R) (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) (hT : StrictUpper T) :
    (Matrix.fromBlocks (t • L) (t • P) (t • Q) (1 + t • T)).det =
      t ^ k * (L + ∑ r ∈ Finset.range m,
        (-t) ^ (r + 1) • (P * T ^ r * Q)).det := by
  rw [block_det t L P Q T hT, reduced_eq_sum]

/-- The first marking coefficient of a product, with an explicit distinguished factor. -/
theorem coeff_one_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → R[X]) :
    (∏ i ∈ s, f i).coeff 1 =
      ∑ j ∈ s, ∏ i ∈ s, if i = j then (f i).coeff 1 else (f i).coeff 0 := by
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Polynomial.mul_coeff_one, ih,
        Polynomial.coeff_zero_prod, Finset.sum_insert ha]
      have hhead : (∏ i ∈ insert a s,
          if i = a then (f i).coeff 1 else (f i).coeff 0) =
          (f a).coeff 1 * ∏ i ∈ s, (f i).coeff 0 := by
        rw [Finset.prod_insert ha]
        simp only [ite_true]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [ite_eq_right (by intro h; subst i; exact ha hi)]
      have htail : (∑ j ∈ s, ∏ i ∈ insert a s,
          if i = j then (f i).coeff 1 else (f i).coeff 0) =
          (f a).coeff 0 * ∑ j ∈ s, ∏ i ∈ s,
            if i = j then (f i).coeff 1 else (f i).coeff 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.prod_insert ha, ite_eq_right (by intro h; subst j; exact ha hj)]
      rw [hhead, htail]
      ring

/-- Coefficientwise determinants have the usual first variation even at singular matrices. -/
theorem det_coeff_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R[X]) :
    M.det.coeff 1 =
      ∑ j : ι, ((M.map fun p => p.coeff 0).updateCol j
        (fun i => (M i j).coeff 1)).det := by
  have hdet : M.det = ∑ σ : Equiv.Perm ι,
      Polynomial.C (((Equiv.Perm.sign σ : ℤ) : R)) * ∏ i, M (σ i) i := by
    simpa only [map_intCast] using Matrix.det_apply' M
  rw [hdet]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, coeff_one_prod,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hij : i = j
  · subst i
    simp
  · simp [Matrix.map_apply, hij]

/-- The adjugate entry is the genuine signed complementary determinant. -/
theorem adjugate_cofactor (L : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (i j : Fin (k + 1)) :
    L.adjugate j i = (-1) ^ (i.val + j.val) *
      (L.submatrix i.succAbove j.succAbove).det :=
  Matrix.adjugate_fin_succ_eq_det_submatrix L j i

/-- First variation in cofactor form, with no nonsingularity assumption. -/
theorem det_coeff_one_eq_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R[X]) :
    M.det.coeff 1 = ∑ j : ι, ∑ i : ι,
      (M.map fun p => p.coeff 0).adjugate j i * (M i j).coeff 1 := by
  rw [det_coeff_one]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- The inverse has identity constant term, proved from its produced inverse identity. -/
theorem finiteInverse_constant (T : Matrix (Fin m) (Fin m) R)
    (hT : StrictUpper T) :
    (finiteInverse (Polynomial.X : R[X]) (T.map Polynomial.C)).map
      Polynomial.constantCoeff = 1 := by
  have hTC : StrictUpper (T.map Polynomial.C) := by
    intro i j hij
    simp [Matrix.map_apply, hT i j hij]
  have hD : (1 + (Polynomial.X : R[X]) • T.map Polynomial.C).map
      Polynomial.constantCoeff = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]
  have hOne : (1 : Matrix (Fin m) (Fin m) R[X]).map
      Polynomial.constantCoeff = (1 : Matrix (Fin m) (Fin m) R) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]
  have h := congrArg (fun A : Matrix (Fin m) (Fin m) R[X] =>
      A.map Polynomial.constantCoeff)
      (one_add_mul_finiteInverse (Polynomial.X : R[X]) (T.map Polynomial.C) hTC)
  rw [Matrix.map_mul, hD, Matrix.one_mul, hOne] at h
  exact h

/-- The marked reduced matrix has constant matrix `L`. -/
theorem reduced_coeff_zero (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) :
    (reduced (Polynomial.X : R[X]) (L.map Polynomial.C) (P.map Polynomial.C)
      (Q.map Polynomial.C) (T.map Polynomial.C)).map (fun p => p.coeff 0) = L := by
  ext i j
  simp [reduced, Matrix.map_apply]

/-- The linear marking matrix is the negative single-insertion product. -/
theorem reduced_coeff_one (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) (hT : StrictUpper T) :
    (reduced (Polynomial.X : R[X]) (L.map Polynomial.C) (P.map Polynomial.C)
      (Q.map Polynomial.C) (T.map Polynomial.C)).map (fun p => p.coeff 1) = -(P * Q) := by
  have hV := finiteInverse_constant T hT
  have hPQ : ((P.map Polynomial.C *
        finiteInverse (Polynomial.X : R[X]) (T.map Polynomial.C) *
        Q.map Polynomial.C).map Polynomial.constantCoeff) = P * Q := by
    rw [Matrix.map_mul, Matrix.map_mul, hV, Matrix.mul_one]
    congr 1 <;> ext i j <;> simp
  ext i j
  have hij := congrArg (fun A : Matrix (Fin k) (Fin k) R => A i j) hPQ
  simpa [reduced, Matrix.map_apply, Polynomial.mul_coeff_one,
    Polynomial.constantCoeff_apply] using congrArg Neg.neg hij

/-- The first two coefficients of the reduced determinant (`eq:first-components`). -/
theorem reduced_det_first_coefficients (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) (hT : StrictUpper T) :
    let F := (reduced (Polynomial.X : R[X]) (L.map Polynomial.C)
      (P.map Polynomial.C) (Q.map Polynomial.C) (T.map Polynomial.C)).det
    F.coeff 0 = L.det ∧
      F.coeff 1 = -∑ z : Fin m, ∑ j : Fin k, ∑ i : Fin k,
        L.adjugate j i * P i z * Q z j := by
  dsimp only
  constructor
  · rw [← Polynomial.constantCoeff_apply, RingHom.map_det]
    change ((reduced (Polynomial.X : R[X]) (L.map Polynomial.C)
      (P.map Polynomial.C) (Q.map Polynomial.C) (T.map Polynomial.C)).map
      (fun p => p.coeff 0)).det = L.det
    rw [reduced_coeff_zero]
  · rw [det_coeff_one_eq_contraction, reduced_coeff_zero]
    have hlin := reduced_coeff_one L P Q T hT
    have hentry : ∀ i j,
        (reduced (Polynomial.X : R[X]) (L.map Polynomial.C)
          (P.map Polynomial.C) (Q.map Polynomial.C) (T.map Polynomial.C) i j).coeff 1 =
          -(P * Q) i j := by
      intro i j
      exact congrArg (fun A : Matrix (Fin k) (Fin k) R => A i j) hlin
    simp only [hentry, Matrix.mul_apply, mul_neg, Finset.sum_neg_distrib,
      Finset.mul_sum, mul_assoc]
    congr 1
    calc
      (∑ j : Fin k, ∑ i : Fin k, ∑ z : Fin m,
          L.adjugate j i * (P i z * Q z j)) =
          ∑ j : Fin k, ∑ z : Fin m, ∑ i : Fin k,
            L.adjugate j i * (P i z * Q z j) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact Finset.sum_comm
      _ = ∑ z : Fin m, ∑ j : Fin k, ∑ i : Fin k,
          L.adjugate j i * (P i z * Q z j) := Finset.sum_comm

/-- After extracting the exact overall factor, the marking degrees are `k` and `k+1`. -/
theorem marked_block_first_coefficients (L : Matrix (Fin k) (Fin k) R)
    (P : Matrix (Fin k) (Fin m) R) (Q : Matrix (Fin m) (Fin k) R)
    (T : Matrix (Fin m) (Fin m) R) (hT : StrictUpper T) :
    let G := (Matrix.fromBlocks ((Polynomial.X : R[X]) • L.map Polynomial.C)
      ((Polynomial.X : R[X]) • P.map Polynomial.C)
      ((Polynomial.X : R[X]) • Q.map Polynomial.C)
      ((1 : Matrix (Fin m) (Fin m) R[X]) + (Polynomial.X : R[X]) • T.map Polynomial.C)).det
    G.coeff k = L.det ∧
      G.coeff (k + 1) = -∑ z : Fin m, ∑ j : Fin k, ∑ i : Fin k,
        L.adjugate j i * P i z * Q z j := by
  dsimp only
  have hTC : StrictUpper (T.map Polynomial.C) := by
    intro i j hij
    simp [Matrix.map_apply, hT i j hij]
  rw [block_det _ _ _ _ _ hTC, mul_comm (Polynomial.X ^ k)]
  simpa [Polynomial.coeff_mul_X_pow', Nat.add_comm] using
    reduced_det_first_coefficients L P Q T hT

end RestorationPaths
end SkewJacobiNegative
