/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.SpliceNonzeroMain

/-!
# Adjugate lemmas for the whole-unit expansion
-/

namespace SkewCoframeRigidity.UnitRestoration

open Matrix Polynomial

section Perm

variable {R : Type*} [CommRing R] {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l]
  [DecidableEq m]

theorem det_submatrix_perm (ι κ : l ≃ m) (B : Matrix m m R) :
    (B.submatrix ι κ).det = ((Equiv.Perm.sign (κ.trans ι.symm) : ℤˣ) : ℤ) • B.det := by
  have : B.submatrix ι κ = (B.submatrix ι ι).submatrix id (κ.trans ι.symm) := by
    ext a b; simp
  rw [this, Matrix.det_permute', Matrix.det_submatrix_equiv_self, zsmul_eq_mul]

/-- The adjugate of a matrix with rows and columns reindexed by two different bijections. -/
theorem adjugate_submatrix_perm (M : Matrix m m R) (ι κ : l ≃ m) (i j : m) :
    adjugate (M.submatrix ι κ) (κ.symm j) (ι.symm i) =
      ((Equiv.Perm.sign (κ.trans ι.symm) : ℤˣ) : ℤ) • adjugate M j i := by
  rw [adjugate_apply, adjugate_apply, ← det_submatrix_perm, Matrix.submatrix_updateRow_equiv]
  congr 2
  ext a
  simp [Pi.single_apply, Equiv.eq_symm_apply]

end Perm

section Field

open SkewCoframeRigidity.Coframe

variable {F : Type*} [Field F] {n : ℕ}

/-- The adjugate of `[[1, 0], [G, K]]` has a zero upper-right block and lower-right block
`adj K`. -/
theorem adjugate_fromBlocks_one {υ κ : Type*} [Fintype υ] [Fintype κ] [DecidableEq υ]
    [DecidableEq κ] (G : Matrix κ υ F) (K : Matrix κ κ F) (hK : K.det ≠ 0) :
    (∀ a b, adjugate (Matrix.fromBlocks (1 : Matrix υ υ F) 0 G K) (Sum.inl a) (Sum.inr b) = 0) ∧
    (∀ a b, adjugate (Matrix.fromBlocks (1 : Matrix υ υ F) 0 G K) (Sum.inr a) (Sum.inr b) =
      adjugate K a b) ∧
    (∀ a, adjugate (Matrix.fromBlocks (1 : Matrix υ υ F) 0 G K) (Sum.inl a) (Sum.inl a) =
      K.det) := by
  have hd : (Matrix.fromBlocks (1 : Matrix υ υ F) 0 G K).det = K.det := by
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
  have hinv := Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff (1 : Matrix υ υ F) G K
    (by simpa [Matrix.isUnit_iff_isUnit_det] using hK)
  rw [adjugate_eq_det_smul_inv _ (by rw [hd]; exact hK), hd, hinv]
  refine ⟨fun a b => by simp, fun a b => ?_, fun a => by simp⟩
  rw [adjugate_eq_det_smul_inv K hK]
  simp

theorem adjugate_diagonal_ite {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (i : ι) :
    ∏ l ∈ Finset.univ.erase i, (if p l then (1 : R[X]) else Polynomial.X) =
      Polynomial.X ^ ((Finset.univ.filter fun l => ¬ p l).card - if p i then 0 else 1) := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_erase]
  by_cases hp : p i
  · rw [Finset.erase_eq_of_notMem (by simp [hp])]; simp [hp]
  · rw [Finset.card_erase_of_mem (by simp [hp])]; simp [hp]

end Field

section Strip

open SkewCoframeRigidity.Coframe

variable {R : Type*} [CommRing R] {n : ℕ}

open scoped Classical in
/-- The scaled matrix with the core rows divided by `ε`. -/
noncomputable def rowStripped (h : ℕ → R) (row col : Fin n → ℤ) : Matrix (Fin n) (Fin n) R[X] :=
  Matrix.of fun i j => if i ∈ unitRows row col then scaledLetter h (row i - col j)
    else Polynomial.C (letterOf h (row i - col j))

open scoped Classical in
theorem scaledMatrix_eq_diagonal_mul (h : ℕ → R) (row col : Fin n → ℤ) :
    scaledMatrix h row col = Matrix.diagonal
      (fun i => if i ∈ unitRows row col then (1 : R[X]) else Polynomial.X) *
        rowStripped h row col := by
  ext i j
  rw [Matrix.diagonal_mul]
  by_cases hi : i ∈ unitRows row col
  · simp [rowStripped, hi, scaledMatrix]
  · have hne : row i - col j ≠ 0 := fun h0 => hi ⟨j, by omega⟩
    simp [rowStripped, hi, scaledMatrix, scaledLetter_of_ne h hne]

open scoped Classical in
/-- Dividing the core rows by `ε` divides the adjugate entry in column `j`, row `i` by
`ε^{c-1}` for a core row `i` and by `ε^c` for a unit row `i`, where `c` is the number of core
rows. -/
theorem adjugate_scaledMatrix (h : ℕ → R) (row col : Fin n → ℤ) (i j : Fin n) :
    adjugate (scaledMatrix h row col) j i = adjugate (rowStripped h row col) j i *
      Polynomial.X ^ ((Finset.univ.filter fun l => l ∉ unitRows row col).card -
        if i ∈ unitRows row col then 0 else 1) := by
  rw [scaledMatrix_eq_diagonal_mul, Matrix.adjugate_mul_distrib, Matrix.adjugate_diagonal,
    Matrix.mul_diagonal, adjugate_diagonal_ite]

open scoped Classical in
/-- The constant coefficients of the stripped matrix. -/
noncomputable def strippedConst (h : ℕ → R) (row col : Fin n → ℤ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i ∈ unitRows row col then (if row i = col j then 1 else 0)
    else letterOf h (row i - col j)

open scoped Classical in
theorem rowStripped_constantCoeff (h : ℕ → R) (row col : Fin n → ℤ) :
    (rowStripped h row col).map Polynomial.constantCoeff = strippedConst h row col := by
  ext i j
  by_cases hi : i ∈ unitRows row col
  · simp only [Matrix.map_apply, rowStripped, strippedConst, Matrix.of_apply, if_pos hi]
    rw [constantCoeff_scaledLetter]
    simp [sub_eq_zero]
  · simp [rowStripped, strippedConst, hi]

end Strip

section Expansion

open SkewCoframeRigidity.Coframe

variable {F : Type*} [Field F] {n : ℕ}

open scoped Classical in
/-- **The adjugate of the scaled matrix.**  Let `c` be the number of core rows.  Every entry in a
unit row or a unit column is divisible by `ε^c`, and the entry in a core column `j` and core row
`i` is `ε^{c-1} (σ adj K + ε q)` where `K` is the core matrix and `σ` the sorting sign. -/
theorem adjugate_scaledMatrix_expansion (h : ℕ → F) (row col : Fin n → ℤ)
    (hr : Function.Injective row) (hc : Function.Injective col)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col})
    (hφ : ∀ i, row i.1 = col (φ i).1)
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col})
    (hK : (coreMatrix h row col e).det ≠ 0) :
    ∃ σ : ℤˣ, ∀ i j : Fin n,
      ((i ∈ unitRows row col ∨ j ∈ unitCols row col) →
        ∃ q : F[X], adjugate (scaledMatrix h row col) j i =
          Polynomial.X ^ (Finset.univ.filter fun l => l ∉ unitRows row col).card * q) ∧
      (∀ (hi : i ∉ unitRows row col) (hj : j ∉ unitCols row col), ∃ q : F[X],
        adjugate (scaledMatrix h row col) j i =
          Polynomial.X ^ ((Finset.univ.filter fun l => l ∉ unitRows row col).card - 1) *
            (Polynomial.C (((σ : ℤ) : F) * adjugate (coreMatrix h row col e)
              (e.symm ⟨j, hj⟩) ⟨i, hi⟩) + Polynomial.X * q)) ∧
      (∀ (hi : i ∈ unitRows row col) (hj : j ∈ unitCols row col), j = (φ ⟨i, hi⟩).1 →
        ∃ q : F[X], adjugate (scaledMatrix h row col) j i =
          Polynomial.X ^ (Finset.univ.filter fun l => l ∉ unitRows row col).card *
            (Polynomial.C (((σ : ℤ) : F) * (coreMatrix h row col e).det) +
              Polynomial.X * q)) := by
  set ι := Equiv.sumCompl (fun i => i ∈ unitRows row col) with hι
  set κ := (Equiv.sumCongr φ e).trans (Equiv.sumCompl (fun j => j ∈ unitCols row col)) with hκ
  have hsub : (strippedConst h row col).submatrix ι κ =
      Matrix.fromBlocks (1 : Matrix {i // i ∈ unitRows row col} {i // i ∈ unitRows row col} F) 0
        (unitG h row col φ) (coreMatrix h row col e) := by
    refine Matrix.ext fun a b => ?_
    rcases a with i | r <;> rcases b with j | c
    · by_cases hij : i = j
      · subst hij
        simp [strippedConst, hι, hκ, hφ i]
      · have hne : row i.1 ≠ col (φ j).1 := by
          intro h0
          apply hij
          have h1 : col (φ i).1 = col (φ j).1 := by rw [← hφ i]; exact h0
          exact φ.injective (Subtype.ext (hc h1))
        simp [strippedConst, hι, hκ, hne, Matrix.one_apply_ne hij]
    · have hne : row i.1 ≠ col (e c).1 := fun h0 => (e c).2 ⟨i.1, h0⟩
      simp [strippedConst, hι, hκ, hne]
    · simp [strippedConst, hι, hκ, unitG, r.2]
    · simp [strippedConst, hι, hκ, coreMatrix, r.2]
  obtain ⟨hB1, hB2, hB3⟩ := adjugate_fromBlocks_one (unitG h row col φ) (coreMatrix h row col e) hK
  refine ⟨Equiv.Perm.sign (κ.trans ι.symm), fun i j => ?_⟩
  have hsq : ((Equiv.Perm.sign (κ.trans ι.symm) : ℤˣ) : ℤ) *
      ((Equiv.Perm.sign (κ.trans ι.symm) : ℤˣ) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (κ.trans ι.symm)) with h1 | h1 <;> simp [h1]
  have hN0 : adjugate (strippedConst h row col) j i =
      ((Equiv.Perm.sign (κ.trans ι.symm) : ℤˣ) : ℤ) •
        adjugate (Matrix.fromBlocks (1 : Matrix {i // i ∈ unitRows row col}
          {i // i ∈ unitRows row col} F) 0 (unitG h row col φ) (coreMatrix h row col e))
          (κ.symm j) (ι.symm i) := by
    rw [← hsub, adjugate_submatrix_perm, smul_smul, hsq, one_smul]
  have hconst : Polynomial.constantCoeff (adjugate (rowStripped h row col) j i) =
      adjugate (strippedConst h row col) j i := by
    have := congrFun (congrFun (RingHom.map_adjugate (Polynomial.constantCoeff (R := F))
      (rowStripped h row col)) j) i
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, rowStripped_constantCoeff] at this
    simpa using this
  have hdvd : ∃ q : F[X], adjugate (rowStripped h row col) j i =
      Polynomial.C (adjugate (strippedConst h row col) j i) + Polynomial.X * q := by
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := adjugate (rowStripped h row col) j i)
    refine ⟨q, ?_⟩
    rw [← hconst, Polynomial.constantCoeff_apply]
    linear_combination hq
  obtain ⟨q, hq⟩ := hdvd
  have hS := adjugate_scaledMatrix h row col i j
  refine ⟨?_, fun hi hj => ?_, fun hi hj hji => ?_⟩
  · intro hij
    by_cases hi : i ∈ unitRows row col
    · exact ⟨_, by rw [hS, if_pos hi, Nat.sub_zero, mul_comm]⟩
    · have hj : j ∈ unitCols row col := hij.resolve_left hi
      have hk1 : ι.symm i = Sum.inr ⟨i, hi⟩ := by simp [hι, hi]
      have hk2 : κ.symm j = Sum.inl (φ.symm ⟨j, hj⟩) := by simp [hκ, hj]
      have h0 : adjugate (strippedConst h row col) j i = 0 := by
        rw [hN0, hk1, hk2, hB1, smul_zero]
      have hcpos : 0 < (Finset.univ.filter fun l => l ∉ unitRows row col).card :=
        Finset.card_pos.mpr ⟨i, by simp [hi]⟩
      refine ⟨q, ?_⟩
      rw [hS, if_neg hi, hq, h0, map_zero, zero_add, mul_comm,
        ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hcpos]
  · have hk1 : ι.symm i = Sum.inr ⟨i, hi⟩ := by simp [hι, hi]
    have hk2 : κ.symm j = Sum.inr (e.symm ⟨j, hj⟩) := by simp [hκ, hj]
    have h0 : adjugate (strippedConst h row col) j i =
        ((Equiv.Perm.sign (κ.trans ι.symm) : ℤˣ) : ℤ) •
          adjugate (coreMatrix h row col e) (e.symm ⟨j, hj⟩) ⟨i, hi⟩ := by
      rw [hN0, hk1, hk2, hB2]
    refine ⟨q, ?_⟩
    rw [hS, if_neg hi, hq, h0, zsmul_eq_mul, mul_comm]
  · have hk1 : ι.symm i = Sum.inl ⟨i, hi⟩ := by simp [hι, hi]
    have hk2 : κ.symm j = Sum.inl ⟨i, hi⟩ := by
      have : φ.symm ⟨j, hj⟩ = ⟨i, hi⟩ := by
        rw [Equiv.symm_apply_eq]; exact Subtype.ext hji
      simp [hκ, hj, this]
    have h0 : adjugate (strippedConst h row col) j i =
        ((Equiv.Perm.sign (κ.trans ι.symm) : ℤˣ) : ℤ) • (coreMatrix h row col e).det := by
      rw [hN0, hk1, hk2, hB3]
    refine ⟨q, ?_⟩
    rw [hS, if_pos hi, hq, h0, zsmul_eq_mul, Nat.sub_zero]
    ring

end Expansion

end SkewCoframeRigidity.UnitRestoration
