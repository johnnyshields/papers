/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fin.Rev
import Mathlib
import Vendor.AlgebraicCombinatorics.CauchyBinet

/-!
# Formal two-series word matrices

Formal-series and Toeplitz algebra for "Reversal pairs on the locus"
(`subsec:locus-family`, `lem:two-series-reversal`).  Quotients are multiplication
by the inverse of a unit with constant coefficient one.  Toeplitz elimination,
simultaneous coordinate deletion with its computed sign, and sorted minor
reflection prove the full word-minor formula and determinant reversal.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace TwoSeries

open scoped BigOperators

variable {R : Type*} [CommRing R] {N ell : ℕ}

/-- A series coefficient at a signed index, retaining the negative-index zero convention. -/
noncomputable def signedCoeff (A : PowerSeries R) (i : ℤ) : R :=
  if 0 ≤ i then PowerSeries.coeff i.toNat A else 0

/-- A right-shifted coefficient row. -/
noncomputable def shiftedRow (A : PowerSeries R) (s : ℕ) (j : Fin N) : R :=
  if s ≤ j.val then PowerSeries.coeff (j.val - s) A else 0

/-- Upper triangular truncation of the Toeplitz matrix of a formal series. -/
noncomputable def toeplitz (A : PowerSeries R) (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => shiftedRow A i.val j

/-- Formal division by a series with constant coefficient one uses its genuine unit inverse. -/
noncomputable def quotient (A B : PowerSeries R) : PowerSeries R :=
  B * PowerSeries.invOfUnit A 1

theorem quotient_mul (A B : PowerSeries R) (hA : PowerSeries.constantCoeff A = 1) :
    quotient A B * A = B := by
  rw [quotient, mul_assoc, PowerSeries.invOfUnit_mul A 1 (by simpa using hA), mul_one]

theorem series_mul_quotient (A B : PowerSeries R) (hA : PowerSeries.constantCoeff A = 1) :
    A * quotient A B = B := by
  rw [mul_comm]
  exact quotient_mul A B hA

/-- Finite row convolution agrees with formal-series multiplication. -/
theorem shiftedRow_mul_toeplitz (A B : PowerSeries R) (s : ℕ) (j : Fin N) :
    (∑ i : Fin N, shiftedRow A s i * toeplitz B N i j) = shiftedRow (A * B) s j := by
  classical
  by_cases hs : s ≤ j.val
  · let S : Finset (Fin N) := Finset.univ.filter (fun i => s ≤ i.val ∧ i.val ≤ j.val)
    have hrestrict :
        (∑ i : Fin N, shiftedRow A s i * toeplitz B N i j) =
          ∑ i ∈ S, shiftedRow A s i * toeplitz B N i j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
      simp only [shiftedRow, toeplitz, Matrix.of_apply]
      split_ifs with ha hb <;> simp_all
    rw [hrestrict]
    simp only [shiftedRow, ite_eq_left hs, PowerSeries.coeff_mul]
    refine Finset.sum_bij (fun i _ => (i.val - s, j.val - i.val)) ?_ ?_ ?_ ?_
    · intro i hi
      have hb : s ≤ i.val ∧ i.val ≤ j.val := by simpa [S] using hi
      apply Finset.HasAntidiagonal.mem_antidiagonal.mpr
      omega
    · intro i hi l hl hil
      have hbi : s ≤ i.val ∧ i.val ≤ j.val := by simpa [S] using hi
      have hbl : s ≤ l.val ∧ l.val ≤ j.val := by simpa [S] using hl
      have hp := congrArg Prod.fst hil
      apply Fin.ext
      omega
    · intro p hp
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hj := j.isLt
      let i : Fin N := ⟨s + p.1, by omega⟩
      refine ⟨i, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [i]
        constructor <;> omega
      · apply Prod.ext <;> dsimp [i] <;> omega
    · intro i hi
      have hb : s ≤ i.val ∧ i.val ≤ j.val := by simpa [S] using hi
      simp only [toeplitz, Matrix.of_apply, shiftedRow,
        ite_eq_left hb.1, ite_eq_left hb.2]
  · have hj : j.val < s := by omega
    simp only [shiftedRow, ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro i _
    simp only [shiftedRow, toeplitz, Matrix.of_apply]
    split_ifs <;> simp_all
    all_goals omega

theorem toeplitz_mul (A B : PowerSeries R) : toeplitz A N * toeplitz B N = toeplitz (A * B) N := by
  ext i j
  exact shiftedRow_mul_toeplitz A B i.val j

@[simp] theorem toeplitz_one : toeplitz (1 : PowerSeries R) N = 1 := by
  ext i j
  change (if i.val ≤ j.val then PowerSeries.coeff (j.val - i.val) (1 : PowerSeries R)
    else 0) = if i = j then 1 else 0
  by_cases h : i = j
  · subst j
    simp only [le_refl, ite_true, Nat.sub_self, PowerSeries.coeff_zero_one]
  · rw [ite_eq_right h]
    have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
    by_cases hij : i.val ≤ j.val
    · have hd : j.val - i.val ≠ 0 := by omega
      rw [ite_eq_left hij, PowerSeries.coeff_one, ite_eq_right hd]
    · rw [ite_eq_right hij]

/-- Triangular Toeplitz determinant is the power of the constant coefficient. -/
theorem det_toeplitz (A : PowerSeries R) : (toeplitz A N).det =
    (PowerSeries.constantCoeff A) ^ N := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [toeplitz, shiftedRow, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro i j hij
    have h : ¬ i.val ≤ j.val := by change j.val < i.val at hij; omega
    change (if i.val ≤ j.val then PowerSeries.coeff (j.val - i.val) A else 0) = 0
    rw [ite_eq_right h]

theorem toeplitz_unit_inverse (A : PowerSeries R) (hA : PowerSeries.constantCoeff A = 1) :
    toeplitz A N * toeplitz (PowerSeries.invOfUnit A 1) N = 1 := by
  rw [toeplitz_mul, PowerSeries.mul_invOfUnit A 1 (by simpa using hA), toeplitz_one]

theorem toeplitz_inverse_det (A : PowerSeries R) :
    (toeplitz (PowerSeries.invOfUnit A 1) N).det = 1 := by
  rw [det_toeplitz]
  simp

/-- A Boolean letter is `true` for the B series and `false` for the A series. -/
noncomputable def wordMatrix (A B : PowerSeries R) (x : Fin ell → Bool) :
    Matrix (Fin (ell + 2)) (Fin (ell + 2)) R :=
  Matrix.of fun i j => Fin.cases (shiftedRow B 0 j)
    (fun i => Fin.cases (shiftedRow A 0 j)
      (fun t => shiftedRow (if x t then B else A) (t.val + 1) j) i) i

/-- The word matrix after elimination by the unit inverse of A. -/
noncomputable def normalizedWordMatrix (Q : PowerSeries R) (x : Fin ell → Bool) :
    Matrix (Fin (ell + 2)) (Fin (ell + 2)) R :=
  wordMatrix 1 Q x

/-- Actual right multiplication turns A rows into coordinates and B rows into Q shifts. -/
theorem wordMatrix_mul_inverse (A B : PowerSeries R) (hA : PowerSeries.constantCoeff A = 1)
    (x : Fin ell → Bool) :
    wordMatrix A B x * toeplitz (PowerSeries.invOfUnit A 1) (ell + 2) =
      normalizedWordMatrix (quotient A B) x := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    simp only [wordMatrix, normalizedWordMatrix, Matrix.mul_apply, Matrix.of_apply,
      Fin.cases_zero]
    exact shiftedRow_mul_toeplitz B (PowerSeries.invOfUnit A 1) 0 j
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      simp only [wordMatrix, normalizedWordMatrix, Matrix.mul_apply, Matrix.of_apply,
        Fin.cases_succ, Fin.cases_zero]
      simpa only [PowerSeries.mul_invOfUnit A 1 (by simpa using hA)] using
        shiftedRow_mul_toeplitz A (PowerSeries.invOfUnit A 1) 0 j
    | succ i =>
      simp only [wordMatrix, normalizedWordMatrix, Matrix.mul_apply, Matrix.of_apply,
        Fin.cases_succ]
      cases hx : x i
      · simp only [Bool.false_eq_true, ite_false]
        simpa only [PowerSeries.mul_invOfUnit A 1 (by simpa using hA)] using
          shiftedRow_mul_toeplitz A (PowerSeries.invOfUnit A 1) (i.val + 1) j
      · simp only [ite_true]
        exact shiftedRow_mul_toeplitz B (PowerSeries.invOfUnit A 1) (i.val + 1) j

theorem wordMatrix_det_normalized (A B : PowerSeries R)
    (hA : PowerSeries.constantCoeff A = 1) (x : Fin ell → Bool) :
    (wordMatrix A B x).det = (normalizedWordMatrix (quotient A B) x).det := by
  rw [← wordMatrix_mul_inverse A B hA x, Matrix.det_mul, toeplitz_inverse_det, mul_one]

/-- A Toeplitz minor expressed on two equally sized signed index lists. -/
noncomputable def coefficientMinor (Q : PowerSeries R) (r c : Fin N → ℤ) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => signedCoeff Q (c j - r i)

/-- Reflection swaps index lists and reverses both orders; both determinant signs cancel. -/
theorem coefficientMinor_reflection (Q : PowerSeries R) (r c : Fin N → ℤ) (L : ℤ) :
    (coefficientMinor Q (fun i => L - c i.rev) (fun i => L - r i.rev)).det =
      (coefficientMinor Q r c).det := by
  have he : coefficientMinor Q (fun i => L - c i.rev) (fun i => L - r i.rev) =
      (coefficientMinor Q r c).transpose.submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [coefficientMinor, Matrix.of_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, Fin.revPerm_apply]
    congr 1
    ring
  rw [he, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

/-- Deleting a coordinate row has its exact Laplace sign, with no nonzero assumption. -/
theorem coordinate_row_det {s : ℕ} (M : Matrix (Fin (s + 1)) (Fin (s + 1)) R)
    (r c : Fin (s + 1)) (hrow : ∀ j, M r j = if j = c then 1 else 0) :
    M.det = (-1 : R) ^ (r.val + c.val) * (M.submatrix r.succAbove c.succAbove).det := by
  classical
  rw [Matrix.det_succ_row M r]
  simp_rw [hrow]
  simp

theorem normalizedWordMatrix_first_coordinate (Q : PowerSeries R) (x : Fin ell → Bool)
    (j : Fin (ell + 2)) :
    normalizedWordMatrix Q x (0 : Fin (ell + 1)).succ j =
      if j = 0 then 1 else 0 := by
  change shiftedRow (1 : PowerSeries R) 0 j = _
  have h := congrArg (fun M : Matrix (Fin (ell + 2)) (Fin (ell + 2)) R => M 0 j)
    (toeplitz_one (R := R) (N := ell + 2))
  change shiftedRow (1 : PowerSeries R) 0 j = if (0 : Fin (ell + 2)) = j then 1 else 0 at h
  simpa only [eq_comm] using h

theorem normalizedWordMatrix_letter_coordinate (Q : PowerSeries R) (x : Fin ell → Bool)
    (i : Fin ell) (hi : x i = false) (j : Fin (ell + 2)) :
    normalizedWordMatrix Q x i.succ.succ j =
      if j = i.succ.castSucc then 1 else 0 := by
  change shiftedRow (if x i then Q else 1) (i.val + 1) j = _
  simp only [hi, Bool.false_eq_true, ite_false]
  have h := congrArg
    (fun M : Matrix (Fin (ell + 2)) (Fin (ell + 2)) R => M i.succ.castSucc j)
    (toeplitz_one (R := R) (N := ell + 2))
  change shiftedRow (1 : PowerSeries R) (i.val + 1) j =
    if i.succ.castSucc = j then 1 else 0 at h
  simpa only [eq_comm] using h

/-- The first A row contributes exactly one negative sign. -/
theorem normalizedWordMatrix_delete_first (Q : PowerSeries R) (x : Fin ell → Bool) :
    (normalizedWordMatrix Q x).det =
      -((normalizedWordMatrix Q x).submatrix
        (0 : Fin (ell + 1)).succ.succAbove (0 : Fin (ell + 2)).succAbove).det := by
  rw [coordinate_row_det _ _ 0 (normalizedWordMatrix_first_coordinate Q x)]
  simp

/-- Coordinate columns, embedded without shifting into the full matrix. -/
def coordinateColumns {s : ℕ} (S : Finset (Fin s)) : Finset (Fin (s + 1)) :=
  S.map ⟨Fin.castSucc, by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (s + 1) => k.val) h)⟩

/-- The coordinate rows sit one index after their corresponding columns. -/
def coordinateRows {s : ℕ} (S : Finset (Fin s)) : Finset (Fin (s + 1)) :=
  S.map (Fin.succEmb s)

/-- Simultaneous coordinate-row deletion, with the full computed sign.
**Differs from the paper's route.** Extracts the unique surviving minor through
the formalized generalized Laplace identity instead of deleting coordinate rows serially. -/
theorem coordinate_rows_det {s : ℕ} (M : Matrix (Fin (s + 1)) (Fin (s + 1)) R)
    (S : Finset (Fin s))
    (hrow : ∀ k ∈ S, ∀ j, M k.succ j = if j = k.castSucc then 1 else 0) :
    M.det = (-1 : R) ^ S.card *
      AlgebraicCombinatorics.CauchyBinet.submatrixDet M
        (coordinateRows S)ᶜ (coordinateColumns S)ᶜ (by
          simp [coordinateRows, coordinateColumns, Finset.card_compl]) := by
  classical
  let P := coordinateColumns S
  let Q := coordinateRows S
  have hcard : P.card = Q.card := by simp [P, Q, coordinateColumns, coordinateRows]
  have hnonmapping : ∀ σ : Equiv.Perm (Fin (s + 1)),
      σ ∉ AlgebraicCombinatorics.CauchyBinet.permsMapping P Q →
      (∏ i, M (σ i) i) = 0 := by
    intro σ hσ
    by_contra hprod
    have hpoint : ∀ k ∈ S, σ k.castSucc = k.succ := by
      intro k hk
      by_contra hneq
      let i := σ.symm k.succ
      have hi : i ≠ k.castSucc := by
        intro he
        apply hneq
        have h := congrArg σ he
        simpa [i] using h.symm
      have hz : M (σ i) i = 0 := by
        simp only [i, Equiv.apply_symm_apply]
        rw [hrow k hk, ite_eq_right hi]
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hz)
    apply hσ
    simp only [AlgebraicCombinatorics.CauchyBinet.permsMapping,
      Finset.mem_filter, Finset.mem_univ, true_and]
    ext z
    simp only [AlgebraicCombinatorics.CauchyBinet.imageFinset, P, Q, coordinateColumns,
      coordinateRows, Finset.mem_map, Function.Embedding.coeFn_mk, Fin.coe_succEmb]
    constructor
    · rintro ⟨p, ⟨k, hk, rfl⟩, hp⟩
      exact ⟨k, hk, (hpoint k hk).symm.trans hp⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.castSucc, ⟨k, hk, rfl⟩, hpoint k hk⟩
  have hrestrict : M.det =
      ∑ σ ∈ AlgebraicCombinatorics.CauchyBinet.permsMapping P Q,
        Equiv.Perm.sign σ • ((∏ i ∈ P, M (σ i) i) * ∏ i ∈ Pᶜ, M (σ i) i) := by
    rw [Matrix.det_apply]
    simp_rw [Finset.prod_mul_prod_compl]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro σ _ hσ
    rw [hnonmapping σ hσ, smul_zero]
  rw [hrestrict, AlgebraicCombinatorics.CauchyBinet.sum_perms_mapping_eq_det_product M M P Q hcard]
  have hminor : AlgebraicCombinatorics.CauchyBinet.submatrixDet M Q P hcard.symm = 1 := by
    unfold AlgebraicCombinatorics.CauchyBinet.submatrixDet
    let f : Fin Q.card → Fin s := S.orderEmbOfFin (by simp [Q, coordinateRows])
    have hQ : (fun i : Fin Q.card => (f i).succ) = Q.orderEmbOfFin rfl := by
      apply Finset.orderEmbOfFin_unique
      · intro i
        exact Finset.mem_map.mpr ⟨f i, S.orderEmbOfFin_mem _ i, rfl⟩
      · intro i j hij
        have h := (S.orderEmbOfFin (by simp [Q, coordinateRows])).strictMono hij
        change (f i).val + 1 < (f j).val + 1
        change (f i).val < (f j).val at h
        omega
    have hP : (fun i : Fin Q.card => (f i).castSucc) =
        P.orderEmbOfFin hcard := by
      apply Finset.orderEmbOfFin_unique
      · intro i
        exact Finset.mem_map.mpr ⟨f i, S.orderEmbOfFin_mem _ i, rfl⟩
      · exact (S.orderEmbOfFin (by simp [Q, coordinateRows])).strictMono
    have hm : M.submatrix (Q.orderEmbOfFin rfl)
        (P.orderEmbOfFin hcard) = 1 := by
      ext i j
      rw [Matrix.submatrix_apply, ← congrFun hQ i, ← congrFun hP j]
      rw [hrow (f i) (S.orderEmbOfFin_mem _ i)]
      simp only [Matrix.one_apply, Fin.castSucc_inj]
      have hf : (f j = f i) ↔ j = i := (S.orderEmbOfFin _).injective.eq_iff
      simp [hf, eq_comm]
    rw [hm, Matrix.det_one]
  have hsum : AlgebraicCombinatorics.CauchyBinet.finsetSumFin P +
      AlgebraicCombinatorics.CauchyBinet.finsetSumFin Q =
        2 * (∑ k ∈ S, k.val) + S.card := by
    have hPsum : AlgebraicCombinatorics.CauchyBinet.finsetSumFin P = ∑ k ∈ S, k.val := by
      dsimp only [P, coordinateColumns, AlgebraicCombinatorics.CauchyBinet.finsetSumFin]
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro k _
      rfl
    have hQsum : AlgebraicCombinatorics.CauchyBinet.finsetSumFin Q =
        (∑ k ∈ S, k.val) + S.card := by
      dsimp only [Q, coordinateRows, AlgebraicCombinatorics.CauchyBinet.finsetSumFin]
      rw [Finset.sum_map]
      calc
        (∑ k ∈ S, ((Fin.succEmb s) k).val) = ∑ k ∈ S, (k.val + 1) := by
          apply Finset.sum_congr rfl
          intro k _
          rfl
        _ = (∑ k ∈ S, k.val) + S.card := by
          rw [Finset.sum_add_distrib]
          simp
    rw [hPsum, hQsum]
    omega
  rw [hminor, mul_one, hsum, pow_add, pow_mul]
  norm_num
  rfl

/-- Pivots of all coordinate rows after Toeplitz elimination. -/
noncomputable def wordCoordinates (x : Fin ell → Bool) : Finset (Fin (ell + 1)) := by
  classical
  exact Finset.univ.filter (fun k => Fin.cases (motive := fun _ => Prop)
    True (fun i => x i = false) k)

@[simp] theorem mem_wordCoordinates_zero (x : Fin ell → Bool) :
    (0 : Fin (ell + 1)) ∈ wordCoordinates x := by simp [wordCoordinates]

@[simp] theorem mem_wordCoordinates_succ (x : Fin ell → Bool) (i : Fin ell) :
    i.succ ∈ wordCoordinates x ↔ x i = false := by simp [wordCoordinates]

/-- Rows retained after removing every coordinate pivot row. -/
noncomputable def residualRows (x : Fin ell → Bool) : Finset (Fin (ell + 2)) :=
  (coordinateRows (wordCoordinates x))ᶜ

/-- Columns retained after removing every coordinate pivot column. -/
noncomputable def residualColumns (x : Fin ell → Bool) : Finset (Fin (ell + 2)) :=
  (coordinateColumns (wordCoordinates x))ᶜ

theorem residual_card_eq (x : Fin ell → Bool) :
    (residualRows x).card = (residualColumns x).card := by
  simp [residualRows, residualColumns, coordinateRows, coordinateColumns, Finset.card_compl]

@[simp] theorem mem_residualRows_succ (x : Fin ell → Bool) (i : Fin (ell + 1)) :
    i.succ ∈ residualRows x ↔ i ∉ wordCoordinates x := by
  simp [residualRows, coordinateRows]

@[simp] theorem mem_residualColumns_castSucc (x : Fin ell → Bool) (i : Fin (ell + 1)) :
    i.castSucc ∈ residualColumns x ↔ i ∉ wordCoordinates x := by
  simp only [residualColumns, Finset.mem_compl]
  constructor
  · intro h hi
    exact h (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro h hi
    obtain ⟨k, hk, he⟩ := Finset.mem_map.mp hi
    have hki : k = i := Fin.castSucc_inj.mp he
    subst k
    exact h hk

@[simp] theorem mem_residualRows_zero (x : Fin ell → Bool) :
    (0 : Fin (ell + 2)) ∈ residualRows x := by
  simp only [residualRows, Finset.mem_compl]
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  have hval := congrArg Fin.val hi
  change i.val + 1 = 0 at hval
  omega

@[simp] theorem mem_residualColumns_last (x : Fin ell → Bool) :
    Fin.last (ell + 1) ∈ residualColumns x := by
  simp only [residualColumns, Finset.mem_compl]
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  have hval := congrArg Fin.val hi
  have hib := i.isLt
  change i.val = ell + 1 at hval
  omega

theorem residualColumns_pos (x : Fin ell → Bool) (c : Fin (ell + 2))
    (hc : c ∈ residualColumns x) : 0 < c.val := by
  by_contra h
  have he : c = (0 : Fin (ell + 1)).castSucc := by
    apply Fin.ext
    change c.val = 0
    omega
  rw [he, mem_residualColumns_castSucc] at hc
  exact hc (mem_wordCoordinates_zero x)

theorem residualRows_ne_first (x : Fin ell → Bool) (r : Fin (ell + 2))
    (hr : r ∈ residualRows x) : r.val ≠ 1 := by
  intro he
  have h : r = (0 : Fin (ell + 1)).succ := Fin.ext (by simpa using he)
  rw [h, mem_residualRows_succ] at hr
  exact hr (mem_wordCoordinates_zero x)

/-- Reversal of the binary coefficient-series word. -/
def wordReverse (x : Fin ell → Bool) (i : Fin ell) : Bool := x i.rev

@[simp] theorem wordReverse_reverse (x : Fin ell → Bool) : wordReverse (wordReverse x) = x := by
  funext i
  simp [wordReverse]

/-- The coefficient shift carried by an undeleted row. -/
def rowShift (r : Fin (ell + 2)) : ℤ := if r.val = 0 then 0 else (r.val : ℤ) - 1

@[simp] theorem rowShift_succ_succ (i : Fin ell) :
    rowShift i.succ.succ = (i.val : ℤ) + 1 := by
  have hp : (i.succ.succ).val ≠ 0 := by change i.val + 1 + 1 ≠ 0; omega
  rw [rowShift, ite_eq_right hp]
  change ((i.val + 1 + 1 : ℕ) : ℤ) - 1 = (i.val : ℤ) + 1
  push_cast
  ring

/-- The reflected residual row associated to a retained coefficient column. -/
def reflectColumnRow (c : Fin (ell + 2)) : Fin (ell + 2) :=
  if hc : c.val = 0 then 0 else if hl : c.val = ell + 1 then 0
  else ⟨ell + 2 - c.val, by have hb := c.isLt; omega⟩

/-- The reflected retained column associated to a residual coefficient row. -/
def reflectRowColumn (r : Fin (ell + 2)) : Fin (ell + 2) :=
  if hr : r.val = 0 then Fin.last (ell + 1)
  else ⟨ell + 2 - r.val, by have h := r.isLt; omega⟩

theorem reflectColumnRow_mem (x : Fin ell → Bool) (c : Fin (ell + 2))
    (hc : c ∈ residualColumns x) :
    reflectColumnRow c ∈ residualRows (wordReverse x) := by
  have hp := residualColumns_pos x c hc
  have hcb := c.isLt
  by_cases hl : c.val = ell + 1
  · simp [reflectColumnRow, hl]
  · have hi : c.val - 1 < ell := by omega
    let i : Fin ell := ⟨c.val - 1, hi⟩
    have he : c = i.succ.castSucc := by apply Fin.ext; dsimp [i]; omega
    have hx : x i = true := by
      rw [he, mem_residualColumns_castSucc, mem_wordCoordinates_succ] at hc
      cases h : x i <;> simp_all
    have hr : reflectColumnRow c = i.rev.succ.succ := by
      apply Fin.ext
      simp only [reflectColumnRow, dite_eq_right (ne_of_gt hp), dite_eq_right hl,
        Fin.val_succ]
      change ell + 2 - c.val = ell - (i.val + 1) + 1 + 1
      dsimp [i]
      omega
    rw [hr, mem_residualRows_succ, mem_wordCoordinates_succ]
    simp [wordReverse, hx]

theorem reflectRowColumn_mem (x : Fin ell → Bool) (r : Fin (ell + 2))
    (hr : r ∈ residualRows x) :
    reflectRowColumn r ∈ residualColumns (wordReverse x) := by
  have hn := residualRows_ne_first x r hr
  have hrb := r.isLt
  by_cases h0 : r.val = 0
  · simp [reflectRowColumn, h0]
  · have hi : r.val - 2 < ell := by omega
    let i : Fin ell := ⟨r.val - 2, hi⟩
    have he : r = i.succ.succ := by apply Fin.ext; dsimp [i]; omega
    have hx : x i = true := by
      rw [he, mem_residualRows_succ, mem_wordCoordinates_succ] at hr
      cases h : x i <;> simp_all
    have hc : reflectRowColumn r = i.rev.succ.castSucc := by
      apply Fin.ext
      simp only [reflectRowColumn, dite_eq_right h0, Fin.val_castSucc, Fin.val_succ]
      change ell + 2 - r.val = ell - (i.val + 1) + 1
      dsimp [i]
      omega
    rw [hc, mem_residualColumns_castSucc, mem_wordCoordinates_succ]
    simp [wordReverse, hx]

theorem reflectRowColumn_reflectColumnRow (x : Fin ell → Bool) (c : Fin (ell + 2))
    (hc : c ∈ residualColumns x) : reflectRowColumn (reflectColumnRow c) = c := by
  have hp := residualColumns_pos x c hc
  have hb := c.isLt
  by_cases hl : c.val = ell + 1
  · have hf : reflectColumnRow c = 0 := by
      rw [reflectColumnRow, dite_eq_right (ne_of_gt hp), dite_eq_left hl]
    rw [hf, reflectRowColumn,
      dite_eq_left (show (0 : Fin (ell + 2)).val = 0 by simp)]
    apply Fin.ext
    change ell + 1 = c.val
    omega
  · have hz : (reflectColumnRow c).val ≠ 0 := by
      rw [reflectColumnRow, dite_eq_right (ne_of_gt hp), dite_eq_right hl]
      change ell + 2 - c.val ≠ 0
      omega
    rw [reflectRowColumn, dite_eq_right hz]
    apply Fin.ext
    change ell + 2 - (reflectColumnRow c).val = c.val
    rw [reflectColumnRow, dite_eq_right (ne_of_gt hp), dite_eq_right hl]
    change ell + 2 - (ell + 2 - c.val) = c.val
    omega

theorem reflectColumnRow_reflectRowColumn (x : Fin ell → Bool) (r : Fin (ell + 2))
    (hr : r ∈ residualRows x) : reflectColumnRow (reflectRowColumn r) = r := by
  have hn := residualRows_ne_first x r hr
  have hb := r.isLt
  by_cases h0 : r.val = 0
  · have hr0 : r = 0 := by apply Fin.ext; change r.val = 0; exact h0
    rw [reflectRowColumn, dite_eq_left h0, reflectColumnRow,
      dite_eq_right (show (Fin.last (ell + 1)).val ≠ 0 by change ell + 1 ≠ 0; omega),
      dite_eq_left (show (Fin.last (ell + 1)).val = ell + 1 from rfl)]
    exact hr0.symm
  · have hc0 : (reflectRowColumn r).val ≠ 0 := by
      rw [reflectRowColumn, dite_eq_right h0]
      change ell + 2 - r.val ≠ 0
      omega
    have hcL : (reflectRowColumn r).val ≠ ell + 1 := by
      rw [reflectRowColumn, dite_eq_right h0]
      change ell + 2 - r.val ≠ ell + 1
      omega
    rw [reflectColumnRow, dite_eq_right hc0, dite_eq_right hcL]
    apply Fin.ext
    change ell + 2 - (reflectRowColumn r).val = r.val
    rw [reflectRowColumn, dite_eq_right h0]
    change ell + 2 - (ell + 2 - r.val) = r.val
    omega

theorem reflection_card (x : Fin ell → Bool) :
    (residualRows (wordReverse x)).card = (residualColumns x).card := by
  classical
  symm
  refine Finset.card_bij (fun c _ => reflectColumnRow c) ?_ ?_ ?_
  · exact reflectColumnRow_mem x
  · intro c hc d hd he
    have h := congrArg reflectRowColumn he
    rwa [reflectRowColumn_reflectColumnRow x c hc, reflectRowColumn_reflectColumnRow x d hd] at h
  · intro r hr
    refine ⟨reflectRowColumn r, ?_, ?_⟩
    · simpa using reflectRowColumn_mem (wordReverse x) r hr
    · exact reflectColumnRow_reflectRowColumn (wordReverse x) r hr

theorem reflectColumnRow_strictAnti (x : Fin ell → Bool) (c d : Fin (ell + 2))
    (hc : c ∈ residualColumns x) (hd : d ∈ residualColumns x) (hcd : c < d) :
    reflectColumnRow d < reflectColumnRow c := by
  have hcp := residualColumns_pos x c hc
  have hdp := residualColumns_pos x d hd
  have hcb := c.isLt
  have hdb := d.isLt
  have hval : c.val < d.val := hcd
  change (reflectColumnRow d).val < (reflectColumnRow c).val
  unfold reflectColumnRow
  split_ifs <;> simp_all <;> omega

theorem reflectRowColumn_strictAnti (x : Fin ell → Bool) (r s : Fin (ell + 2))
    (hr : r ∈ residualRows x) (hs : s ∈ residualRows x) (hrs : r < s) :
    reflectRowColumn s < reflectRowColumn r := by
  have hrn := residualRows_ne_first x r hr
  have hsn := residualRows_ne_first x s hs
  have hrb := r.isLt
  have hsb := s.isLt
  have hval : r.val < s.val := hrs
  change (reflectRowColumn s).val < (reflectRowColumn r).val
  unfold reflectRowColumn
  split_ifs <;> simp_all <;> omega

theorem rowShift_reflectColumnRow (x : Fin ell → Bool) (c : Fin (ell + 2))
    (hc : c ∈ residualColumns x) :
    rowShift (reflectColumnRow c) = (ell + 1 : ℕ) - (c.val : ℤ) := by
  have hp := residualColumns_pos x c hc
  have hb := c.isLt
  unfold rowShift reflectColumnRow
  split_ifs <;> simp_all <;> omega

theorem reflectRowColumn_val (x : Fin ell → Bool) (r : Fin (ell + 2))
    (hr : r ∈ residualRows x) :
    ((reflectRowColumn r).val : ℤ) = (ell + 1 : ℕ) - rowShift r := by
  have hn := residualRows_ne_first x r hr
  have hb := r.isLt
  unfold reflectRowColumn rowShift
  split_ifs <;> simp_all
  all_goals omega

theorem shiftedRow_eq_signedCoeff (A : PowerSeries R) (s : ℕ) (j : Fin N) :
    shiftedRow A s j = signedCoeff A ((j.val : ℤ) - s) := by
  by_cases hs : s ≤ j.val
  · have hz : 0 ≤ (j.val : ℤ) - s := by omega
    have he : ((j.val : ℤ) - s).toNat = j.val - s := by omega
    simp only [shiftedRow, signedCoeff, ite_eq_left hs, ite_eq_left hz, he]
  · have hz : ¬ 0 ≤ (j.val : ℤ) - s := by omega
    simp only [shiftedRow, signedCoeff, ite_eq_right hs, ite_eq_right hz]

theorem normalizedWordMatrix_active_entry (Q : PowerSeries R) (x : Fin ell → Bool)
    (r : Fin (ell + 2)) (hr : r ∈ residualRows x) (c : Fin (ell + 2)) :
    normalizedWordMatrix Q x r c = signedCoeff Q ((c.val : ℤ) - rowShift r) := by
  cases r using Fin.cases with
  | zero => simp [normalizedWordMatrix, wordMatrix, shiftedRow_eq_signedCoeff, rowShift]
  | succ r =>
    cases r using Fin.cases with
    | zero =>
      exact False.elim ((residualRows_ne_first x _ hr) (by change 1 = 1; rfl))
    | succ i =>
      have hx : x i = true := by
        rw [mem_residualRows_succ, mem_wordCoordinates_succ] at hr
        cases h : x i <;> simp_all
      simp only [normalizedWordMatrix, wordMatrix, Matrix.of_apply, Fin.cases_succ,
        hx, ite_true]
      rw [shiftedRow_eq_signedCoeff, rowShift_succ_succ]
      congr 1

theorem normalizedWordMatrix_det_residual (Q : PowerSeries R) (x : Fin ell → Bool) :
    (normalizedWordMatrix Q x).det = (-1 : R) ^ (wordCoordinates x).card *
      AlgebraicCombinatorics.CauchyBinet.submatrixDet (normalizedWordMatrix Q x)
        (residualRows x) (residualColumns x) (residual_card_eq x) := by
  apply coordinate_rows_det
  intro k hk
  cases k using Fin.cases with
  | zero => exact normalizedWordMatrix_first_coordinate Q x
  | succ i =>
    have hi : x i = false := (mem_wordCoordinates_succ x i).mp hk
    exact normalizedWordMatrix_letter_coordinate Q x i hi

private theorem submatrixDet_reparametrize {s k : ℕ} (M : Matrix (Fin s) (Fin s) R)
    (U V : Finset (Fin s)) (hUV : U.card = V.card)
    (hU : U.card = k) (hV : V.card = k) :
    AlgebraicCombinatorics.CauchyBinet.submatrixDet M U V hUV =
      (M.submatrix (U.orderEmbOfFin hU) (V.orderEmbOfFin hV)).det := by
  subst k
  rfl

/-- Sorted residual minors of reversed words are transposes with both orders reversed. -/
theorem residual_minor_reversal (Q : PowerSeries R) (x : Fin ell → Bool) :
    AlgebraicCombinatorics.CauchyBinet.submatrixDet (normalizedWordMatrix Q (wordReverse x))
      (residualRows (wordReverse x)) (residualColumns (wordReverse x))
      (residual_card_eq (wordReverse x)) =
    AlgebraicCombinatorics.CauchyBinet.submatrixDet (normalizedWordMatrix Q x)
      (residualRows x) (residualColumns x) (residual_card_eq x) := by
  classical
  let k := (residualRows x).card
  have hC : (residualColumns x).card = k := (residual_card_eq x).symm
  have hRrev : (residualRows (wordReverse x)).card = k :=
    (reflection_card x).trans hC
  have hCrev : (residualColumns (wordReverse x)).card = k :=
    (residual_card_eq (wordReverse x)).symm.trans hRrev
  let rr : Fin k → Fin (ell + 2) := (residualRows x).orderEmbOfFin rfl
  let cc : Fin k → Fin (ell + 2) := (residualColumns x).orderEmbOfFin hC
  have hr : (fun i : Fin k => reflectColumnRow (cc i.rev)) =
      (residualRows (wordReverse x)).orderEmbOfFin hRrev := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      exact reflectColumnRow_mem x _ ((residualColumns x).orderEmbOfFin_mem hC _)
    · intro i j hij
      apply reflectColumnRow_strictAnti x
      · exact (residualColumns x).orderEmbOfFin_mem hC _
      · exact (residualColumns x).orderEmbOfFin_mem hC _
      · exact ((residualColumns x).orderEmbOfFin hC).strictMono (Fin.rev_lt_rev.mpr hij)
  have hc : (fun i : Fin k => reflectRowColumn (rr i.rev)) =
      (residualColumns (wordReverse x)).orderEmbOfFin hCrev := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      exact reflectRowColumn_mem x _ ((residualRows x).orderEmbOfFin_mem rfl _)
    · intro i j hij
      apply reflectRowColumn_strictAnti x
      · exact (residualRows x).orderEmbOfFin_mem rfl _
      · exact (residualRows x).orderEmbOfFin_mem rfl _
      · exact ((residualRows x).orderEmbOfFin rfl).strictMono (Fin.rev_lt_rev.mpr hij)
  rw [submatrixDet_reparametrize _ _ _ _ hRrev hCrev,
    submatrixDet_reparametrize _ _ _ _ rfl hC]
  have he :
      (normalizedWordMatrix Q (wordReverse x)).submatrix
        ((residualRows (wordReverse x)).orderEmbOfFin hRrev)
        ((residualColumns (wordReverse x)).orderEmbOfFin hCrev) =
      ((normalizedWordMatrix Q x).submatrix rr cc).transpose.submatrix
        Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Fin.revPerm_apply]
    rw [normalizedWordMatrix_active_entry Q (wordReverse x) _
      ((residualRows (wordReverse x)).orderEmbOfFin_mem hRrev _)]
    rw [normalizedWordMatrix_active_entry Q x _ ((residualRows x).orderEmbOfFin_mem rfl _)]
    rw [← congrFun hr i, ← congrFun hc j,
      rowShift_reflectColumnRow x _ ((residualColumns x).orderEmbOfFin_mem hC _),
      reflectRowColumn_val x _ ((residualRows x).orderEmbOfFin_mem rfl _)]
    congr 1
    ring
  rw [he, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

theorem wordCoordinates_card_reversal (x : Fin ell → Bool) :
    (wordCoordinates (wordReverse x)).card = (wordCoordinates x).card := by
  have h := (reflection_card x).trans (residual_card_eq x).symm
  have hx : (wordCoordinates x).card ≤ ell + 1 := by
    simpa using Finset.card_le_univ (wordCoordinates x)
  have hy : (wordCoordinates (wordReverse x)).card ≤ ell + 1 := by
    simpa using Finset.card_le_univ (wordCoordinates (wordReverse x))
  simp only [residualRows, Finset.card_compl, coordinateRows, Finset.card_map,
    Fintype.card_fin] at h
  omega

/-- Full binary-word determinant reversal after coordinate deletion and sorted reflection. -/
theorem normalizedWordMatrix_det_reversal (Q : PowerSeries R) (x : Fin ell → Bool) :
    (normalizedWordMatrix Q x).det = (normalizedWordMatrix Q (wordReverse x)).det := by
  rw [normalizedWordMatrix_det_residual, normalizedWordMatrix_det_residual,
    wordCoordinates_card_reversal, residual_minor_reversal]

/-- The determinant equality of `lem:two-series-reversal` over a generic commutative ring. -/
theorem wordMatrix_det_reversal (A B : PowerSeries R)
    (hA : PowerSeries.constantCoeff A = 1) (x : Fin ell → Bool) :
    (wordMatrix A B x).det = (wordMatrix A B (wordReverse x)).det := by
  rw [wordMatrix_det_normalized A B hA x, wordMatrix_det_normalized A B hA (wordReverse x)]
  exact normalizedWordMatrix_det_reversal _ x

/-- Positions carrying the second formal series in the binary word. -/
noncomputable def wordBPositions (x : Fin ell → Bool) : Finset (Fin ell) :=
  Finset.univ.filter (fun i => x i = true)

theorem wordCoordinates_card (x : Fin ell → Bool) :
    (wordCoordinates x).card = ell + 1 - (wordBPositions x).card := by
  classical
  let A : Finset (Fin ell) := Finset.univ.filter (fun i => x i = false)
  have hset : wordCoordinates x = insert 0 (A.map (Fin.succEmb ell)) := by
    ext i
    cases i using Fin.cases <;> simp [wordCoordinates, A]
  have h0 : (0 : Fin (ell + 1)) ∉ A.map (Fin.succEmb ell) := by simp
  have hcount := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ell)))
    (fun i => x i = false)
  have hneg : (Finset.univ : Finset (Fin ell)).filter (fun i => ¬ x i = false) =
      wordBPositions x := by
    ext i
    cases h : x i <;> simp [wordBPositions, h]
  rw [hneg] at hcount
  simp only [Finset.card_univ, Fintype.card_fin] at hcount
  rw [hset, Finset.card_insert_of_notMem h0, Finset.card_map]
  dsimp [A]
  omega

/-- The signed sorted-minor formula `eq:word-minor`, with row shifts named explicitly. -/
theorem wordMatrix_det_coefficientMinor (A B : PowerSeries R)
    (hA : PowerSeries.constantCoeff A = 1) (x : Fin ell → Bool) :
    (wordMatrix A B x).det =
      (-1 : R) ^ (ell + 1 - (wordBPositions x).card) *
        (coefficientMinor (quotient A B)
          (fun i : Fin (residualRows x).card =>
            rowShift ((residualRows x).orderEmbOfFin rfl i))
          (fun i : Fin (residualRows x).card =>
            (((residualColumns x).orderEmbOfFin (residual_card_eq x).symm i).val : ℤ))).det := by
  rw [wordMatrix_det_normalized A B hA x, normalizedWordMatrix_det_residual,
    wordCoordinates_card]
  congr 1
  unfold AlgebraicCombinatorics.CauchyBinet.submatrixDet
  congr 1
  ext i j
  exact normalizedWordMatrix_active_entry _ x _
    ((residualRows x).orderEmbOfFin_mem rfl _) _

/-- The manuscript's set J, using its one-based internal shifts. -/
noncomputable def wordBShifts (x : Fin ell → Bool) : Finset ℤ :=
  (wordBPositions x).image (fun i => (i.val : ℤ) + 1)

theorem residual_row_shift_set (x : Fin ell → Bool) :
    (residualRows x).image rowShift = insert 0 (wordBShifts x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    cases r using Fin.cases with
    | zero => simp [rowShift]
    | succ r =>
      cases r using Fin.cases with
      | zero =>
        exact False.elim ((residualRows_ne_first x _ hr) (by change 1 = 1; rfl))
      | succ i =>
        have hx : x i = true := by
          rw [mem_residualRows_succ, mem_wordCoordinates_succ] at hr
          cases h : x i <;> simp_all
        apply Finset.mem_insert.mpr
        right
        refine Finset.mem_image.mpr ⟨i, by simp [wordBPositions, hx], ?_⟩
        simp only [rowShift_succ_succ]
  · intro hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact Finset.mem_image.mpr ⟨0, mem_residualRows_zero x, by simp [rowShift]⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hx : x i = true := by simpa [wordBPositions] using hi
      refine Finset.mem_image.mpr ⟨i.succ.succ, ?_, ?_⟩
      · rw [mem_residualRows_succ, mem_wordCoordinates_succ]
        simp [hx]
      · simp only [rowShift_succ_succ]

theorem residual_column_shift_set (x : Fin ell → Bool) :
    (residualColumns x).image (fun c => (c.val : ℤ)) =
      insert (((ell + 1 : ℕ) : ℤ)) (wordBShifts x) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    have hp := residualColumns_pos x c hc
    have hb := c.isLt
    by_cases hl : c.val = ell + 1
    · exact Finset.mem_insert.mpr (Or.inl (by exact_mod_cast hl))
    · have hi : c.val - 1 < ell := by omega
      let i : Fin ell := ⟨c.val - 1, hi⟩
      have he : c = i.succ.castSucc := by apply Fin.ext; dsimp [i]; omega
      have hx : x i = true := by
        rw [he, mem_residualColumns_castSucc, mem_wordCoordinates_succ] at hc
        cases h : x i <;> simp_all
      apply Finset.mem_insert.mpr
      right
      refine Finset.mem_image.mpr ⟨i, by simp [wordBPositions, hx], ?_⟩
      dsimp [i]
      omega
  · intro hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact Finset.mem_image.mpr ⟨Fin.last (ell + 1), mem_residualColumns_last x, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hx : x i = true := by simpa [wordBPositions] using hi
      refine Finset.mem_image.mpr ⟨i.succ.castSucc, ?_, ?_⟩
      · rw [mem_residualColumns_castSucc, mem_wordCoordinates_succ]
        simp [hx]
      · simp

theorem rowShift_strictMono_on_residual (x : Fin ell → Bool) (r s : Fin (ell + 2))
    (hr : r ∈ residualRows x) (hs : s ∈ residualRows x) (hrs : r < s) :
    rowShift r < rowShift s := by
  have hrn := residualRows_ne_first x r hr
  have hsn := residualRows_ne_first x s hs
  have hval : r.val < s.val := hrs
  unfold rowShift
  split_ifs <;> omega

end TwoSeries
end SkewSchurReconstruction
