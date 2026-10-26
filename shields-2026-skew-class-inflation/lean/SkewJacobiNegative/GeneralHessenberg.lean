/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/GeneralHessenberg.lean

import SkewJacobiNegative.StaircasePrimitives
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Finite-order Hessenberg cuts and contractions

The actual matrix identities underlying `eq:interval-expansion` and
`lem:staircase-minimum` in `shields-2026-skew-jacobi-negative.tex`.
All sizes and seam positions are arbitrary.  Entry erasure is distinguished
from generator erasure, so repeated numerical labels remain permitted.
-/

namespace SkewJacobiNegative.GeneralHessenberg

open Gluing
open scoped BigOperators

/-- Clear one matrix entry, without changing other occurrences of its value. -/
def clearEntry {R : Type*} [Zero R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (r c : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  M.updateRow r (Function.update (M r) c 0)

@[simp] theorem clearEntry_apply {R : Type*} [Zero R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (r c i j : Fin (n + 1)) :
    clearEntry M r c i j = if i = r ∧ j = c then 0 else M i j := by
  classical
  by_cases hi : i = r <;> by_cases hj : j = c <;>
    simp [clearEntry, Matrix.updateRow_apply, Function.update, hi, hj]

/-- Exact single-entry Laplace decomposition, without a private-variable premise. -/
theorem det_clearEntry {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (r c : Fin (n + 1)) :
    M.det = (clearEntry M r c).det +
      (-1 : R) ^ (r.val + c.val) * M r c *
        (M.submatrix r.succAbove c.succAbove).det := by
  classical
  have hm (j : Fin (n + 1)) :
      (clearEntry M r c).submatrix r.succAbove j.succAbove =
        M.submatrix r.succAbove j.succAbove := by
    ext a b
    simp [Matrix.submatrix_apply, Fin.succAbove_ne]
  rw [Matrix.det_succ_row M r, Matrix.det_succ_row (clearEntry M r c) r]
  simp only [hm]
  have ht (j : Fin (n + 1)) :
      (-1 : R) ^ (r.val + j.val) * M r j *
        (M.submatrix r.succAbove j.succAbove).det =
      (-1 : R) ^ (r.val + j.val) * clearEntry M r c r j *
        (M.submatrix r.succAbove j.succAbove).det +
      if j = c then (-1 : R) ^ (r.val + c.val) * M r c *
        (M.submatrix r.succAbove c.succAbove).det else 0 := by
    by_cases hj : j = c
    · subst j; simp
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => ht j), Finset.sum_add_distrib]
  simp

/-- An arbitrary upper Hessenberg matrix is cut at an arbitrary seam.  The
complementary determinant is the genuine contraction, not a formal factor. -/
theorem det_seam_expansion {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (hM : ∀ i j, j.val + 1 < i.val → M i j = 0) (c : Fin (n + 1)) :
    M.det =
      ((clearEntry M c.succ c.castSucc).toSquareBlockProp
        (fun i => i.val ≤ c.val)).det *
      ((clearEntry M c.succ c.castSucc).toSquareBlockProp
        (fun i => ¬ i.val ≤ c.val)).det -
      M c.succ c.castSucc *
        (M.submatrix c.succ.succAbove c.castSucc.succAbove).det := by
  classical
  have ht : ∀ i : Fin (n + 2), ¬ i.val ≤ c.val →
      ∀ j : Fin (n + 2), j.val ≤ c.val →
      clearEntry M c.succ c.castSucc i j = 0 := by
    intro i hi j hj
    by_cases h : j.val + 1 < i.val
    · simp [hM i j h]
    · have hir : i = c.succ := by ext; simp only [Fin.val_succ]; omega
      have hjc : j = c.castSucc := by ext; simp only [Fin.val_castSucc]; omega
      simp [hir, hjc]
  have hs : (-1 : R) ^ (c.succ.val + c.castSucc.val) = -1 := by
    simp only [Fin.val_succ, Fin.val_castSucc]
    rw [show c.val + 1 + c.val = 2 * c.val + 1 by omega,
      pow_add, pow_mul]
    simp
  rw [det_clearEntry M c.succ c.castSucc,
    Matrix.twoBlockTriangular_det _ (fun i => i.val ≤ c.val) ht, hs]
  ring

/-- Deleting a seam's lower row and upper column retains each other gap. -/
theorem contraction_gap_indices {n : ℕ} (c : Fin (n + 1)) (j : Fin n) :
    c.succ.succAbove j.succ = (c.succAbove j).succ ∧
      c.castSucc.succAbove j.castSucc = (c.succAbove j).castSucc := by
  by_cases hj : j.val < c.val
  · constructor
    · rw [Fin.succAbove_of_castSucc_lt _ _
        (show j.succ.castSucc < c.succ by change j.val + 1 < c.val + 1; omega),
        Fin.succAbove_of_castSucc_lt _ _
        (show j.castSucc < c by exact hj)]
      apply Fin.ext
      rfl
    · rw [Fin.succAbove_of_castSucc_lt _ _
        (show j.castSucc.castSucc < c.castSucc by exact hj),
        Fin.succAbove_of_castSucc_lt _ _ (show j.castSucc < c by exact hj)]
  · constructor
    · rw [Fin.succAbove_of_le_castSucc _ _
        (show c.succ ≤ j.succ.castSucc by change c.val + 1 ≤ j.val + 1; omega),
        Fin.succAbove_of_le_castSucc _ _
        (show c ≤ j.castSucc by change c.val ≤ j.val; omega)]
    · rw [Fin.succAbove_of_le_castSucc _ _
        (show c.castSucc ≤ j.castSucc.castSucc by change c.val ≤ j.val; omega),
        Fin.succAbove_of_le_castSucc _ _
        (show c ≤ j.castSucc by change c.val ≤ j.val; omega)]
      apply Fin.ext
      rfl

/-- The contracted beta pair deletes actual beta coordinates. -/
def contractionPair {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    Profile.BetaPair n where
  xi i := P.xi (c.succ.succAbove i)
  zeta i := P.zeta (c.castSucc.succAbove i)
  xi_strictAnti i j hij := P.xi_strictAnti ((Fin.strictMono_succAbove _) hij)
  zeta_strictAnti i j hij := P.zeta_strictAnti ((Fin.strictMono_succAbove _) hij)
  zeta_last := by
    have he : c.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) := by
      rw [Fin.succAbove_castSucc_of_le c (Fin.last n) (Fin.le_last c)]
      apply Fin.ext
      rfl
    rw [he, P.zeta_last]
  zeta_le_xi_succ j := by
    obtain ⟨hr, hc⟩ := contraction_gap_indices c j
    rw [hr, hc]
    exact P.zeta_le_xi_succ _
  xi_last_pos := P.xi_pos _

/-- The genuine connected profile obtained by contracting one seam. -/
def contract {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) : Profile n :=
  Profile.ofBetaPair (contractionPair P c)

/-- Both contracted coordinate lists agree with the actual deleted lists. -/
theorem contract_beta {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    (contract P c).xi = (fun i => P.xi (c.succ.succAbove i)) ∧
    (contract P c).zeta = (fun i => P.zeta (c.castSucc.succAbove i)) := by
  have h := Profile.equivBetaPair.right_inv (contractionPair P c)
  have hx := congrArg Profile.BetaPair.xi h
  have hz := congrArg Profile.BetaPair.zeta h
  exact ⟨hx, hz⟩

@[simp] theorem contract_gap {n : ℕ} (P : Profile (n + 1))
    (c : Fin (n + 1)) (j : Fin n) :
    (contract P c).g j = P.g (c.succAbove j) := by
  obtain ⟨hr, hc⟩ := contraction_gap_indices c j
  simp only [contract, Profile.ofBetaPair, contractionPair, hr, hc]
  rw [P.xi_succ_sub_zeta_castSucc]
  simp

/-- The merged row has the exact interval index, with no truncated subtraction. -/
theorem contract_joined_row {n : ℕ} (P : Profile (n + 1))
    (c : Fin (n + 1)) :
    ((contract P c).r c : ℤ) =
      (P.r c.castSucc : ℤ) + P.r c.succ - P.g c := by
  have h := P.zeta_castSucc c
  have hx := P.xi_sub_zeta c.castSucc
  have hpos := P.g_lt_succ c
  simp only [contract, Profile.ofBetaPair, contractionPair,
    Fin.succAbove_succ_self, Fin.succAbove_castSucc_of_le _ _ le_rfl]
  omega

/-- The actual contracted determinant is precisely the complementary matrix. -/
theorem contract_schur {n : ℕ} (P : Profile (n + 1))
    (c : Fin (n + 1)) :
    (contract P c).toBetaDiagram.schur =
      (P.toBetaDiagram.matrix.submatrix c.succ.succAbove
        c.castSucc.succAbove).det := by
  rw [Profile.toBetaDiagram_schur]
  unfold Profile.schur
  obtain ⟨hx, hz⟩ := contract_beta P c
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [hx, hz, BetaDiagram.matrix, Profile.toBetaDiagram,
    Matrix.of_apply, Matrix.submatrix_apply]
  exact (complete_eq_hh _).symm

/-- The intrinsic lower-zero geometry is preserved by every seam contraction. -/
theorem contract_hessenberg {n : ℕ} (P : Profile (n + 1))
    (hP : P.Hessenberg) (c : Fin (n + 1)) : (contract P c).Hessenberg := by
  obtain ⟨hx, hz⟩ := contract_beta P c
  intro i j hij
  rw [hx, hz]
  apply hP
  simp only [Fin.succAbove, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc,
    Fin.lt_def] <;> omega

/-- Thickness is the arithmetic form of intrinsic Hessenberg geometry. -/
theorem hessenberg_thick {n : ℕ} (P : Profile n) (hP : P.Hessenberg) :
    Staircase.Thick P := by
  intro j k hjk
  have hl := hP k.succ j.castSucc (by
    have hv := congrArg Fin.val hjk
    simp only [Fin.val_succ, Fin.val_castSucc] at hv ⊢
    omega)
  have hz := P.zeta_castSucc j
  have hg := P.xi_succ_sub_zeta_castSucc k
  rw [← hjk] at hg
  have hx := P.xi_sub_zeta j.succ
  exact_mod_cast (show (P.g j : ℤ) + P.g k < P.r j.succ by omega)

/-- Every contraction of a thick profile is a thick, genuinely connected profile. -/
theorem contract_thick {n : ℕ} {P : Profile (n + 1)}
    (hP : Staircase.Thick P) (c : Fin (n + 1)) :
    Staircase.Thick (contract P c) :=
  hessenberg_thick _ (contract_hessenberg _ hP.hessenberg c)

/-- Single-seam expansion for the actual Schur determinant at every order. -/
theorem schur_seam_expansion {n : ℕ} (P : Profile (n + 1))
    (hP : Staircase.Thick P) (c : Fin (n + 1)) :
    P.toBetaDiagram.schur =
      ((clearEntry P.toBetaDiagram.matrix c.succ c.castSucc).toSquareBlockProp
        (fun i => i.val ≤ c.val)).det *
      ((clearEntry P.toBetaDiagram.matrix c.succ c.castSucc).toSquareBlockProp
        (fun i => ¬ i.val ≤ c.val)).det -
      complete (P.g c) * (contract P c).toBetaDiagram.schur := by
  have h := det_seam_expansion P.toBetaDiagram.matrix
    (fun i j hij => complete_of_neg (hP.hessenberg i j hij)) c
  have he : P.toBetaDiagram.matrix c.succ c.castSucc = complete (P.g c) := by
    change complete (P.xi c.succ - P.zeta c.castSucc) = _
    rw [P.xi_succ_sub_zeta_castSucc]
  rw [he, ← contract_schur P c] at h
  exact h

/-- Telescoping beta coordinates give the full row-minus-gap interval label. -/
theorem intervalLabel_eq_index {n : ℕ} (P : Profile n)
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    P.intervalLabel a b = P.xi a - P.zeta b := by
  classical
  have hz : P.zeta a = P.zeta b +
      ∑ j : Fin n, if a.val ≤ j.val ∧ j.val < b.val then
        ((P.r j.succ : ℤ) - P.g j) else 0 := by
    unfold Profile.zeta
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> omega
  have hr :
      (∑ i : Fin (n + 1), if a.val ≤ i.val ∧ i.val ≤ b.val then
        (P.r i : ℤ) else 0) =
      (P.r a : ℤ) +
        ∑ j : Fin n, if a.val ≤ j.val ∧ j.val < b.val then
          (P.r j.succ : ℤ) else 0 := by
    have ht (i : Fin (n + 1)) :
        (if a.val ≤ i.val ∧ i.val ≤ b.val then (P.r i : ℤ) else 0) =
        (if i = a then (P.r a : ℤ) else 0) +
          if a.val < i.val ∧ i.val ≤ b.val then (P.r i : ℤ) else 0 := by
      by_cases hi : i = a
      · subst i; simp [hab]
      · have hne : i.val ≠ a.val := fun h => hi (Fin.ext h)
        split_ifs <;> simp_all <;> omega
    rw [Finset.sum_congr rfl (fun i _ => ht i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, not_lt_zero, false_and, ite_false, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    have hp : (a.val < j.succ.val ∧ j.succ.val ≤ b.val) ↔
        (a.val ≤ j.val ∧ j.val < b.val) := by
      simp only [Fin.val_succ]
      omega
    simp only [hp]
  unfold Profile.intervalLabel
  rw [hr, add_sub_assoc, ← Finset.sum_sub_distrib]
  have ht (j : Fin n) :
      (if a.val ≤ j.val ∧ j.val < b.val then (P.r j.succ : ℤ) else 0) -
      (if a.val ≤ j.val ∧ j.val < b.val then (P.g j : ℤ) else 0) =
      if a.val ≤ j.val ∧ j.val < b.val then
        ((P.r j.succ : ℤ) - P.g j) else 0 := by
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => ht j)]
  simp only [Profile.xi]
  omega

/-- A minimum internal gap is below every row, at every finite order. -/
theorem row_gt_minimum {n : ℕ} (P : Profile n) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val)
    (i : Fin (n + 1)) : z.val < P.r i := by
  obtain ⟨k, _⟩ := hocc
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val, hi⟩
    have he : j.castSucc = i := by ext; rfl
    have h := P.g_lt_castSucc j
    rw [he] at h
    exact lt_of_le_of_lt (hmin j) h
  · let j : Fin n := ⟨n - 1, by have := k.isLt; omega⟩
    have he : j.succ = i := by
      apply Fin.ext
      change n - 1 + 1 = i.val
      have hn := k.isLt
      have hb := i.isLt
      omega
    have h := P.g_lt_succ j
    rw [he] at h
    exact lt_of_le_of_lt (hmin j) h

/-- No upper interval label equals the minimum gap, even when gap values repeat. -/
theorem intervalLabel_gt_minimum {n : ℕ} (P : Profile n) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val)
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    (z.val : ℤ) < P.intervalLabel a b := by
  rw [intervalLabel_eq_index P a b hab]
  have hr : (z.val : ℤ) < P.r a := by
    exact_mod_cast row_gt_minimum P z hmin hocc a
  have hx := P.xi_sub_zeta a
  have hz := P.zeta_strictAnti.antitone hab
  omega

/-- The minimum generator occurs exactly at its subdiagonal seams in the
actual matrix; it cannot collide with any upper interval entry. -/
theorem minimum_index_iff_seam {n : ℕ} {P : Profile n}
    (hP : Staircase.Thick P) (z : ℕ+)
    (hmin : ∀ j, z.val ≤ P.g j) (hocc : ∃ j, P.g j = z.val)
    (i j : Fin (n + 1)) :
    P.xi i - P.zeta j = (z.val : ℤ) ↔
      ∃ s : Fin n, i = s.succ ∧ j = s.castSucc ∧ P.g s = z.val := by
  constructor
  · intro he
    have hlo : j < i := by
      by_contra h
      have hij : i ≤ j := le_of_not_gt h
      have hu := intervalLabel_gt_minimum P z hmin hocc i j hij
      rw [intervalLabel_eq_index P i j hij, he] at hu
      omega
    have hnear : i.val = j.val + 1 := by
      by_contra h
      have hn := hP.hessenberg i j (by omega)
      have hp := z.pos
      omega
    let s : Fin n := ⟨j.val, by have := i.isLt; omega⟩
    have hi : i = s.succ := by ext; dsimp [s]; omega
    have hj : j = s.castSucc := by ext; rfl
    refine ⟨s, hi, hj, ?_⟩
    rw [hi, hj, P.xi_succ_sub_zeta_castSucc] at he
    exact_mod_cast he
  · rintro ⟨s, rfl, rfl, hs⟩
    rw [P.xi_succ_sub_zeta_castSucc, hs]

/-- Increasing inclusion of a genuine consecutive row interval. -/
def sliceEmbedding {n : ℕ} (a k : ℕ) (h : a + k ≤ n) :
    Fin (k + 1) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨a + i.val, by have := i.isLt; omega⟩)
    (by intro i j hij; change a + i.val < a + j.val; omega)

/-- A consecutive subprofile retains actual row lengths and actual gaps. -/
def slice {n : ℕ} (P : Profile n) (a k : ℕ) (h : a + k ≤ n) : Profile k where
  r i := P.r (sliceEmbedding a k h i)
  g j := P.g ⟨a + j.val, by have := j.isLt; omega⟩
  r_pos i := P.r_pos _
  g_lt_castSucc j := P.g_lt_castSucc _
  g_lt_succ j := P.g_lt_succ _

/-- A subprofile is exactly the normalized restriction of both beta lists. -/
theorem slice_beta {n : ℕ} (P : Profile n) (a k : ℕ) (h : a + k ≤ n) :
    (slice P a k h).xi =
      (fun i => P.xi (sliceEmbedding a k h i) -
        P.zeta (sliceEmbedding a k h (Fin.last k))) ∧
    (slice P a k h).zeta =
      (fun i => P.zeta (sliceEmbedding a k h i) -
        P.zeta (sliceEmbedding a k h (Fin.last k))) := by
  have he := (slice P a k h).eq_beta_of_equations
    (x := fun i => P.xi (sliceEmbedding a k h i) -
      P.zeta (sliceEmbedding a k h (Fin.last k)))
    (z := fun i => P.zeta (sliceEmbedding a k h i) -
      P.zeta (sliceEmbedding a k h (Fin.last k))) (sub_self _) ?_ ?_
  · exact ⟨he.1.symm, he.2.symm⟩
  · intro i
    simp only [slice]
    have hx := P.xi_sub_zeta (sliceEmbedding a k h i)
    linarith
  · intro j
    let s : Fin n := ⟨a + j.val, by have := j.isLt; omega⟩
    have h1 : s.castSucc = sliceEmbedding a k h j.castSucc := by ext; rfl
    have h2 : s.succ = sliceEmbedding a k h j.succ := by
      apply Fin.ext
      change a + j.val + 1 = a + (j.val + 1)
      omega
    have hg := P.xi_succ_sub_zeta_castSucc s
    rw [h1, h2] at hg
    change _ = (P.g s : ℤ)
    linarith

/-- The determinant of a consecutive subprofile is its actual principal minor. -/
theorem slice_schur {n : ℕ} (P : Profile n) (a k : ℕ) (h : a + k ≤ n) :
    (slice P a k h).toBetaDiagram.schur =
      (P.toBetaDiagram.matrix.submatrix (sliceEmbedding a k h)
        (sliceEmbedding a k h)).det := by
  rw [Profile.toBetaDiagram_schur]
  unfold Profile.schur
  obtain ⟨hx, hz⟩ := slice_beta P a k h
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [hx, hz, BetaDiagram.matrix, Profile.toBetaDiagram,
    Matrix.of_apply, Matrix.submatrix_apply]
  rw [show P.xi (sliceEmbedding a k h i) - P.zeta (sliceEmbedding a k h (Fin.last k)) -
      (P.zeta (sliceEmbedding a k h j) - P.zeta (sliceEmbedding a k h (Fin.last k))) =
      P.xi (sliceEmbedding a k h i) - P.zeta (sliceEmbedding a k h j) by ring]
  exact (complete_eq_hh _).symm

theorem slice_thick {n : ℕ} {P : Profile n} (hP : Staircase.Thick P)
    (a k : ℕ) (h : a + k ≤ n) : Staircase.Thick (slice P a k h) := by
  intro j l hjl
  let s : Fin n := ⟨a + j.val, by have := j.isLt; omega⟩
  let t : Fin n := ⟨a + l.val, by have := l.isLt; omega⟩
  have he : s.succ = t.castSucc := by
    have hv := congrArg Fin.val hjl
    ext
    simp only [Fin.val_succ, Fin.val_castSucc] at hv ⊢
    dsimp [s, t]
    omega
  exact hP s t he

/-- Left and right actual components at a single specified seam. -/
def leftOfSeam {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) : Profile c.val :=
  slice P 0 c.val (by omega)

def rightOfSeam {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    Profile (n - c.val) := slice P (c.val + 1) (n - c.val) (by have := c.isLt; omega)

/-- Identification of the cleared left block with its actual connected profile. -/
theorem leftOfSeam_block {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    ((clearEntry P.toBetaDiagram.matrix c.succ c.castSucc).toSquareBlockProp
      (fun i => i.val ≤ c.val)).det = (leftOfSeam P c).toBetaDiagram.schur := by
  classical
  rw [leftOfSeam, slice_schur]
  let e : {i : Fin (n + 2) // i.val ≤ c.val} ≃ Fin (c.val + 1) :=
    { toFun := fun i => ⟨i.val.val, by omega⟩
      invFun := fun i => ⟨⟨i.val, by have := c.isLt; have := i.isLt; omega⟩,
        by change i.val ≤ c.val; have := i.isLt; omega⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  rw [← Matrix.det_reindex_self e]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hei : (e.symm i).val = sliceEmbedding 0 c.val (by omega) i := by
    apply Fin.ext
    change i.val = 0 + i.val
    omega
  have hej : (e.symm j).val = sliceEmbedding 0 c.val (by omega) j := by
    apply Fin.ext
    change j.val = 0 + j.val
    omega
  change clearEntry P.toBetaDiagram.matrix c.succ c.castSucc
    (e.symm i).val (e.symm j).val =
    P.toBetaDiagram.matrix (sliceEmbedding 0 c.val (by omega) i)
      (sliceEmbedding 0 c.val (by omega) j)
  rw [hei, hej, clearEntry_apply]
  have hn : sliceEmbedding 0 c.val (by omega) i ≠ c.succ := by
    intro h
    have hv := congrArg Fin.val h
    change 0 + i.val = c.val + 1 at hv
    have hb := i.isLt
    omega
  simp [hn]

/-- Identification of the cleared right block with its actual connected profile. -/
theorem rightOfSeam_block {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    ((clearEntry P.toBetaDiagram.matrix c.succ c.castSucc).toSquareBlockProp
      (fun i => ¬ i.val ≤ c.val)).det = (rightOfSeam P c).toBetaDiagram.schur := by
  classical
  rw [rightOfSeam, slice_schur]
  let e : {i : Fin (n + 2) // ¬ i.val ≤ c.val} ≃ Fin (n - c.val + 1) :=
    { toFun := fun i => ⟨i.val.val - (c.val + 1), by
        have := i.val.isLt; have := c.isLt; omega⟩
      invFun := fun i => ⟨⟨c.val + 1 + i.val, by
        have := i.isLt; have := c.isLt; omega⟩,
        by change ¬ c.val + 1 + i.val ≤ c.val; omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        change c.val + 1 + (i.val.val - (c.val + 1)) = i.val.val
        have hi := i.property
        omega
      right_inv := by intro i; apply Fin.ext; simp }
  rw [← Matrix.det_reindex_self e]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hei : (e.symm i).val =
      sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i := by
    apply Fin.ext
    rfl
  have hej : (e.symm j).val =
      sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) j := by
    apply Fin.ext
    rfl
  change clearEntry P.toBetaDiagram.matrix c.succ c.castSucc
    (e.symm i).val (e.symm j).val =
    P.toBetaDiagram.matrix
      (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i)
      (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) j)
  rw [hei, hej, clearEntry_apply]
  have hn :
      sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) j ≠
        c.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    change c.val + 1 + j.val = c.val at hv
    omega
  simp [hn]

/-- The all-order joining identity on the thick domain.  The domain includes
both strict endpoint inequalities, not merely connectedness. -/
theorem schur_join_formula {n : ℕ} (P : Profile (n + 1))
    (hP : Staircase.Thick P) (c : Fin (n + 1)) :
    P.toBetaDiagram.schur =
      (leftOfSeam P c).toBetaDiagram.schur *
        (rightOfSeam P c).toBetaDiagram.schur -
      complete (P.g c) * (contract P c).toBetaDiagram.schur := by
  rw [schur_seam_expansion P hP c, leftOfSeam_block, rightOfSeam_block]

/-- The unsigned interval monomial selected by a seam mask.  A true seam
merges its adjacent rows and retains its gap factor; a false seam terminates
the first interval.  Thus this construction enumerates consecutive intervals. -/
noncomputable def intervalMask {R : Type*} [CommRing R] (h : ℤ → R) :
    {n : ℕ} → Profile n → (Fin n → Bool) → R
  | 0, P, _ => h (P.r 0)
  | n + 1, P, S =>
      if S 0 then
        h (P.g 0) * intervalMask h (contract P 0) (fun j => S j.succ)
      else h (P.r 0) * intervalMask h (rightOfSeam P 0) (fun j => S j.succ)

/-- Number of selected seams, counting positions rather than numerical values. -/
def selectedSeams {n : ℕ} (S : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if S i then 1 else 0

/-- Every finite-order actual Schur determinant is its interval-subset
expansion.  Repeated numerical gap values are separate mask coordinates. -/
theorem schur_interval_mask_expansion {n : ℕ} (P : Profile n)
    (hP : Staircase.Thick P) :
    P.toBetaDiagram.schur =
      ∑ S : Fin n → Bool,
        (-1 : CompleteRing) ^ selectedSeams S * intervalMask complete P S := by
  classical
  induction n with
  | zero =>
      rw [Profile.toBetaDiagram_schur]
      simp [Profile.schur, Matrix.det_fin_one, Profile.xi_sub_zeta,
        selectedSeams, intervalMask, complete_eq_hh]
  | succ n ih =>
      rw [schur_join_formula P hP 0]
      have hl : (leftOfSeam P 0).toBetaDiagram.schur = complete (P.r 0) := by
        rw [Profile.toBetaDiagram_schur]
        let Q : Profile 0 := leftOfSeam P 0
        change (Matrix.of (fun i j : Fin 1 => hh (Q.xi i - Q.zeta j))).det =
          complete (P.r 0)
        rw [Matrix.det_fin_one]
        change hh (Q.xi 0 - Q.zeta 0) = complete (P.r 0)
        rw [Q.xi_sub_zeta]
        have hr : Q.r 0 = P.r 0 := rfl
        rw [hr, complete_eq_hh]
      let Q : Profile n := slice P 1 n (by omega)
      have hr : Staircase.Thick Q := slice_thick hP 1 n (by omega)
      have hright : (rightOfSeam P 0).toBetaDiagram.schur =
          ∑ S : Fin n → Bool,
            (-1 : CompleteRing) ^ selectedSeams S * intervalMask complete Q S := by
        simpa only [rightOfSeam, Fin.val_zero, Nat.sub_zero] using ih Q hr
      rw [hl, hright, ih (contract P 0) (contract_thick hP 0)]
      have he := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
        (fun S : Fin (n + 1) → Bool =>
          (-1 : CompleteRing) ^ selectedSeams S * intervalMask complete P S)
      rw [← he]
      have hf (S : Fin n → Bool) :
          (-1 : CompleteRing) ^ selectedSeams (Fin.cons false S) *
            intervalMask complete P (Fin.cons false S) =
          complete (P.r 0) *
            ((-1 : CompleteRing) ^ selectedSeams S * intervalMask complete Q S) := by
        have hs : selectedSeams (Fin.cons false S) = selectedSeams S := by
          simp only [selectedSeams, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
            Bool.false_eq_true, ite_false, zero_add]
        have hm : intervalMask complete P (Fin.cons false S) =
            complete (P.r 0) * intervalMask complete Q S := by
          simp only [intervalMask, Fin.cons_zero, Fin.cons_succ,
            Bool.false_eq_true, ite_false, Q, rightOfSeam, Fin.val_zero, Nat.sub_zero]
        rw [hs, hm]
        ring
      have ht (S : Fin n → Bool) :
          (-1 : CompleteRing) ^ selectedSeams (Fin.cons true S) *
            intervalMask complete P (Fin.cons true S) =
          -(complete (P.g 0) *
            ((-1 : CompleteRing) ^ selectedSeams S *
              intervalMask complete (contract P 0) S)) := by
        have hs : selectedSeams (Fin.cons true S) = selectedSeams S + 1 := by
          simp only [selectedSeams, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
            ite_true]
          omega
        have hm : intervalMask complete P (Fin.cons true S) =
            complete (P.g 0) * intervalMask complete (contract P 0) S := by
          simp only [intervalMask, Fin.cons_zero, Fin.cons_succ,
            ite_true]
        rw [hs, hm, pow_succ]
        ring
      have htsum :
          (∑ S : Fin n → Bool,
            (-1 : CompleteRing) ^ selectedSeams (Fin.cons true S) *
              intervalMask complete P (Fin.cons true S)) =
          -(complete (P.g 0) * ∑ S : Fin n → Bool,
            (-1 : CompleteRing) ^ selectedSeams S *
              intervalMask complete (contract P 0) S) := by
        rw [Finset.sum_congr rfl (fun S _ => ht S),
          Finset.sum_neg_distrib, ← Finset.mul_sum]
      have hfsum :
          (∑ S : Fin n → Bool,
            (-1 : CompleteRing) ^ selectedSeams (Fin.cons false S) *
              intervalMask complete P (Fin.cons false S)) =
          complete (P.r 0) * ∑ S : Fin n → Bool,
            (-1 : CompleteRing) ^ selectedSeams S * intervalMask complete Q S := by
        rw [Finset.sum_congr rfl (fun S _ => hf S), ← Finset.mul_sum]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      change complete (P.r 0) *
          (∑ S : Fin n → Bool,
            (-1 : CompleteRing) ^ selectedSeams S * intervalMask complete Q S) -
        complete (P.g 0) *
          (∑ S : Fin n → Bool,
            (-1 : CompleteRing) ^ selectedSeams S *
              intervalMask complete (contract P 0) S) =
        (∑ S : Fin n → Bool,
          (-1 : CompleteRing) ^ selectedSeams (Fin.cons true S) *
            intervalMask complete P (Fin.cons true S)) +
        (∑ S : Fin n → Bool,
          (-1 : CompleteRing) ^ selectedSeams (Fin.cons false S) *
            intervalMask complete P (Fin.cons false S))
      rw [htsum, hfsum]
      ring

/-- The incident internal gap above the joining row, absent at the first row. -/
def joiningLeftGap {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) : ℕ :=
  if h : c.val = 0 then 0 else
    P.g ⟨c.val - 1, by have := c.isLt; omega⟩

/-- The incident internal gap below the joining row, absent at the last row. -/
def joiningRightGap {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) : ℕ :=
  if h : c.val + 1 < n + 1 then P.g ⟨c.val + 1, h⟩ else 0

/-- The joining hypotheses are the two strict positive-border inequalities.
Connectedness alone supplies neither sum inequality. -/
theorem joining_inequalities {n : ℕ} (P : Profile (n + 1))
    (hP : Staircase.Thick P) (c : Fin (n + 1)) :
    joiningLeftGap P c + P.g c < P.r c.castSucc ∧
      P.g c + joiningRightGap P c < P.r c.succ := by
  constructor
  · unfold joiningLeftGap
    split_ifs with hc
    · simpa using P.g_lt_castSucc c
    · let a : Fin (n + 1) := ⟨c.val - 1, by have := c.isLt; omega⟩
      have ha : a.succ = c.castSucc := by ext; dsimp [a]; omega
      have h := hP a c ha
      simpa only [ha] using h
  · unfold joiningRightGap
    split_ifs with hc
    · let b : Fin (n + 1) := ⟨c.val + 1, hc⟩
      have hb : c.succ = b.castSucc := by ext; rfl
      exact hP c b hb
    · simpa using P.g_lt_succ c

theorem contract_connected {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1)) :
    (contract P c).toBetaDiagram.Connected :=
  (contract P c).toBetaDiagram_connected

end SkewJacobiNegative.GeneralHessenberg
