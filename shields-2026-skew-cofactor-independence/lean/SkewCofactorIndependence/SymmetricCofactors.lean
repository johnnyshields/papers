/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.BetaDiagrams
import SkewCofactorIndependence.MaximumAssignments
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Sym.Card

/-!
# Symmetric dense cofactor relations

The symmetric clause of `thm:cofactor-relations`, with the interlacing in
`eq:interlaced-indices` and the actual determinant leaders in
`eq:symmetric-leader`.  The order-one auxiliary case is included: its sole
cofactor is the determinant of the empty matrix, hence one.
-/

namespace SkewCofactorIndependence

open scoped BigOperators
open MvPolynomial

/-- Reflection of a matrix site across its secondary diagonal. -/
def siteReflection {m : ℕ} (s : Fin m × Fin m) : Fin m × Fin m :=
  (s.2.rev, s.1.rev)

@[simp] theorem siteReflection_involutive {m : ℕ} (s : Fin m × Fin m) :
    siteReflection (siteReflection s) = s := by simp [siteReflection]

/-- One actual site from each secondary-diagonal reflection orbit. -/
abbrev CofactorRepresentative (m : ℕ) := {s : Fin m × Fin m // s.1 ≤ s.2.rev}

namespace BetaDiagram

variable {n : ℕ} (D : BetaDiagram (n + 1))

/-- Symmetry supplies the common center; it is not an additional hypothesis. -/
theorem Symmetric.exists_center (h : D.Symmetric) :
    ∃ c : ℤ, ∀ j, D.col j = c - D.row j.rev := by
  obtain ⟨c, _, hc⟩ := h
  exact ⟨c, hc⟩

/-- The center is unique already in the one-row auxiliary case. -/
theorem center_unique {c c' : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev)
    (hc' : ∀ j, D.col j = c' - D.row j.rev) : c = c' := by
  have h := hc 0
  have h' := hc' 0
  omega

/-- Reversing the columns produces the symmetric sum-label matrix. -/
theorem reverse_columns {c : ℤ} (hc : ∀ j, D.col j = c - D.row j.rev) :
    D.matrix.submatrix id Fin.rev =
      Matrix.of (fun i j => complete (D.row i + D.row j - c)) := by
  ext i j
  simp only [Matrix.submatrix_apply, matrix, Matrix.of_apply, id_eq, hc, Fin.rev_rev]
  congr 1
  ring_nf

/-- Every sum label is positive, including the last diagonal label. -/
theorem symmetric_sum_pos (hd : D.Dense) {c : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev) (i j : Fin (n + 1)) :
    0 < D.row i + D.row j - c := by
  have h := hd i j.rev
  rw [hc, Fin.rev_rev] at h
  omega

/-- Diagonal labels from `eq:interlaced-indices`. -/
def diagonalLabel (c : ℤ) (i : Fin (n + 1)) : ℤ := 2 * D.row i - c

/-- Adjacent off-diagonal labels from `eq:interlaced-indices`. -/
def adjacentLabel (c : ℤ) (i : Fin n) : ℤ := D.row i.castSucc + D.row i.succ - c

/-- Both strict inequalities in each interlacing step are derived from the beta order. -/
theorem symmetric_interlacing (c : ℤ) (i : Fin n) :
    D.diagonalLabel c i.succ < D.adjacentLabel c i ∧
      D.adjacentLabel c i < D.diagonalLabel c i.castSucc := by
  have h := D.row_strictAnti i.castSucc_lt_succ
  simp only [diagonalLabel, adjacentLabel]
  omega

/-- The entire diagonal label list decreases strictly. -/
theorem diagonalLabel_strictAnti (c : ℤ) : StrictAnti (D.diagonalLabel c) := by
  intro i j hij
  have h := D.row_strictAnti hij
  simp only [diagonalLabel]
  omega

/-- Density supplies the terminal strict positivity in the interlacing chain. -/
theorem diagonalLabel_pos (hd : D.Dense) {c : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev) (i : Fin (n + 1)) :
    0 < D.diagonalLabel c i := by
  have h := D.symmetric_sum_pos hd hc i i
  simpa [diagonalLabel, two_mul] using h

/-- The order-one auxiliary case uses the actual empty complementary determinant. -/
theorem cofactor_order_one (E : BetaDiagram 1) :
    E.cofactor 0 0 = 1 := by
  simp [cofactor, Matrix.det_isEmpty]

/-- The actual signed cofactors agree at reflected sites, without discarding their signs. -/
theorem symmetric_cofactor_eq (hs : D.Symmetric) (i j : Fin (n + 1)) :
    D.cofactor i j = D.cofactor j.rev i.rev := by
  obtain ⟨c, hc⟩ := Symmetric.exists_center D hs
  have hm : D.matrix = D.matrix.transpose.submatrix Fin.rev Fin.rev := by
    ext a b
    simp only [matrix, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
      hc, Fin.rev_rev]
    congr 1
    ring_nf
  have hAdj := congrArg Matrix.adjugate hm
  change D.matrix.adjugate =
    (D.matrix.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin (n + 1)))
      (Fin.revPerm : Equiv.Perm (Fin (n + 1)))).adjugate at hAdj
  rw [Matrix.adjugate_submatrix_equiv_self (Fin.revPerm : Equiv.Perm (Fin (n + 1))),
    ← Matrix.adjugate_transpose] at hAdj
  have he := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing =>
    A j i) hAdj
  simpa only [Fin.revPerm_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
    Matrix.adjugate_fin_succ_eq_det_submatrix, cofactor] using he

private theorem succAbove_strictMono (i : Fin (n + 1)) : StrictMono i.succAbove := by
  intro a b hab
  simp only [Fin.succAbove]
  split_ifs <;> simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;> omega

/-- The unsigned minor in the column-reversed symmetric matrix. -/
noncomputable def symmetricMinor (c : ℤ) (i j : Fin (n + 1)) : CompleteRing :=
  (Matrix.of (fun a b : Fin n =>
    complete (D.row (i.succAbove a) + D.row (j.succAbove b) - c))).det

/-- Exponents of the real maximum-square assignment, on actual positive generators. -/
noncomputable def symmetricMinorExponent (hd : D.Dense) {c : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev) (i j : Fin (n + 1)) : ℕ+ →₀ ℕ :=
  assignmentExponent (D.row ∘ i.succAbove) (D.row ∘ j.succAbove) c
    (fun _a _b => D.symmetric_sum_pos hd hc _ _)

/-- Exact maximum-square initial form of each complementary determinant. -/
theorem symmetricMinor_initialForm (hd : D.Dense) {c : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev) (i j : Fin (n + 1)) :
    Base.initialForm negativeSquareWeight (D.symmetricMinor c i j) =
      monomial (D.symmetricMinorExponent hd hc i j) 1 := by
  exact maximum_square_initialForm _ _ c
    (D.row_strictAnti.comp_strictMono (succAbove_strictMono i))
    (D.row_strictAnti.comp_strictMono (succAbove_strictMono j))
    (fun a b => D.symmetric_sum_pos hd hc _ _)

/-- The skipped identity assignment has precisely the diagonal/adjacent/diagonal pattern. -/
theorem symmetric_leader_label {c : ℤ} (i j : Fin (n + 1)) (hij : i ≤ j) (t : Fin n) :
    D.row (i.succAbove t) + D.row (j.succAbove t) - c =
      if t.castSucc < i then D.diagonalLabel c t.castSucc
      else if t.castSucc < j then D.adjacentLabel c t
      else D.diagonalLabel c t.succ := by
  unfold Fin.succAbove diagonalLabel adjacentLabel
  split_ifs with hti htj htj <;> try omega

private theorem identity_label_diagonal_iff (c : ℤ) (i j : Fin (n + 1))
    (hij : i ≤ j) (t : Fin n) (k : Fin (n + 1)) :
    D.row (i.succAbove t) + D.row (j.succAbove t) - c = D.diagonalLabel c k ↔
      (t.castSucc < i ∧ t.castSucc = k) ∨ (j ≤ t.castSucc ∧ t.succ = k) := by
  rw [D.symmetric_leader_label i j hij t]
  by_cases hti : t.castSucc < i
  · rw [ite_eq_left hti]
    have htj : ¬ j ≤ t.castSucc := by omega
    simp only [hti, true_and, htj, false_and, or_false]
    exact (D.diagonalLabel_strictAnti c).injective.eq_iff
  · rw [ite_eq_right hti]
    by_cases htj : t.castSucc < j
    · rw [ite_eq_left htj]
      have hne : D.adjacentLabel c t ≠ D.diagonalLabel c k := by
        intro he
        rcases le_or_gt k t.castSucc with hk | hk
        · have hh := (D.diagonalLabel_strictAnti c).antitone hk
          have hi := (D.symmetric_interlacing c t).2
          rw [he] at hi
          exact (not_lt_of_ge hh) hi
        · have hk' : t.succ ≤ k := by
            simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
            omega
          have hh := (D.diagonalLabel_strictAnti c).antitone hk'
          have hi := (D.symmetric_interlacing c t).1
          rw [he] at hi
          exact (not_lt_of_ge hh) hi
      simp [hne, hti, not_le.mpr htj]
    · rw [ite_eq_right htj]
      have htj' : j ≤ t.castSucc := le_of_not_gt htj
      simp only [hti, false_and, htj', true_and, false_or]
      exact (D.diagonalLabel_strictAnti c).injective.eq_iff

/-- A diagonal generator occurs exactly outside the deleted interval.
This is the coefficient-level distinctness argument behind `eq:symmetric-leader`. -/
theorem symmetric_exponent_diagonal_pos_iff (hd : D.Dense) {c : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev)
    (i j : Fin (n + 1)) (hij : i ≤ j) (k : Fin (n + 1)) :
    0 < D.symmetricMinorExponent hd hc i j
      ⟨(D.diagonalLabel c k).toNat, by have := D.diagonalLabel_pos hd hc k; omega⟩ ↔
      k < i ∨ j < k := by
  classical
  let z : ℕ+ := ⟨(D.diagonalLabel c k).toNat, by
    have := D.diagonalLabel_pos hd hc k; omega⟩
  have heq (t : Fin n) :
      positiveSumIndex (D.row ∘ i.succAbove) (D.row ∘ j.succAbove) c
        (fun a b => D.symmetric_sum_pos hd hc _ _) t t = z ↔
      (t.castSucc < i ∧ t.castSucc = k) ∨ (j ≤ t.castSucc ∧ t.succ = k) := by
    rw [← D.identity_label_diagonal_iff c i j hij t k]
    constructor
    · intro h
      have h' := congrArg (fun x : ℕ+ => (x.val : ℤ)) h
      simpa [positiveSumIndex, z, Int.toNat_of_nonneg
        (D.symmetric_sum_pos hd hc _ _).le,
        Int.toNat_of_nonneg (D.diagonalLabel_pos hd hc k).le] using h'
    · intro h
      apply Subtype.ext
      exact congrArg Int.toNat h
  change 0 < (∑ t : Fin n, Finsupp.single
    (positiveSumIndex (D.row ∘ i.succAbove) (D.row ∘ j.succAbove) c
      (fun a b => D.symmetric_sum_pos hd hc _ _) t t) 1) z ↔ _
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_pos_iff_of_nonneg]
  · constructor
    · rintro ⟨t, _, ht⟩
      have he : positiveSumIndex (D.row ∘ i.succAbove) (D.row ∘ j.succAbove) c
          (fun a b => D.symmetric_sum_pos hd hc _ _) t t = z := by
        split_ifs at ht with h <;> simp_all
      rcases (heq t).mp he with ⟨h, rfl⟩ | ⟨h, rfl⟩
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_lt h t.castSucc_lt_succ)
    · intro h
      rcases h with hki | hjk
      · let t : Fin n := ⟨k.val, by have := i.isLt; omega⟩
        refine ⟨t, Finset.mem_univ _, ?_⟩
        have he : positiveSumIndex (D.row ∘ i.succAbove) (D.row ∘ j.succAbove) c
            (fun a b => D.symmetric_sum_pos hd hc _ _) t t = z :=
          (heq t).mpr (Or.inl ⟨hki, by ext; rfl⟩)
        simp [he]
      · let t : Fin n := ⟨k.val - 1, by have := k.isLt; omega⟩
        refine ⟨t, Finset.mem_univ _, ?_⟩
        have he : positiveSumIndex (D.row ∘ i.succAbove) (D.row ∘ j.succAbove) c
            (fun a b => D.symmetric_sum_pos hd hc _ _) t t = z :=
          (heq t).mpr (Or.inr ⟨by change j.val ≤ k.val - 1; omega,
            by ext; change k.val - 1 + 1 = k.val; omega⟩)
        simp [he]
  · intro t _; positivity

/-- Distinct intervals give distinct leader monomials, including diagonal sites. -/
theorem symmetricMinorExponent_injective (hd : D.Dense) {c : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev) :
    Function.Injective (fun s : {s : Fin (n + 1) × Fin (n + 1) // s.1 ≤ s.2} =>
      D.symmetricMinorExponent hd hc s.1.1 s.1.2) := by
  intro s t he
  change D.symmetricMinorExponent hd hc s.1.1 s.1.2 =
    D.symmetricMinorExponent hd hc t.1.1 t.1.2 at he
  have hp (k : Fin (n + 1)) :
      (k < s.1.1 ∨ s.1.2 < k) ↔ (k < t.1.1 ∨ t.1.2 < k) := by
    let z : ℕ+ := ⟨(D.diagonalLabel c k).toNat, by
      have := D.diagonalLabel_pos hd hc k
      omega⟩
    calc
      (k < s.1.1 ∨ s.1.2 < k) ↔
          0 < D.symmetricMinorExponent hd hc s.1.1 s.1.2 z :=
        (D.symmetric_exponent_diagonal_pos_iff hd hc s.1.1 s.1.2 s.2 k).symm
      _ ↔ 0 < D.symmetricMinorExponent hd hc t.1.1 t.1.2 z := by rw [he]
      _ ↔ (k < t.1.1 ∨ t.1.2 < k) :=
        D.symmetric_exponent_diagonal_pos_iff hd hc t.1.1 t.1.2 t.2 k
  have hl : s.1.1 = t.1.1 := by
    apply le_antisymm
    · by_contra h
      have hs := (hp t.1.1).mp (Or.inl (lt_of_not_ge h))
      have horder := t.2
      omega
    · by_contra h
      have hs := (hp s.1.1).mpr (Or.inl (lt_of_not_ge h))
      have horder := s.2
      omega
  have hr : s.1.2 = t.1.2 := by
    apply le_antisymm
    · by_contra h
      have hh := (hp s.1.2).mpr (Or.inr (lt_of_not_ge h))
      have horder := s.2
      omega
    · by_contra h
      have hh := (hp t.1.2).mp (Or.inr (lt_of_not_ge h))
      have horder := t.2
      omega
  apply Subtype.ext
  exact Prod.ext hl hr

/-- Original signed cofactors are a nonzero scalar times the corresponding symmetric minors. -/
theorem cofactor_eq_symmetricMinor {c : ℤ}
    (hc : ∀ j, D.col j = c - D.row j.rev) (i j : Fin (n + 1)) :
    D.cofactor i j =
      (((-1 : ℚ) ^ (i.val + j.val)) *
        (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ)) •
        D.symmetricMinor c i j.rev := by
  have hm : D.matrix.submatrix i.succAbove j.succAbove =
      (Matrix.of (fun a b : Fin n => complete
        (D.row (i.succAbove a) + D.row (j.rev.succAbove b) - c))).submatrix id Fin.rev := by
    ext a b
    simp only [matrix, Matrix.of_apply, Matrix.submatrix_apply, id_eq, hc,
      Fin.succAbove_rev_right, Fin.rev_rev]
    congr 1
    ring_nf
  change D.matrix.submatrix i.succAbove j.succAbove =
    (Matrix.of (fun a b : Fin n => complete
      (D.row (i.succAbove a) + D.row (j.rev.succAbove b) - c))).submatrix id
        (Fin.revPerm : Equiv.Perm (Fin n)) at hm
  rw [cofactor, hm, Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n))]
  rcases Int.units_eq_one_or (Equiv.Perm.sign
    (Fin.revPerm : Equiv.Perm (Fin n))) with hsign | hsign
  all_goals simp [hsign, symmetricMinor, smul_eq_C_mul]

end BetaDiagram

variable {n : ℕ}

/-- The selected half is independent over the rationals, with the specified cofactor signs. -/
theorem symmetric_cofactor_representatives_independent (D : BetaDiagram (n + 1))
    (hd : D.Dense) (hs : D.Symmetric) :
    LinearIndependent ℚ (fun s : CofactorRepresentative (n + 1) =>
      D.cofactor s.1.1 s.1.2) := by
  classical
  obtain ⟨c, hc⟩ := BetaDiagram.Symmetric.exists_center D hs
  let e : CofactorRepresentative (n + 1) ≃
      {s : Fin (n + 1) × Fin (n + 1) // s.1 ≤ s.2} :=
    { toFun := fun s => ⟨(s.1.1, s.1.2.rev), s.2⟩
      invFun := fun s => ⟨(s.1.1, s.1.2.rev), by simpa using s.2⟩
      left_inv := by intro s; apply Subtype.ext; simp
      right_inv := by intro s; apply Subtype.ext; simp }
  have hi := linearIndependent_of_monomial_initial
    (fun s : {s : Fin (n + 1) × Fin (n + 1) // s.1 ≤ s.2} =>
      D.symmetricMinor c s.1.1 s.1.2)
    (fun s => D.symmetricMinorExponent hd hc s.1.1 s.1.2) (fun _ => 1)
    (by simp) (D.symmetricMinorExponent_injective hd hc)
    (fun s => D.symmetricMinor_initialForm hd hc s.1.1 s.1.2)
  have hi' := hi.comp e e.injective
  let u : CofactorRepresentative (n + 1) → ℚ := fun s =>
    (-1 : ℚ) ^ (s.1.1.val + s.1.2.val) *
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ)
  have hu : ∀ s, u s ≠ 0 := by
    intro s
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact_mod_cast (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))).ne_zero
  convert hi'.units_smul (fun s => Units.mk0 (u s) (hu s)) using 1
  funext s
  exact D.cofactor_eq_symmetricMinor hc s.1.1 s.1.2

/-- Total coefficient-to-polynomial map for the actual signed cofactors. -/
noncomputable def cofactorRelationMap (D : BetaDiagram (n + 1)) :
    (Fin (n + 1) × Fin (n + 1) → ℚ) →ₗ[ℚ] CompleteRing where
  toFun c := ∑ s, c s • D.cofactor s.1 s.2
  map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro a b; simp [mul_smul, Finset.smul_sum]

/-- The linear image is the span of all the actual cofactor polynomials. -/
theorem cofactorRelationMap_range (D : BetaDiagram (n + 1)) :
    LinearMap.range (cofactorRelationMap D) = Submodule.span ℚ
      (Set.range fun s : Fin (n + 1) × Fin (n + 1) => D.cofactor s.1 s.2) := by
  classical
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    change (∑ s, c s • D.cofactor s.1 s.2) ∈ _
    apply Submodule.sum_mem
    intro s _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    refine ⟨Pi.single s 1, ?_⟩
    simp [cofactorRelationMap, Pi.single_apply]

/-- The canonical site in a secondary-diagonal orbit. -/
def cofactorCanonical (s : Fin (n + 1) × Fin (n + 1)) : CofactorRepresentative (n + 1) :=
  if h : s.1 ≤ s.2.rev then ⟨s, h⟩
  else ⟨siteReflection s, by
    simpa only [siteReflection, Fin.rev_rev] using le_of_lt (lt_of_not_ge h)⟩

@[simp] theorem cofactorCanonical_representative (s : CofactorRepresentative (n + 1)) :
    cofactorCanonical s.1 = s := by simp [cofactorCanonical, s.2]

theorem cofactorCanonical_reflection (s : Fin (n + 1) × Fin (n + 1)) :
    cofactorCanonical (siteReflection s) = cofactorCanonical s := by
  by_cases h : s.1 ≤ s.2.rev
  · by_cases heq : s.1 = s.2.rev
    · have href : siteReflection s = s := by
        apply Prod.ext
        · exact heq.symm
        · apply Fin.rev_injective
          simpa only [siteReflection, Fin.rev_rev] using heq
      rw [href]
    · have hr : ¬(siteReflection s).1 ≤ (siteReflection s).2.rev := by
        simpa only [siteReflection, Fin.rev_rev] using
          not_le.mpr (lt_of_le_of_ne h heq)
      simp only [cofactorCanonical, dite_eq_left h, dite_eq_right hr, siteReflection_involutive]
  · have hr : (siteReflection s).1 ≤ (siteReflection s).2.rev := by
      simpa only [siteReflection, Fin.rev_rev] using le_of_lt (lt_of_not_ge h)
    simp only [cofactorCanonical, dite_eq_left hr, dite_eq_right h]

private theorem cofactorCanonical_value (D : BetaDiagram (n + 1)) (hs : D.Symmetric)
    (s : Fin (n + 1) × Fin (n + 1)) :
    D.cofactor (cofactorCanonical s).1.1 (cofactorCanonical s).1.2 = D.cofactor s.1 s.2 := by
  unfold cofactorCanonical
  split_ifs
  · rfl
  · exact (D.symmetric_cofactor_eq hs s.1 s.2).symm

/-- Add the coefficients belonging to the same cofactor orbit. -/
noncomputable def cofactorOrbitProjection :
    (Fin (n + 1) × Fin (n + 1) → ℚ) →ₗ[ℚ]
      (CofactorRepresentative (n + 1) → ℚ) where
  toFun c r := ∑ s, if cofactorCanonical s = r then c s else 0
  map_add' := by
    intro a b
    ext r
    change (∑ s, if cofactorCanonical s = r then a s + b s else 0) =
      (∑ s, if cofactorCanonical s = r then a s else 0) +
        ∑ s, if cofactorCanonical s = r then b s else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : cofactorCanonical s = r <;> simp [h]
  map_smul' := by intro a b; ext r; simp [mul_ite, Finset.mul_sum]

/-- Grouping the actual finite determinant relation by reflection orbits. -/
theorem cofactorRelationMap_factor (D : BetaDiagram (n + 1)) (hs : D.Symmetric)
    (c : Fin (n + 1) × Fin (n + 1) → ℚ) :
    cofactorRelationMap D c = ∑ r : CofactorRepresentative (n + 1),
      cofactorOrbitProjection c r • D.cofactor r.1.1 r.1.2 := by
  classical
  change (∑ s, c s • D.cofactor s.1 s.2) =
    ∑ r : CofactorRepresentative (n + 1),
      (∑ s, if cofactorCanonical s = r then c s else 0) • D.cofactor r.1.1 r.1.2
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single (cofactorCanonical s)]
  · simp [cofactorCanonical_value D hs]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

/-- The orbit-sum equations characterize every rational cofactor relation. -/
theorem symmetric_relation_iff_orbit_sums (D : BetaDiagram (n + 1))
    (hd : D.Dense) (hs : D.Symmetric) (c : Fin (n + 1) × Fin (n + 1) → ℚ) :
    cofactorRelationMap D c = 0 ↔ cofactorOrbitProjection c = 0 := by
  rw [cofactorRelationMap_factor D hs]
  constructor
  · intro h
    exact funext ((Fintype.linearIndependent_iff.mp
      (symmetric_cofactor_representatives_independent D hd hs)) _ h)
  · intro h; simp [h]

private theorem sum_coordinate_single {α : Type*} [Fintype α] [DecidableEq α]
    (c : α → ℚ) :
    (∑ x, c x • (Pi.single x (1 : ℚ) : α → ℚ)) = c := by
  classical
  ext y
  simp [Pi.single_apply]

/-- The full relation kernel is exactly the coordinate-difference span. -/
theorem symmetric_cofactor_kernel (D : BetaDiagram (n + 1))
    (hd : D.Dense) (hs : D.Symmetric) :
    LinearMap.ker (cofactorRelationMap D) = Submodule.span ℚ
      (Set.range (fun s : Fin (n + 1) × Fin (n + 1) =>
        Pi.single s (1 : ℚ) - Pi.single (siteReflection s) 1)) := by
  classical
  let W : Submodule ℚ (Fin (n + 1) × Fin (n + 1) → ℚ) :=
    Submodule.span ℚ (Set.range fun s => Pi.single s (1 : ℚ) - Pi.single (siteReflection s) 1)
  apply le_antisymm
  · intro c hc
    have hp : cofactorOrbitProjection c = 0 :=
      (symmetric_relation_iff_orbit_sums D hd hs c).mp hc
    have hz : (∑ s, c s • Pi.single (cofactorCanonical s).1 (1 : ℚ)) = 0 := by
      ext x
      change (∑ s, c s • Pi.single (cofactorCanonical s).1 (1 : ℚ)) x = 0
      by_cases hx : x.1 ≤ x.2.rev
      · have hh := congrFun hp ⟨x, hx⟩
        simpa [cofactorOrbitProjection, Pi.single_apply, Subtype.ext_iff, eq_comm] using hh
      · have hh : ∀ s, (cofactorCanonical s).1 ≠ x := by
          intro s h
          have h' := (cofactorCanonical s).2
          rw [h] at h'
          exact hx h'
        simp [hh]
    have hc' : c = ∑ s, c s • (Pi.single s (1 : ℚ) -
        Pi.single (cofactorCanonical s).1 1) := by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, sum_coordinate_single, hz, sub_zero]
    rw [hc']
    apply Submodule.sum_mem
    intro s _
    apply Submodule.smul_mem
    unfold cofactorCanonical
    split_ifs with h
    · simp
    · exact Submodule.subset_span ⟨s, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change cofactorRelationMap D (Pi.single s 1 - Pi.single (siteReflection s) 1) = 0
    rw [map_sub]
    have he (x : Fin (n + 1) × Fin (n + 1)) :
        cofactorRelationMap D (Pi.single x 1) = D.cofactor x.1 x.2 := by
      change (∑ y, (Pi.single x (1 : ℚ) : Fin (n + 1) × Fin (n + 1) → ℚ) y •
        D.cofactor y.1 y.2) =
        D.cofactor x.1 x.2
      simp [Pi.single_apply]
    rw [he, he]
    exact sub_eq_zero.mpr (D.symmetric_cofactor_eq hs s.1 s.2)

/-- The range is the span of the independent representative half. -/
theorem symmetric_cofactor_image (D : BetaDiagram (n + 1)) (hs : D.Symmetric) :
    LinearMap.range (cofactorRelationMap D) = Submodule.span ℚ
      (Set.range (fun s : CofactorRepresentative (n + 1) => D.cofactor s.1.1 s.1.2)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [cofactorRelationMap_factor D hs]
    apply Submodule.sum_mem
    intro r _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    refine ⟨Pi.single r.1 1, ?_⟩
    simp [cofactorRelationMap, Pi.single_apply]

/-- Representatives are the unordered pairs of row indices after column reversal. -/
noncomputable def cofactorRepresentativeEquivSym2 (m : ℕ) :
    CofactorRepresentative m ≃ Sym2 (Fin m) where
  toFun s := s(s.1.1, s.1.2.rev)
  invFun := Sym2.lift ⟨(fun a b =>
    (⟨(min a b, (max a b).rev), by simp⟩ : CofactorRepresentative m)),
    by intro a b; apply Subtype.ext; simp [min_comm, max_comm]⟩
  left_inv := by
    intro s
    apply Subtype.ext
    simp [min_eq_left s.2, max_eq_right s.2]
  right_inv := by
    intro s
    induction s using Sym2.ind with
    | _ a b =>
      simp only [Sym2.lift_mk, Fin.rev_rev]
      rcases le_total a b with h | h
      · simp [min_eq_left h, max_eq_right h]
      · simp [min_eq_right h, max_eq_left h, Sym2.eq_swap]

/-- The exact number of independent representatives, not merely an upper bound. -/
theorem card_cofactorRepresentative (m : ℕ) :
    Fintype.card (CofactorRepresentative m) = m * (m + 1) / 2 := by
  rw [Fintype.card_congr (cofactorRepresentativeEquivSym2 m), Sym2.card, Fintype.card_fin]
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

/-- Exact rational rank in the symmetric clause of `thm:cofactor-relations`. -/
theorem symmetric_cofactor_rank (D : BetaDiagram (n + 1))
    (hd : D.Dense) (hs : D.Symmetric) :
    Module.finrank ℚ (LinearMap.range (cofactorRelationMap D)) = (n + 1) * (n + 2) / 2 := by
  rw [symmetric_cofactor_image D hs,
    finrank_span_eq_card (symmetric_cofactor_representatives_independent D hd hs),
    card_cofactorRepresentative]

/-- The span dimension in the manuscript, expressed without the coefficient map. -/
theorem symmetric_cofactor_span_rank (D : BetaDiagram (n + 1))
    (hd : D.Dense) (hs : D.Symmetric) :
    Module.finrank ℚ (Submodule.span ℚ
      (Set.range fun s : Fin (n + 1) × Fin (n + 1) => D.cofactor s.1 s.2)) =
      (n + 1) * (n + 2) / 2 := by
  rw [← cofactorRelationMap_range]
  exact symmetric_cofactor_rank D hd hs

/-- All clauses for the actual cofactors, with only the paper's structural hypotheses. -/
theorem symmetric_cofactor_relations (D : BetaDiagram (n + 1))
    (hd : D.Dense) (hs : D.Symmetric) :
    (∀ i j, D.cofactor i j = D.cofactor j.rev i.rev) ∧
    LinearIndependent ℚ (fun s : CofactorRepresentative (n + 1) =>
      D.cofactor s.1.1 s.1.2) ∧
    LinearMap.ker (cofactorRelationMap D) = Submodule.span ℚ
      (Set.range (fun s : Fin (n + 1) × Fin (n + 1) =>
        Pi.single s (1 : ℚ) - Pi.single (siteReflection s) 1)) ∧
    Module.finrank ℚ (LinearMap.range (cofactorRelationMap D)) = (n + 1) * (n + 2) / 2 :=
  ⟨D.symmetric_cofactor_eq hs, symmetric_cofactor_representatives_independent D hd hs,
    symmetric_cofactor_kernel D hd hs, symmetric_cofactor_rank D hd hs⟩

end SkewCofactorIndependence
