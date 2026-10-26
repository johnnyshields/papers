/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/RestorationComponents.lean

import SkewJacobiNegative.RestorationGeometry
import SkewJacobiNegative.StrictTriangularPaths
import SkewJacobiNegative.OrdinaryReadings

/-!
# Exact marked determinants of sorted restorations

The actual permutation regrouping, terminating path expansion, and ordinary
components in `prop:path-expansion` and `eq:first-components` of
`shields-2026-skew-cofactor-independence.tex`.
-/

namespace SkewJacobiNegative

open scoped BigOperators Polynomial
open StrictTriangularPaths BetaEndpointCounts

/-- Marks the ordinary number of positive complete generators. -/
noncomputable def markOrdinary : CompleteRing →+* Polynomial CompleteRing :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j => Polynomial.X * Polynomial.C (MvPolynomial.X j))

theorem markOrdinary_complete (a : ℤ) :
    markOrdinary (complete a) =
      if a = 0 then 1 else Polynomial.X * Polynomial.C (complete a) := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · simp [complete_of_neg h, ne_of_lt h]
  · simp [markOrdinary]
  · rw [complete_of_pos h, ite_eq_right (ne_of_gt h)]
    exact MvPolynomial.eval₂Hom_X' _ _ _

/-- An ordinary component is read as a coefficient of the exact marking homomorphism. -/
noncomputable def ordinaryComponent (p : CompleteRing) (d : ℕ) : CompleteRing :=
  (markOrdinary p).coeff d

/-- Marking a monomial records its actual ordinary exponent sum. -/
theorem markOrdinary_monomial (d : ℕ+ →₀ ℕ) (r : ℚ) :
    markOrdinary (MvPolynomial.monomial d r) =
      Polynomial.C (MvPolynomial.monomial d r) * Polynomial.X ^ d.degree := by
  classical
  rw [markOrdinary, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← Polynomial.C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [MvPolynomial.monomial_eq, Finsupp.prod, Polynomial.C_mul, Finsupp.degree_apply]
  ring

/-- The coefficient convention agrees exactly with Mathlib's ordinary homogeneous component. -/
theorem ordinaryComponent_eq_homogeneousComponent (p : CompleteRing) (d : ℕ) :
    ordinaryComponent p d = MvPolynomial.homogeneousComponent d p := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply]
  unfold ordinaryComponent
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp only [markOrdinary_monomial, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : v.degree = d
  · simp [h]
  · simp [h, Ne.symm h]

namespace BetaDiagram

variable {k m : ℕ}

/-- A strict enumeration is a genuine equivalence with its image subtype. -/
noncomputable def enumerationEquiv (f : Fin k → ℤ) (hf : Function.Injective f) :
    Fin k ≃ ↥(Finset.univ.image f) :=
  Equiv.ofBijective (fun i => ⟨f i, by
    classical
    simp⟩) (by
    constructor
    · intro i j h
      exact hf (congrArg Subtype.val h)
    · rintro ⟨z, hz⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      exact ⟨i, Subtype.ext hi⟩)

/-- Concatenating disjoint strict lists gives a literal union enumeration. -/
noncomputable def unionEnumeration (f : Fin k → ℤ) (hf : Function.Injective f)
    (Z : Finset ℤ) (hdis : Disjoint (Finset.univ.image f) Z) :
    (Fin k ⊕ Fin Z.card) ≃ ↥((Finset.univ.image f) ∪ Z) :=
  Equiv.ofBijective
    (fun u => match u with
      | Sum.inl i => ⟨f i, by
          classical
          simp⟩
      | Sum.inr j => ⟨descending Z rfl j,
          Finset.mem_union_right _ (descending_mem Z rfl j)⟩)
    (by
      classical
      constructor
      · intro u v he
        have hv := congrArg Subtype.val he
        cases u with
        | inl i =>
          cases v with
          | inl j => exact congrArg Sum.inl (hf hv)
          | inr j =>
            change f i = descending Z rfl j at hv
            have hm : f i ∈ Finset.univ.image f :=
              Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
            have hz : f i ∈ Z := hv.symm ▸ descending_mem Z rfl j
            exact False.elim (Finset.disjoint_left.mp hdis hm hz)
        | inr i =>
          cases v with
          | inl j =>
            change descending Z rfl i = f j at hv
            have hm : f j ∈ Finset.univ.image f :=
              Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
            have hz : f j ∈ Z := hv ▸ descending_mem Z rfl i
            exact False.elim (Finset.disjoint_left.mp hdis hm hz)
          | inr j => exact congrArg Sum.inr ((descending_strictAnti Z rfl).injective hv)
      · rintro ⟨z, hz⟩
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
          exact ⟨Sum.inl i, Subtype.ext hi⟩
        · obtain ⟨j, hj⟩ := descending_surjective Z rfl hz
          exact ⟨Sum.inr j, Subtype.ext hj⟩)

/-- Regroups actual sorted coordinates as old endpoints followed by common endpoints. -/
noncomputable def regroup (f : Fin k → ℤ) (hf : Function.Injective f)
    (Z : Finset ℤ) (hdis : Disjoint (Finset.univ.image f) Z)
    (g : Fin (k + Z.card) → ℤ) (hg : Function.Injective g)
    (he : Finset.univ.image g = (Finset.univ.image f) ∪ Z) :
    (Fin k ⊕ Fin Z.card) ≃ Fin (k + Z.card) :=
  (unionEnumeration f hf Z hdis).trans
    ((Equiv.subtypeEquivRight
      (p := fun z : ℤ => z ∈ (Finset.univ.image f) ∪ Z)
      (q := fun z : ℤ => z ∈ Finset.univ.image g)
      (fun z => by rw [he])).trans
      (enumerationEquiv g hg).symm)

theorem regroup_apply (f : Fin k → ℤ) (hf : Function.Injective f)
    (Z : Finset ℤ) (hdis : Disjoint (Finset.univ.image f) Z)
    (g : Fin (k + Z.card) → ℤ) (hg : Function.Injective g)
    (he : Finset.univ.image g = (Finset.univ.image f) ∪ Z)
    (u : Fin k ⊕ Fin Z.card) :
    g (regroup f hf Z hdis g hg he u) =
      Sum.elim f (descending Z rfl) u := by
  change ((enumerationEquiv g hg) ((enumerationEquiv g hg).symm
    ((Equiv.subtypeEquivRight
      (p := fun z : ℤ => z ∈ (Finset.univ.image f) ∪ Z)
      (q := fun z : ℤ => z ∈ Finset.univ.image g)
      (fun z => by rw [he])) ((unionEnumeration f hf Z hdis) u)))).val = _
  rw [Equiv.apply_symm_apply]
  cases u <;> rfl

/-- The two actual regrouping permutations and their product sign. -/
noncomputable def deletionSign (C : BetaDiagram k) (Z : Finset ℤ)
    (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) : ℤˣ :=
  Equiv.Perm.sign ((finSumFinEquiv : (Fin k ⊕ Fin Z.card) ≃ Fin (k + Z.card)).symm.trans
    (regroup C.row C.row_strictAnti.injective Z hr D.row D.row_strictAnti.injective er)) *
  Equiv.Perm.sign ((finSumFinEquiv : (Fin k ⊕ Fin Z.card) ≃ Fin (k + Z.card)).symm.trans
    (regroup C.col C.col_strictAnti.injective Z hc D.col D.col_strictAnti.injective ec))

theorem deletionSign_square (C : BetaDiagram k) (Z : Finset ℤ)
    (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) :
    ((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing) ^ 2 = 1 := by
  rcases Int.units_eq_one_or (C.deletionSign Z hr hc D er ec) with hu | hu <;>
    simp [hu]

/-- The marked original matrix is exactly the four-block matrix, not merely equideterminantal. -/
theorem regroup_marked_matrix (C : BetaDiagram k) (hZero : C.ZeroFree) (Z : Finset ℤ)
    (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) :
    (D.matrix.map markOrdinary).submatrix
      (regroup C.row C.row_strictAnti.injective Z hr D.row D.row_strictAnti.injective er)
      (regroup C.col C.col_strictAnti.injective Z hc D.col D.col_strictAnti.injective ec) =
      Matrix.fromBlocks
        ((Polynomial.X : Polynomial CompleteRing) •
          C.matrix.map (Polynomial.C : CompleteRing → Polynomial CompleteRing))
        ((Polynomial.X : Polynomial CompleteRing) •
          (positiveMatrix complete C.row (descending Z rfl)).map
            (Polynomial.C : CompleteRing → Polynomial CompleteRing))
        ((Polynomial.X : Polynomial CompleteRing) •
          (positiveMatrix complete (descending Z rfl) C.col).map
            (Polynomial.C : CompleteRing → Polynomial CompleteRing))
        ((1 : Matrix (Fin Z.card) (Fin Z.card) (Polynomial CompleteRing)) +
          (Polynomial.X : Polynomial CompleteRing) •
            (positiveMatrix complete (descending Z rfl) (descending Z rfl)).map
              (Polynomial.C : CompleteRing → Polynomial CompleteRing)) := by
  classical
  apply Matrix.ext
  intro u v
  simp only [Matrix.submatrix_apply, Matrix.map_apply, matrix, Matrix.of_apply]
  have hrCoord := regroup_apply C.row C.row_strictAnti.injective Z hr
    D.row D.row_strictAnti.injective er u
  have hcCoord := regroup_apply C.col C.col_strictAnti.injective Z hc
    D.col D.col_strictAnti.injective ec v
  rw [hrCoord, hcCoord]
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      simp [markOrdinary_complete, sub_eq_zero, hZero i j, Matrix.smul_apply, smul_eq_mul]
    | inr j =>
      have hn : C.row i ≠ descending Z rfl j := by
        intro he
        exact Finset.disjoint_left.mp hr (by simp [rowSet])
          (he.symm ▸ descending_mem Z rfl j)
      simp [markOrdinary_complete, sub_eq_zero, hn, positiveMatrix,
        positiveGap_complete_of_ne hn, Matrix.smul_apply, smul_eq_mul]
  | inr i =>
    cases v with
    | inl j =>
      have hn : descending Z rfl i ≠ C.col j := by
        intro he
        exact Finset.disjoint_left.mp hc (by simp [colSet])
          (he ▸ descending_mem Z rfl i)
      simp [markOrdinary_complete, sub_eq_zero, hn, positiveMatrix,
        positiveGap_complete_of_ne hn, Matrix.smul_apply, smul_eq_mul]
    | inr j =>
      by_cases hij : i = j
      · subst j
        simp [positiveMatrix, positiveGap_self,
          Matrix.smul_apply, smul_eq_mul]
      · have hn := (descending_strictAnti Z rfl).injective.ne hij
        simp [markOrdinary_complete, sub_eq_zero, hn, positiveMatrix,
          positiveGap_complete_of_ne hn, hij,
          Matrix.smul_apply, smul_eq_mul]

/-- Product of the row and column signs is the exact deletion sign. -/
theorem regroup_marked_det (C : BetaDiagram k) (hZero : C.ZeroFree) (Z : Finset ℤ)
    (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) :
    markOrdinary D.schur =
      Polynomial.C (((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing)) *
      (Matrix.fromBlocks
        ((Polynomial.X : Polynomial CompleteRing) •
          C.matrix.map (Polynomial.C : CompleteRing → Polynomial CompleteRing))
        ((Polynomial.X : Polynomial CompleteRing) •
          (positiveMatrix complete C.row (descending Z rfl)).map
            (Polynomial.C : CompleteRing → Polynomial CompleteRing))
        ((Polynomial.X : Polynomial CompleteRing) •
          (positiveMatrix complete (descending Z rfl) C.col).map
            (Polynomial.C : CompleteRing → Polynomial CompleteRing))
        ((1 : Matrix (Fin Z.card) (Fin Z.card) (Polynomial CompleteRing)) +
          (Polynomial.X : Polynomial CompleteRing) •
            (positiveMatrix complete (descending Z rfl) (descending Z rfl)).map
              (Polynomial.C : CompleteRing → Polynomial CompleteRing))).det := by
  classical
  let e := (finSumFinEquiv : (Fin k ⊕ Fin Z.card) ≃ Fin (k + Z.card))
  let r := regroup C.row C.row_strictAnti.injective Z hr D.row D.row_strictAnti.injective er
  let c := regroup C.col C.col_strictAnti.injective Z hc D.col D.col_strictAnti.injective ec
  let rp := e.symm.trans r
  let cp := e.symm.trans c
  have hd : ((D.matrix.map markOrdinary).submatrix r c).det =
      Polynomial.C (((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing)) *
        markOrdinary D.schur := by
    have hm : (D.matrix.map markOrdinary).submatrix r c =
        (((D.matrix.map markOrdinary).submatrix id cp).submatrix rp id).submatrix e e := by
      apply Matrix.ext
      intro i j
      simp only [Matrix.submatrix_apply, rp, cp, Equiv.trans_apply,
        Equiv.symm_apply_apply, id_eq]
    have hmap : (D.matrix.map markOrdinary).det = markOrdinary D.schur :=
      (markOrdinary.map_det D.matrix).symm
    rw [hm, Matrix.det_submatrix_equiv_self, Matrix.det_permute,
      Matrix.det_permute', hmap]
    simp [deletionSign, rp, cp, r, c, e, schur, Polynomial.C_mul, mul_assoc]
  rw [C.regroup_marked_matrix hZero Z hr hc D er ec] at hd
  have hs : (Polynomial.C (((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing))) ^ 2 = 1 := by
    rw [← Polynomial.C_pow, C.deletionSign_square, Polynomial.C_1]
  calc
    markOrdinary D.schur =
        Polynomial.C (((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing)) *
          (Polynomial.C (((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing)) *
            markOrdinary D.schur) := by rw [← mul_assoc, ← pow_two, hs, one_mul]
    _ = _ := by rw [← hd]

theorem positiveMatrix_eq_matrix (C : BetaDiagram k) (hZero : C.ZeroFree) :
    positiveMatrix complete C.row C.col = C.matrix := by
  apply Matrix.ext
  intro i j
  exact positiveGap_complete_of_ne (hZero i j)

/-- The terminating determinant path expansion in `prop:path-expansion`. -/
theorem restoration_path_expansion (C : BetaDiagram k) (hZero : C.ZeroFree)
    (Z : Finset ℤ) (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) :
    markOrdinary D.schur =
      Polynomial.C (((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing)) *
        Polynomial.X ^ k *
        (RestorationPaths.reduced Polynomial.X (C.matrix.map Polynomial.C)
          ((positiveMatrix complete C.row (descending Z rfl)).map Polynomial.C)
          ((positiveMatrix complete (descending Z rfl) C.col).map Polynomial.C)
          ((positiveMatrix complete (descending Z rfl) (descending Z rfl)).map
            Polynomial.C)).det := by
  rw [regroup_marked_det C hZero Z hr hc D er ec,
    RestorationPaths.block_det]
  · ring
  · intro i j hij
    simp only [Matrix.map_apply]
    rw [positiveMatrix_strictUpper complete (descending Z rfl)
      (descending_strictAnti Z rfl) i j hij, Polynomial.C_0]

/-- The lowest and next components in `eq:first-components`, including the deletion sign. -/
theorem restoration_first_coefficients (C : BetaDiagram (k + 1)) (hZero : C.ZeroFree)
    (Z : Finset ℤ) (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + 1 + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) :
    ordinaryComponent D.schur (k + 1) =
        (((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing)) * C.schur ∧
      ordinaryComponent D.schur (k + 2) =
        -(((C.deletionSign Z hr hc D er ec : ℤ) : CompleteRing)) *
          ∑ z ∈ Z, C.unitVariation z := by
  classical
  have hp := path_marking_first_coefficients_cofactors complete C.row C.col
    (descending Z rfl) (descending_strictAnti Z rfl)
  rw [positiveMatrix_eq_matrix C hZero] at hp
  have hsum : (∑ z : Fin Z.card, ∑ j : Fin (k + 1), ∑ i : Fin (k + 1),
      ((-1) ^ (i.val + j.val) * (C.matrix.submatrix i.succAbove j.succAbove).det) *
        positiveGap complete (C.row i) (descending Z rfl z) *
        positiveGap complete (descending Z rfl z) (C.col j)) =
      ∑ z ∈ Z, C.unitVariation z := by
    apply Finset.sum_bij (fun z _ => descending Z rfl z)
    · intro z hz
      exact descending_mem Z rfl z
    · intro z hz w hw he
      exact (descending_strictAnti Z rfl).injective he
    · intro z hz
      obtain ⟨i, hi⟩ := descending_surjective Z rfl hz
      exact ⟨i, Finset.mem_univ _, hi⟩
    · intro z hz
      exact Finset.sum_comm
  dsimp only at hp
  rw [hsum] at hp
  simp only [ordinaryComponent, regroup_marked_det C hZero Z hr hc D er ec,
    Polynomial.coeff_C_mul]
  constructor
  · rw [hp.1]
    rfl
  · rw [hp.2]
    ring

theorem restoration_coeff_below (C : BetaDiagram k) (hZero : C.ZeroFree)
    (Z : Finset ℤ) (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z)
    (d : ℕ) (hd : d < k) : ordinaryComponent D.schur d = 0 := by
  rw [ordinaryComponent, restoration_path_expansion C hZero Z hr hc D er ec]
  rw [mul_assoc, mul_comm (Polynomial.X ^ k), ← mul_assoc]
  simp [Polynomial.coeff_mul_X_pow', Nat.not_le_of_gt hd]

theorem restoration_lowest_nonzero (C : BetaDiagram (k + 1)) (hZero : C.ZeroFree)
    (Z : Finset ℤ) (hr : Disjoint C.rowSet Z) (hc : Disjoint C.colSet Z)
    (D : BetaDiagram (k + 1 + Z.card))
    (er : D.rowSet = C.rowSet ∪ Z) (ec : D.colSet = C.colSet ∪ Z) :
    ordinaryComponent D.schur (k + 1) ≠ 0 := by
  rw [(restoration_first_coefficients C hZero Z hr hc D er ec).1]
  apply mul_ne_zero _ C.schur_ne_zero
  have hs := C.deletionSign_square Z hr hc D er ec
  intro hz
  simp [hz] at hs

theorem restore_first_coefficients (C : BetaDiagram (k + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    let D := C.restore hC hZero Z hZ
    let hr := C.available_disjoint_rows Z hZ
    let hc := C.available_disjoint_cols Z hZ
    ordinaryComponent D.schur (k + 1) =
        (((C.deletionSign Z hr hc D (C.restore_rowSet hC hZero Z hZ)
          (C.restore_colSet hC hZero Z hZ) : ℤ) : CompleteRing)) * C.schur ∧
      ordinaryComponent D.schur (k + 2) =
        -(((C.deletionSign Z hr hc D (C.restore_rowSet hC hZero Z hZ)
          (C.restore_colSet hC hZero Z hZ) : ℤ) : CompleteRing)) *
          ∑ z ∈ Z, C.unitVariation z :=
  C.restoration_first_coefficients hZero Z _ _ _ _ _

/-- Literal strict-chain entries of the reduced actual restoration matrix (`eq:path-entry`). -/
theorem restoration_path_entry (C : BetaDiagram k) (hZero : C.ZeroFree)
    (Z : Finset ℤ) (i j : Fin k) :
    RestorationPaths.reduced Polynomial.X (C.matrix.map Polynomial.C)
      ((positiveMatrix complete C.row (descending Z rfl)).map Polynomial.C)
      ((positiveMatrix complete (descending Z rfl) C.col).map Polynomial.C)
      ((positiveMatrix complete (descending Z rfl) (descending Z rfl)).map Polynomial.C) i j =
      Polynomial.C (C.matrix i j) +
        ∑ r ∈ Finset.range Z.card, (-(Polynomial.X : Polynomial CompleteRing)) ^ (r + 1) *
          Polynomial.C
            (∑ p ∈ Finset.univ.filter
              (IsStrictChain (descending Z rfl) (C.row i) (C.col j) (r + 1)),
              chainProduct complete (descending Z rfl) (C.row i) (C.col j) (r + 1) p) := by
  have he := polynomial_reduced_entry complete C.row C.col (descending Z rfl) i j
  rw [C.positiveMatrix_eq_matrix hZero,
    positiveGap_complete_of_ne (hZero i j)] at he
  simpa only [matrix, Matrix.of_apply, orderedPathSum_eq_strict_sum] using he

/-- The literal chain sum vanishes past the number of restored common endpoints. -/
theorem restoration_path_terminates (C : BetaDiagram k) (Z : Finset ℤ)
    (r : ℕ) (hr : Z.card ≤ r) (i j : Fin k) :
    (∑ p ∈ Finset.univ.filter
      (IsStrictChain (descending Z rfl) (C.row i) (C.col j) (r + 1)),
      chainProduct complete (descending Z rfl) (C.row i) (C.col j) (r + 1) p) = 0 := by
  rw [← orderedPathSum_eq_strict_sum]
  exact orderedPathSum_eq_zero_of_card_le complete C.row C.col
    (descending Z rfl) (descending_strictAnti Z rfl) r hr i j

/-- The displayed terminating matrix-power series for an actual sorted restoration. -/
theorem restore_finite_series (C : BetaDiagram (k + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    let D := C.restore hC hZero Z hZ
    let L := C.matrix.map Polynomial.C
    let P := (positiveMatrix complete C.row (descending Z rfl)).map Polynomial.C
    let Q := (positiveMatrix complete (descending Z rfl) C.col).map Polynomial.C
    let T := (positiveMatrix complete (descending Z rfl) (descending Z rfl)).map Polynomial.C
    markOrdinary D.schur =
      Polynomial.C (((C.deletionSign Z (C.available_disjoint_rows Z hZ)
        (C.available_disjoint_cols Z hZ) D (C.restore_rowSet hC hZero Z hZ)
        (C.restore_colSet hC hZero Z hZ) : ℤ) : CompleteRing)) *
      Polynomial.X ^ (k + 1) *
        (L + ∑ r ∈ Finset.range Z.card,
          (-(Polynomial.X : Polynomial CompleteRing)) ^ (r + 1) • (P * T ^ r * Q)).det := by
  dsimp only
  rw [C.restoration_path_expansion hZero Z _ _ _
    (C.restore_rowSet hC hZero Z hZ) (C.restore_colSet hC hZero Z hZ),
    RestorationPaths.reduced_eq_sum]

theorem sum_rowSet (D : BetaDiagram k) : (∑ z ∈ D.rowSet, z) = ∑ i, D.row i := by
  classical
  exact Finset.sum_image (fun i _ j _ he => D.row_strictAnti.injective he)

theorem sum_colSet (D : BetaDiagram k) : (∑ z ∈ D.colSet, z) = ∑ i, D.col i := by
  classical
  exact Finset.sum_image (fun i _ j _ he => D.col_strictAnti.injective he)

/-- Restoration adds the same common beta sum to both endpoints, preserving area. -/
theorem restore_area (C : BetaDiagram (k + 1)) (hC : C.Connected)
    (hZero : C.ZeroFree) (Z : Finset ℤ) (hZ : Z ⊆ C.availablePositions) :
    (C.restore hC hZero Z hZ).area = C.area := by
  classical
  unfold area
  rw [← sum_rowSet, ← sum_colSet, restore_rowSet, restore_colSet,
    Finset.sum_union (C.available_disjoint_rows Z hZ),
    Finset.sum_union (C.available_disjoint_cols Z hZ),
    sum_rowSet C, sum_colSet C]
  ring

end BetaDiagram
end SkewJacobiNegative
