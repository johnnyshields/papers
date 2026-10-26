/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.PositiveBorders

/-!
# Coefficients of genuine positive borders

Actual complete-generator determinants for `lem:border` and `eq:border-square`
in «Boundary coefficients and propagation» (`sec:boundary-tools`).  The
complementary core may have negative entries and genuine index-zero units.
-/

namespace SkewJacobiNegative
namespace BetaDiagram

variable {n : ℕ}

/-- Positive corner feasibility survives literal rotation. -/
theorem rotate_positiveCorner (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner) :
    D.rotate.PositiveCorner := by
  intro i
  have h := hP i.rev
  simpa only [rotate, Fin.rev_succ, Fin.rev_castSucc] using (neg_lt_neg h)

set_option backward.isDefEq.respectTransparency false in
/-- Deleting the private second label realizes the top extension of the actual corner. -/
theorem border_top_minor (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner) :
    D.matrix.submatrix (0 : Fin (n + 2)).succ.succAbove
        (Fin.last (n + 2)).succAbove =
      ((D.cornerDiagram hP).extendTop
        D.topMargin D.topMargin_pos).matrix := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases with
  | zero =>
      simp only [Matrix.submatrix_apply, matrix, Matrix.of_apply,
        Fin.succ_succAbove_zero, Fin.succAbove_last,
        extendTop, cornerDiagram, ite_true]
      congr 1
      unfold topMargin
      ring
  | succ i =>
      simp only [Matrix.submatrix_apply, matrix, Matrix.of_apply,
        Fin.succ_succAbove_succ, Fin.zero_succAbove, Fin.succAbove_last,
        extendTop, cornerDiagram, Fin.succ_ne_zero, ite_false]

set_option backward.isDefEq.respectTransparency false in
/-- Actual polynomial coefficient at the private next-largest top exterior label. -/
theorem border_top_coefficient (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner)
    (hgap : D.topMargin < D.bottomMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram hP).extendTop
          D.topMargin D.topMargin_pos).schur := by
  classical
  dsimp only
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
    by have := D.exterior_top_label_pos; omega⟩
  let A := D.matrix.map (eraseGenerator N)
  have hMN : M ≠ N := by
    intro h
    have he := congrArg Subtype.val h
    have := D.topMargin_pos
    have := D.exterior_top_label_pos
    have := D.largestLabel_pos
    dsimp [M, N] at he
    omega
  have hentry : A (0 : Fin (n + 2)).succ (Fin.last (n + 2)) =
      MvPolynomial.X M := by
    change eraseGenerator N
      (complete (D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2)))) = _
    rw [D.exterior_candidate_labels.1, complete_of_pos D.exterior_top_label_pos]
    simp [eraseGenerator, M, hMN]
  have hprivate : ∀ a b, a ≠ (0 : Fin (n + 2)).succ ∨
      b ≠ Fin.last (n + 2) → MvPolynomial.pderiv M (A a b) = 0 := by
    intro a b hab
    by_cases hcorner : a = 0 ∧ b = Fin.last (n + 2)
    · obtain ⟨rfl, rfl⟩ := hcorner
      change MvPolynomial.pderiv M (eraseGenerator N (complete D.largestLabel)) = 0
      rw [complete_of_pos D.largestLabel_pos]
      simp [eraseGenerator, N]
    · have hlt := D.topMargin_private hgap a b (by tauto) hab
      have havoid : M ∉ (D.matrix a b).vars := by
        change M ∉ (complete (D.row a - D.col b)).vars
        rw [mem_vars_complete_iff]
        change ¬ (((D.largestLabel - D.topMargin).toNat : ℕ) : ℤ) = D.row a - D.col b
        have := D.exterior_top_label_pos
        omega
      change MvPolynomial.pderiv M
        (eraseGenerator N (complete (D.row a - D.col b))) = 0
      rw [eraseGenerator_complete]
      split_ifs
      · simp
      · exact MvPolynomial.pderiv_eq_zero_of_notMem_vars havoid
  have hm : A.submatrix (0 : Fin (n + 2)).succ.succAbove
      (Fin.last (n + 2)).succAbove =
      D.matrix.submatrix (0 : Fin (n + 2)).succ.succAbove
        (Fin.last (n + 2)).succAbove := by
    apply Matrix.ext
    intro i j
    change eraseGenerator N
      (complete (D.row ((0 : Fin (n + 2)).succ.succAbove i) -
        D.col ((Fin.last (n + 2)).succAbove j))) =
      complete (D.row ((0 : Fin (n + 2)).succ.succAbove i) -
        D.col ((Fin.last (n + 2)).succAbove j))
    apply eraseGenerator_eq_self
    rw [mem_vars_complete_iff]
    change ¬ ((D.largestLabel.toNat : ℕ) : ℤ) =
      D.row ((0 : Fin (n + 2)).succ.succAbove i) -
        D.col ((Fin.last (n + 2)).succAbove j)
    have hb : (Fin.last (n + 2)).succAbove j ≠ Fin.last (n + 2) :=
      Fin.succAbove_ne _ _
    have hlt := D.index_lt_largestLabel
      ((0 : Fin (n + 2)).succ.succAbove i) ((Fin.last (n + 2)).succAbove j)
      (Or.inr hb)
    have := D.largestLabel_pos
    omega
  change MvPolynomial.pderiv M (eraseGenerator N D.matrix.det) =
    (-1) ^ (n + 3) *
      ((D.cornerDiagram hP).extendTop
        D.topMargin D.topMargin_pos).schur
  rw [eraseGenerator_det, pderiv_det_private_of_derivative_zero A M
    (0 : Fin (n + 2)).succ (Fin.last (n + 2)) hentry hprivate,
    hm, D.border_top_minor hP]
  simp only [Fin.val_succ, Fin.val_zero, Fin.val_last, schur]
  rw [show 0 + 1 + (n + 2) = n + 3 by omega]

set_option backward.isDefEq.respectTransparency false in
/-- The private exterior coefficient is nonzero because its actual diagram has nonempty rows. -/
theorem border_top_coefficient_ne_zero (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hgap : D.topMargin < D.bottomMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0 := by
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
    by have := D.exterior_top_label_pos; omega⟩
  change MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0
  have hc : MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram hP).extendTop
          D.topMargin D.topMargin_pos).schur := D.border_top_coefficient hP hgap
  rw [hc]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (((D.cornerDiagram hP).extendTop
      D.topMargin D.topMargin_pos).schur_ne_zero)

set_option backward.isDefEq.respectTransparency false in
/-- Rotation identifies the literal bottom extension with the top extension of the rotated core. -/
theorem border_rotate_corner_extension_schur (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (d : ℤ) (hd : 0 < d) :
    ((D.rotate.cornerDiagram (D.rotate_positiveCorner hP)).extendTop d hd).schur =
    ((D.cornerDiagram hP).extendBottom d hd).schur := by
  let R := (D.rotate.cornerDiagram (D.rotate_positiveCorner hP)).extendTop d hd
  let T := (D.cornerDiagram hP).extendBottom d hd
  have hm : R.rotate.matrix = T.matrix := by
    apply Matrix.ext
    intro i j
    have hj : j.rev = 0 ↔ j = Fin.last (n + 1) := by
      rw [Fin.rev_eq_iff, Fin.rev_zero]
    simp only [R, T, matrix, Matrix.of_apply, rotate, extendTop, extendBottom,
      cornerDiagram, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev]
    by_cases hz : j = Fin.last (n + 1)
    · have hrev := hj.mpr hz
      rw [ite_eq_left hrev, ite_eq_left hz]
      congr 1
      ring
    · have hrev := hj.not.mpr hz
      rw [ite_eq_right hrev, ite_eq_right hz]
      congr 1
      ring
  change R.schur = T.schur
  rw [← R.rotate_schur]
  exact congrArg Matrix.det hm

set_option backward.isDefEq.respectTransparency false in
/-- The actual private bottom coefficient follows by rotating the full board,
not a mate assumption. -/
theorem border_bottom_coefficient (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner)
    (hgap : D.bottomMargin < D.topMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat,
      by have hp := D.rotate.exterior_top_label_pos
         rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
         omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram hP).extendBottom
          D.bottomMargin D.bottomMargin_pos).schur := by
  have hr := D.rotate.border_top_coefficient (D.rotate_positiveCorner hP)
    (by simpa only [D.rotate_topMargin, D.rotate_bottomMargin] using hgap)
  dsimp only at hr ⊢
  have hl := D.rotate_largestLabel
  have hm := D.rotate_topMargin
  simpa only [hl, hm, D.rotate_schur, D.border_rotate_corner_extension_schur hP] using hr

set_option backward.isDefEq.respectTransparency false in
/-- The second private bottom coefficient cannot disappear under erasure of the largest label. -/
theorem border_bottom_coefficient_ne_zero (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hgap : D.bottomMargin < D.topMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat,
      by have hp := D.rotate.exterior_top_label_pos
         rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
         omega⟩
    MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0 := by
  have hp : 0 < D.largestLabel - D.bottomMargin := by
    have hp := D.rotate.exterior_top_label_pos
    rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
    exact hp
  let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let M : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat, by omega⟩
  change MvPolynomial.pderiv M (eraseGenerator N D.schur) ≠ 0
  have hc : MvPolynomial.pderiv M (eraseGenerator N D.schur) =
      (-1) ^ (n + 3) *
        ((D.cornerDiagram hP).extendBottom
          D.bottomMargin D.bottomMargin_pos).schur := D.border_bottom_coefficient hP hgap
  rw [hc]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (((D.cornerDiagram hP).extendBottom
      D.bottomMargin D.bottomMargin_pos).schur_ne_zero)

set_option backward.isDefEq.respectTransparency false in
/-- The true double complementary determinant is nonzero from connectedness
of the actual child alone (`eq:border-square`). -/
theorem border_tied_second_derivative_ne_zero (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected)
    (hgap : D.topMargin = D.bottomMargin) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    MvPolynomial.pderiv M (MvPolynomial.pderiv M (eraseGenerator N D.schur)) ≠ 0 := by
  dsimp only
  rw [D.exterior_tied_second_derivative hgap]
  apply mul_ne_zero (by norm_num)
  apply betaBoard_det_ne_zero
  · exact D.row_strictAnti.comp_strictMono (Fin.strictMono_succ.comp Fin.strictMono_succ)
  · exact D.col_strictAnti.comp_strictMono
      (Fin.strictMono_castSucc.comp Fin.strictMono_castSucc)
  · intro i
    exact hC.2 i.castSucc (by simp only [Fin.val_castSucc]; omega)

set_option backward.isDefEq.respectTransparency false in
/-- The second label really occurs after erasing the largest generator, including tied margins. -/
theorem border_secondLabel_mem_vars (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected) :
    let N : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
    let M : ℕ+ := ⟨D.secondLabel.toNat, by have := D.secondLabel_pos; omega⟩
    M ∈ (eraseGenerator N D.schur).vars := by
  classical
  dsimp only
  by_contra h
  have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars h
  rcases lt_trichotomy D.topMargin D.bottomMargin with ht | he | hb
  · have hn := D.border_top_coefficient_ne_zero hP ht
    dsimp only at hn
    simp only [secondLabel, min_eq_left ht.le] at hz
    exact hn hz
  · have hn := D.border_tied_second_derivative_ne_zero hP hC he
    dsimp only at hn
    simp only [secondLabel, min_eq_left (le_of_eq he)] at hz
    apply hn
    rw [hz]
    exact map_zero _
  · have hn := D.border_bottom_coefficient_ne_zero hP hb
    dsimp only at hn
    simp only [secondLabel, min_eq_right hb.le] at hz
    exact hn hz

set_option backward.isDefEq.respectTransparency false in
/-- Equality of full polynomials recovers the smaller exterior gap when the
actual complementary diagrams are connected. -/
theorem border_minMargin_eq_of_schur_eq (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hPD : D.PositiveCorner)
    (hPE : E.PositiveCorner) (hCD : (D.cornerDiagram hPD).Connected)
    (hCE : (E.cornerDiagram hPE).Connected) (he : D.schur = E.schur) :
    min D.topMargin D.bottomMargin = min E.topMargin E.bottomMargin := by
  have hl := D.largestLabel_eq_of_schur_eq E hD hE he
  have hd := D.border_secondLabel_mem_vars hPD hCD
  have hf := E.border_secondLabel_mem_vars hPE hCE
  dsimp only at hd hf
  have hv : (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) =
      ⟨E.largestLabel.toNat, by have := E.largestLabel_pos; omega⟩ := by
    apply Subtype.ext
    exact congrArg Int.toNat hl
  rw [he, hv] at hd
  rw [← he, ← hv] at hf
  have hb₁ := E.vars_le_secondLabel _ hd
  have hb₂ := D.vars_le_secondLabel _ hf
  have := D.secondLabel_pos
  have := E.secondLabel_pos
  dsimp [secondLabel] at *
  omega

/-- The top endpoint extension increases the child's span by exactly its margin. -/
theorem border_extendTop_largestLabel (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).largestLabel = D.largestLabel + t := by
  simp only [largestLabel, extendTop, ite_true]
  ring

/-- The bottom endpoint extension has the same span increase. -/
theorem border_extendBottom_largestLabel (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) :
    (D.extendBottom t ht).largestLabel = D.largestLabel + t := by
  simp only [largestLabel, extendBottom, ite_true]
  ring

/-- The top coefficient contains no generator as large as the extracted marker. -/
theorem positiveBorder_top_coefficient_labels (D : BetaDiagram (n + 2))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (h : u < v)
    (k : ℕ+) (hk : k ∈ (D.extendTop u hu).schur.vars) :
    (k.val : ℤ) < (D.positiveBorder u v hu hv).secondLabel := by
  have hb := (D.extendTop u hu).vars_le_largestLabel k hk
  rw [border_extendTop_largestLabel] at hb
  rw [positiveBorder_secondLabel, min_eq_left h.le]
  omega

/-- The bottom coefficient likewise contains no extracted marker. -/
theorem positiveBorder_bottom_coefficient_labels (D : BetaDiagram (n + 2))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (h : v < u)
    (k : ℕ+) (hk : k ∈ (D.extendBottom v hv).schur.vars) :
    (k.val : ℤ) < (D.positiveBorder u v hu hv).secondLabel := by
  have hb := (D.extendBottom v hv).vars_le_largestLabel k hk
  rw [border_extendBottom_largestLabel] at hb
  rw [positiveBorder_secondLabel, min_eq_right h.le]
  omega

/-- The genuine largest complete generator. -/
def borderLargestGenerator (D : BetaDiagram (n + 1)) : ℕ+ :=
  ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩

/-- The genuine second complete generator after deleting the corner label. -/
def borderSecondGenerator (D : BetaDiagram (n + 2)) : ℕ+ :=
  ⟨D.secondLabel.toNat, by have := D.secondLabel_pos; omega⟩

@[simp] theorem positiveBorder_cornerPolynomial (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).cornerPolynomial = D.schur := by
  rw [← cornerDiagram_schur _ (D.positiveBorder_positiveCorner u v hu hv)]
  rw [positiveBorder_cornerDiagram]

set_option backward.isDefEq.respectTransparency false in
/-- The private largest-label split for the actual lists in `eq:border-definition`. -/
theorem positiveBorder_corner_split (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    let P := D.positiveBorder u v hu hv
    P.schur = (-1) ^ (n + 1) * D.schur * MvPolynomial.X P.borderLargestGenerator +
      P.cornerResidual := by
  dsimp only
  simpa only [borderLargestGenerator, cornerCoefficient,
    positiveBorder_cornerPolynomial] using
      (D.positiveBorder u v hu hv).schur_corner_split

set_option backward.isDefEq.respectTransparency false in
/-- Differentiation extracts the whole signed core polynomial (`lem:border`). -/
theorem positiveBorder_corner_coefficient (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    let P := D.positiveBorder u v hu hv
    MvPolynomial.pderiv P.borderLargestGenerator P.schur = (-1) ^ (n + 1) * D.schur := by
  dsimp only
  have h := (D.positiveBorder u v hu hv).pderiv_schur_largest
  change MvPolynomial.pderiv (D.positiveBorder u v hu hv).borderLargestGenerator
    (D.positiveBorder u v hu hv).schur = (D.positiveBorder u v hu hv).cornerCoefficient at h
  simpa only [cornerCoefficient, positiveBorder_cornerPolynomial] using h

set_option backward.isDefEq.respectTransparency false in
/-- At unequal margins the coefficient is the actual top extension. -/
theorem positiveBorder_top_coefficient (D : BetaDiagram (n + 2))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (h : u < v) :
    let P := D.positiveBorder u v hu hv
    MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) =
      (-1) ^ (n + 3) * (D.extendTop u hu).schur := by
  let P := D.positiveBorder u v hu hv
  let hP : P.PositiveCorner := D.positiveBorder_positiveCorner u v hu hv
  have hext : (P.cornerDiagram hP).extendTop P.topMargin P.topMargin_pos =
      D.extendTop u hu := by
    simp only [P, hP, positiveBorder_cornerDiagram, positiveBorder_topMargin]
  have hp := P.border_top_coefficient hP (by simpa only [P,
    positiveBorder_topMargin, positiveBorder_bottomMargin] using h)
  dsimp only at hp ⊢
  rw [hext] at hp
  simpa only [P, borderSecondGenerator, borderLargestGenerator, secondLabel,
    positiveBorder_topMargin, positiveBorder_bottomMargin, min_eq_left h.le] using hp

/-- Setting the private corner generator to zero retains exactly the actual
Laplace residual.  Index-zero matrix entries are not removed. -/
theorem positiveBorder_erased_corner (D : BetaDiagram (n + 1))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    let P := D.positiveBorder u v hu hv
    eraseGenerator P.borderLargestGenerator P.schur = P.cornerResidual := by
  dsimp only
  rw [positiveBorder_corner_split, map_add, map_mul]
  have hr := eraseGenerator_eq_self
    (D.positiveBorder u v hu hv).borderLargestGenerator
    (D.positiveBorder u v hu hv).cornerResidual
    (D.positiveBorder u v hu hv).largest_not_mem_residual
  rw [hr]
  simp [eraseGenerator]

set_option backward.isDefEq.respectTransparency false in
/-- At the opposite unequal margins the coefficient is the actual bottom extension. -/
theorem positiveBorder_bottom_coefficient (D : BetaDiagram (n + 2))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (h : v < u) :
    let P := D.positiveBorder u v hu hv
    MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) =
      (-1) ^ (n + 3) * (D.extendBottom v hv).schur := by
  let P := D.positiveBorder u v hu hv
  let hP : P.PositiveCorner := D.positiveBorder_positiveCorner u v hu hv
  have hext : (P.cornerDiagram hP).extendBottom P.bottomMargin P.bottomMargin_pos =
      D.extendBottom v hv := by
    simp only [P, hP, positiveBorder_cornerDiagram, positiveBorder_bottomMargin]
  have hp := P.border_bottom_coefficient hP (by simpa only [P,
    positiveBorder_topMargin, positiveBorder_bottomMargin] using h)
  dsimp only at hp ⊢
  rw [hext] at hp
  simpa only [P, borderSecondGenerator, borderLargestGenerator, secondLabel,
    positiveBorder_topMargin, positiveBorder_bottomMargin, min_eq_right h.le] using hp

-- Nested complete-generator derivatives require unfolding dependent positive-index proofs.
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The tied marker has positive joint sign and the exact derivative factor two.
The displayed determinant is the child's true corner, not a proposed certificate. -/
theorem positiveBorder_tied_second_derivative (D : BetaDiagram (n + 2))
    (q : ℤ) (hq : 0 < q) :
    let P := D.positiveBorder q q hq hq
    MvPolynomial.pderiv P.borderSecondGenerator
      (MvPolynomial.pderiv P.borderSecondGenerator
        (eraseGenerator P.borderLargestGenerator P.schur)) =
      (2 : CompleteRing) * D.cornerPolynomial := by
  let P := D.positiveBorder q q hq hq
  have hp := P.exterior_tied_second_derivative (by simp [P])
  have hm : P.matrix.submatrix (fun i : Fin (n + 1) => i.succ.succ)
      (fun j : Fin (n + 1) => j.castSucc.castSucc) = D.cornerBoard := by
    ext i j
    simp [P, matrix, cornerBoard, betaBoard]
  dsimp only at hp ⊢
  rw [hm] at hp
  simpa only [P, borderSecondGenerator, borderLargestGenerator, secondLabel,
    positiveBorder_topMargin, positiveBorder_bottomMargin, min_self,
    cornerPolynomial] using hp

/-- The tied coefficient is nonzero without density or nonnegative entries. -/
theorem positiveBorder_tied_second_derivative_ne_zero (D : BetaDiagram (n + 2))
    (hC : D.Connected) (q : ℤ) (hq : 0 < q) :
    let P := D.positiveBorder q q hq hq
    MvPolynomial.pderiv P.borderSecondGenerator
      (MvPolynomial.pderiv P.borderSecondGenerator
        (eraseGenerator P.borderLargestGenerator P.schur)) ≠ 0 := by
  dsimp only
  rw [positiveBorder_tied_second_derivative]
  exact mul_ne_zero (by norm_num) (D.cornerPolynomial_ne_zero hC)

/-- All labels in the tied quadratic coefficient lie strictly below the marker. -/
theorem positiveBorder_tied_complement_labels (D : BetaDiagram (n + 2))
    (q : ℤ) (hq : 0 < q) (i j : Fin (n + 1)) :
    D.row i.succ - D.col j.castSucc <
      (D.positiveBorder q q hq hq).secondLabel := by
  have h := D.index_lt_largestLabel i.succ j.castSucc
    (Or.inl (Fin.succ_ne_zero i))
  rw [positiveBorder_secondLabel, min_self]
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The largest remaining label occurs, rather than merely bounding the entries. -/
theorem positiveBorder_secondLabel_mem_vars (D : BetaDiagram (n + 2))
    (hC : D.Connected) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    let P := D.positiveBorder u v hu hv
    P.borderSecondGenerator ∈ (eraseGenerator P.borderLargestGenerator P.schur).vars := by
  dsimp only
  exact (D.positiveBorder u v hu hv).border_secondLabel_mem_vars
    (D.positiveBorder_positiveCorner u v hu hv)
    (by simpa only [positiveBorder_cornerDiagram] using hC)

/-- Equal borders of one literal connected child have equal unordered margins. -/
theorem positiveBorder_margins_recovered (D : BetaDiagram (n + 2))
    (hC : D.Connected) (u v a b : ℤ) (hu : 0 < u) (hv : 0 < v)
    (ha : 0 < a) (hb : 0 < b)
    (he : (D.positiveBorder u v hu hv).schur = (D.positiveBorder a b ha hb).schur) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  let P := D.positiveBorder u v hu hv
  let Q := D.positiveBorder a b ha hb
  have hl := P.largestLabel_eq_of_schur_eq Q
    (D.positiveBorder_connected u v hu hv) (D.positiveBorder_connected a b ha hb) he
  have hm := P.border_minMargin_eq_of_schur_eq Q
    (D.positiveBorder_connected u v hu hv) (D.positiveBorder_connected a b ha hb)
    (D.positiveBorder_positiveCorner u v hu hv) (D.positiveBorder_positiveCorner a b ha hb)
    (by simpa only [P, positiveBorder_cornerDiagram] using hC)
    (by simpa only [Q, positiveBorder_cornerDiagram] using hC) he
  simp only [P, Q, positiveBorder_largestLabel] at hl
  simp only [P, Q, positiveBorder_topMargin, positiveBorder_bottomMargin] at hm
  rcases le_total u v with huv | hvu <;> rcases le_total a b with hab | hba
  · rw [min_eq_left huv, min_eq_left hab] at hm
    exact Or.inl ⟨hm, by omega⟩
  · rw [min_eq_left huv, min_eq_right hba] at hm
    exact Or.inr ⟨hm, by omega⟩
  · rw [min_eq_right hvu, min_eq_left hab] at hm
    exact Or.inr ⟨by omega, hm⟩
  · rw [min_eq_right hvu, min_eq_right hba] at hm
    exact Or.inl ⟨by omega, hm⟩

set_option backward.isDefEq.respectTransparency false in
/-- A strict margin swap forces equality of opposite endpoint functions. -/
theorem positiveBorder_swap_endpoint_equality (D : BetaDiagram (n + 2))
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (h : u < v)
    (he : (D.positiveBorder u v hu hv).schur = (D.positiveBorder v u hv hu).schur) :
    (D.extendTop u hu).schur = (D.extendBottom u hu).schur := by
  let P := D.positiveBorder u v hu hv
  let Q := D.positiveBorder v u hv hu
  have hN : P.borderLargestGenerator = Q.borderLargestGenerator := by
    apply Subtype.ext
    change P.largestLabel.toNat = Q.largestLabel.toNat
    congr 1
    simp [P, Q]
    ring
  have hM : P.borderSecondGenerator = Q.borderSecondGenerator := by
    apply Subtype.ext
    change P.secondLabel.toNat = Q.secondLabel.toNat
    congr 1
    simp [P, Q, min_comm]
    ring
  have hc := congrArg (fun f => MvPolynomial.pderiv P.borderSecondGenerator
    (eraseGenerator P.borderLargestGenerator f)) he
  rw [hN, hM] at hc
  have ht := D.positiveBorder_top_coefficient u v hu hv h
  have hb := D.positiveBorder_bottom_coefficient v u hv hu h
  dsimp only at ht hb
  change MvPolynomial.pderiv Q.borderSecondGenerator
      (eraseGenerator Q.borderLargestGenerator P.schur) =
    MvPolynomial.pderiv Q.borderSecondGenerator
      (eraseGenerator Q.borderLargestGenerator Q.schur) at hc
  rw [← hN, ← hM, ht, hN, hM, hb] at hc
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hc

/-- Literal-core border rigidity, conditional only on the manuscript's
opposite-endpoint rigidity premise (`lem:border`). -/
theorem positiveBorder_literal_core_rigidity (D : BetaDiagram (n + 2))
    (hC : D.Connected)
    (hEndpoint : ∀ (t : ℤ) (ht : 0 < t),
      (D.extendTop t ht).schur = (D.extendBottom t ht).schur → D.Symmetric)
    (u v a b : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (he : (D.positiveBorder u v hu hv).schur = (D.positiveBorder a b ha hb).schur) :
    D.positiveBorder u v hu hv = D.positiveBorder a b ha hb ∨
      (D.positiveBorder u v hu hv).RotationEquivalent (D.positiveBorder a b ha hb) := by
  rcases D.positiveBorder_margins_recovered hC u v a b hu hv ha hb he with h | h
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl rfl
  · obtain ⟨rfl, rfl⟩ := h
    by_cases huv : u = v
    · subst v
      exact Or.inl rfl
    · have hs : D.Symmetric := by
        rcases lt_or_gt_of_ne huv with hlt | hgt
        · exact hEndpoint u hu (D.positiveBorder_swap_endpoint_equality u v hu hv hlt he)
        · exact hEndpoint v hv
            (D.positiveBorder_swap_endpoint_equality v u hv hu hgt he.symm)
      exact Or.inr (D.positiveBorder_swap_rotation hs u v hu hv)

end BetaDiagram
end SkewJacobiNegative
