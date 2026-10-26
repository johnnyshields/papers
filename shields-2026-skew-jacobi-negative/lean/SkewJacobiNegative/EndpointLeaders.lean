/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.EndpointDifferences
import SkewJacobiNegative.NegativeBoards
import SkewJacobiNegative.SingletonContexts
import SkewJacobiNegative.ComponentBudget

/-!
# Fixed endpoint leaders

Polynomial-linear extraction of the full coefficient in `eq:endpoint-top`.
The decomposition retains all lower labels and proves generator absence in
both the coefficient and the remainder.
-/

namespace SkewJacobiNegative
open scoped BigOperators

/-- Every generator occurring in a polynomial lies strictly below this integer. -/
def LabelsBelow (p : CompleteRing) (k : ℤ) : Prop :=
  ∀ v ∈ p.vars, (v.val : ℤ) < k

namespace LabelsBelow
variable {p q : CompleteRing} {k : ℤ}

theorem zero (k : ℤ) : LabelsBelow 0 k := by simp [LabelsBelow]
theorem add (hp : LabelsBelow p k) (hq : LabelsBelow q k) : LabelsBelow (p + q) k := by
  intro v hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with h | h
  · exact hp v h
  · exact hq v h

theorem neg (hp : LabelsBelow p k) : LabelsBelow (-p) k := by
  simpa only [LabelsBelow, MvPolynomial.vars_neg] using hp

theorem sub (hp : LabelsBelow p k) (hq : LabelsBelow q k) : LabelsBelow (p - q) k := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem mul (hp : LabelsBelow p k) (hq : LabelsBelow q k) : LabelsBelow (p * q) k := by
  intro v hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with h | h
  · exact hp v h
  · exact hq v h

theorem sum {ι : Type*} (s : Finset ι) (f : ι → CompleteRing)
    (h : ∀ i ∈ s, LabelsBelow (f i) k) : LabelsBelow (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LabelsBelow]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem complete {a : ℤ} (h : a < k) : LabelsBelow (complete a) k := by
  intro v hv
  have he := (mem_vars_complete_iff a v).mp hv
  omega

theorem not_mem (hp : LabelsBelow p k) (v : ℕ+) (hv : (v.val : ℤ) = k) :
    v ∉ p.vars := by
  intro h
  have := hp v h
  omega
end LabelsBelow

namespace BetaDiagram
variable {n : ℕ}

/-- The geometric top level, without translation normalization. -/
def endpointKappa (D : BetaDiagram (n + 2)) : ℤ :=
  max (D.row (0 : Fin (n + 1)).succ - D.col (Fin.last (n + 1)))
    (D.row 0 - D.col (Fin.last n).castSucc)

/-- The full coefficient of the top endpoint level; ties retain both minors. -/
noncomputable def endpointCoefficient (D : BetaDiagram (n + 2)) : CompleteRing :=
  (∑ j ∈ Finset.univ.erase (Fin.last (n + 1)),
    if D.row 0 - D.col j = D.endpointKappa then D.cofactor 0 j else 0) -
  ∑ i ∈ Finset.univ.erase 0,
    if D.row i - D.col (Fin.last (n + 1)) = D.endpointKappa then
      D.cofactor i (Fin.last (n + 1)) else 0

/-- Every level below the top, still carrying its complete actual cofactor. -/
noncomputable def endpointRemainder (D : BetaDiagram (n + 2)) (t : ℤ) : CompleteRing :=
  (∑ j ∈ Finset.univ.erase (Fin.last (n + 1)),
    if D.row 0 - D.col j = D.endpointKappa then 0 else
      complete (D.row 0 - D.col j + t) * D.cofactor 0 j) -
  ∑ i ∈ Finset.univ.erase 0,
    if D.row i - D.col (Fin.last (n + 1)) = D.endpointKappa then 0 else
      complete (D.row i - D.col (Fin.last (n + 1)) + t) *
        D.cofactor i (Fin.last (n + 1))

/-- The requested max of the two offsets is the already geometric second label. -/
theorem endpointKappa_eq_secondLabel (D : BetaDiagram (n + 2)) :
    D.endpointKappa = D.secondLabel := by
  unfold endpointKappa secondLabel largestLabel topMargin bottomMargin
  omega

theorem endpointKappa_pos (D : BetaDiagram (n + 2)) : 0 < D.endpointKappa := by
  rw [endpointKappa_eq_secondLabel]
  exact D.secondLabel_pos

theorem endpointKappa_lt_largestLabel (D : BetaDiagram (n + 2)) :
    D.endpointKappa < D.largestLabel := by
  have ht := D.topMargin_pos
  have hb := D.bottomMargin_pos
  rw [endpointKappa_eq_secondLabel]
  unfold secondLabel
  omega

/-- Both families of actual cofactors have labels at most the fixed offset. -/
theorem endpoint_cofactor_labels (D : BetaDiagram (n + 2))
    (i j : Fin (n + 2)) (h : i = 0 ∨ j = Fin.last (n + 1))
    (v : ℕ+) (hv : v ∈ (D.cofactor i j).vars) :
    (v.val : ℤ) ≤ D.endpointKappa := by
  have hm := D.cofactor_vars_subset i j hv
  rcases h with rfl | rfl
  · exact le_trans (D.first_row_minor_labels j v hm) (le_max_left _ _)
  · exact le_trans (D.last_column_minor_labels i v hm) (le_max_right _ _)

/-- The coefficient itself is independent of the shift and has no moving marker. -/
theorem endpointCoefficient_labels (D : BetaDiagram (n + 2))
    (t : ℤ) (ht : 0 < t) : LabelsBelow D.endpointCoefficient (D.endpointKappa + t) := by
  apply LabelsBelow.sub <;> apply LabelsBelow.sum <;> intro i hi
  · split_ifs
    · intro v hv
      have := D.endpoint_cofactor_labels 0 i (Or.inl rfl) v hv
      omega
    · exact LabelsBelow.zero _
  · split_ifs
    · intro v hv
      have := D.endpoint_cofactor_labels i (Fin.last (n + 1)) (Or.inr rfl) v hv
      omega
    · exact LabelsBelow.zero _

/-- Every remaining level and every label inside its cofactor is below the marker. -/
theorem endpointRemainder_labels (D : BetaDiagram (n + 2))
    (t : ℤ) (ht : 0 < t) : LabelsBelow (D.endpointRemainder t) (D.endpointKappa + t) := by
  apply LabelsBelow.sub <;> apply LabelsBelow.sum <;> intro i hi
  · split_ifs with he
    · exact LabelsBelow.zero _
    · apply LabelsBelow.mul
      · apply LabelsBelow.complete
        have hh := D.index_le_secondLabel 0 i
          (Or.inr (Finset.mem_erase.mp hi).1)
        rw [← endpointKappa_eq_secondLabel] at hh
        omega
      · intro v hv
        have := D.endpoint_cofactor_labels 0 i (Or.inl rfl) v hv
        omega
  · split_ifs with he
    · exact LabelsBelow.zero _
    · apply LabelsBelow.mul
      · apply LabelsBelow.complete
        have hh := D.index_le_secondLabel i (Fin.last (n + 1))
          (Or.inl (Finset.mem_erase.mp hi).1)
        rw [← endpointKappa_eq_secondLabel] at hh
        omega
      · intro v hv
        have := D.endpoint_cofactor_labels i (Fin.last (n + 1)) (Or.inr rfl) v hv
        omega

set_option backward.isDefEq.respectTransparency false in
/-- The actual polynomial-linear split, including both terms at a tied top level. -/
theorem endpointDifference_split (D : BetaDiagram (n + 2))
    (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht = complete (D.endpointKappa + t) *
      D.endpointCoefficient + D.endpointRemainder t := by
  classical
  rw [endpointDifference_levels]
  unfold endpointCoefficient endpointRemainder
  simp only [mul_sub, Finset.mul_sum]
  have htop : (∑ j ∈ Finset.univ.erase (Fin.last (n + 1)),
      complete (D.row 0 - D.col j + t) * D.cofactor 0 j) =
      (∑ j ∈ Finset.univ.erase (Fin.last (n + 1)),
        complete (D.endpointKappa + t) *
          (if D.row 0 - D.col j = D.endpointKappa then D.cofactor 0 j else 0)) +
      (∑ j ∈ Finset.univ.erase (Fin.last (n + 1)),
        if D.row 0 - D.col j = D.endpointKappa then 0 else
          complete (D.row 0 - D.col j + t) * D.cofactor 0 j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : D.row 0 - D.col j = D.endpointKappa <;> simp [h]
  have hbottom : (∑ i ∈ Finset.univ.erase 0,
      complete (D.row i - D.col (Fin.last (n + 1)) + t) *
        D.cofactor i (Fin.last (n + 1))) =
      (∑ i ∈ Finset.univ.erase 0,
        complete (D.endpointKappa + t) *
          (if D.row i - D.col (Fin.last (n + 1)) = D.endpointKappa then
            D.cofactor i (Fin.last (n + 1)) else 0)) +
      (∑ i ∈ Finset.univ.erase 0,
        if D.row i - D.col (Fin.last (n + 1)) = D.endpointKappa then 0 else
          complete (D.row i - D.col (Fin.last (n + 1)) + t) *
            D.cofactor i (Fin.last (n + 1))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : D.row i - D.col (Fin.last (n + 1)) = D.endpointKappa <;> simp [h]
  rw [htop, hbottom]
  ring

/-- The manuscript's endpoint-leading property as a true coefficient statement. -/
def EndpointLeader (D : BetaDiagram (n + 1)) : Prop :=
  ∃ κ : ℤ, 0 < κ ∧ κ < D.largestLabel ∧
    ∃ c : CompleteRing, c ≠ 0 ∧ ∀ (t : ℤ) (ht : 0 < t),
      ∃ r : CompleteRing, D.endpointDifference t ht = complete (κ + t) * c + r ∧
        LabelsBelow c (κ + t) ∧ LabelsBelow r (κ + t)

/-- Generic extraction: this implication alone does not assert coefficient nonvanishing. -/
theorem endpointLeader_of_endpointCoefficient_ne_zero (D : BetaDiagram (n + 2))
    (h : D.endpointCoefficient ≠ 0) : D.EndpointLeader :=
  ⟨D.endpointKappa, D.endpointKappa_pos, D.endpointKappa_lt_largestLabel,
    D.endpointCoefficient, h, fun t ht =>
      ⟨D.endpointRemainder t, D.endpointDifference_split t ht,
        D.endpointCoefficient_labels t ht, D.endpointRemainder_labels t ht⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Differentiation extracts the entire fixed coefficient, not a scalar monomial coefficient. -/
theorem endpointLeader_pderiv (D : BetaDiagram (n + 1)) (h : D.EndpointLeader) :
    ∃ (κ : ℤ) (hκ : 0 < κ), κ < D.largestLabel ∧ ∃ c : CompleteRing, c ≠ 0 ∧
      ∀ (t : ℤ) (ht : 0 < t),
        MvPolynomial.pderiv (⟨(κ + t).toNat, by omega⟩ : ℕ+)
          (D.endpointDifference t ht) = c := by
  obtain ⟨κ, hκ, hlt, c, hc, hs⟩ := h
  refine ⟨κ, hκ, hlt, c, hc, ?_⟩
  intro t ht
  obtain ⟨r, he, hcl, hrl⟩ := hs t ht
  let v : ℕ+ := ⟨(κ + t).toNat, by omega⟩
  have hv : (v.val : ℤ) = κ + t := by dsimp [v]; omega
  have hcn := hcl.not_mem v hv
  have hrn := hrl.not_mem v hv
  change MvPolynomial.pderiv v (D.endpointDifference t ht) = c
  have hg : complete (κ + t) = (MvPolynomial.X v : CompleteRing) :=
    complete_of_pos (by omega)
  rw [he, hg, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_eq_zero_of_notMem_vars hcn,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars hrn]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Only the penultimate column and second row can contribute to the top level. -/
theorem endpointCoefficient_eq_sites (D : BetaDiagram (n + 2)) :
    D.endpointCoefficient =
      (if D.row 0 - D.col (Fin.last n).castSucc = D.endpointKappa then
        D.cofactor 0 (Fin.last n).castSucc else 0) -
      (if D.row (0 : Fin (n + 1)).succ - D.col (Fin.last (n + 1)) =
        D.endpointKappa then D.cofactor (0 : Fin (n + 1)).succ (Fin.last (n + 1))
        else 0) := by
  classical
  unfold endpointCoefficient
  congr 1
  · apply Finset.sum_eq_single (Fin.last n).castSucc
    · intro j hj hne
      apply if_neg
      have hjlast := (Finset.mem_erase.mp hj).1
      have hjlt : j < (Fin.last n).castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
        have := j.isLt
        have h₁ : j.val ≠ n + 1 := by
          intro h; apply hjlast; exact Fin.ext h
        have h₂ : j.val ≠ n := by
          intro h; apply hne; exact Fin.ext h
        omega
      have hh := D.col_strictAnti hjlt
      have hm : D.row 0 - D.col (Fin.last n).castSucc ≤ D.endpointKappa :=
        le_max_right _ _
      omega
    · intro h
      exact False.elim (h (by simp))
  · apply Finset.sum_eq_single (0 : Fin (n + 1)).succ
    · intro i hi hne
      apply if_neg
      have hi0 := (Finset.mem_erase.mp hi).1
      have hilt : (0 : Fin (n + 1)).succ < i := by
        simp only [Fin.lt_def, Fin.val_succ, Fin.val_zero]
        have h₁ : i.val ≠ 0 := by intro h; apply hi0; exact Fin.ext h
        have h₂ : i.val ≠ 1 := by intro h; apply hne; exact Fin.ext h
        omega
      have hh := D.row_strictAnti hilt
      have hm : D.row (0 : Fin (n + 1)).succ - D.col (Fin.last (n + 1)) ≤
          D.endpointKappa := le_max_left _ _
      omega
    · intro h
      exact False.elim (h (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The top-site unsigned minor is the child's actual bottom extension. -/
theorem endpoint_top_minor (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner) :
    D.unsignedMinor 0 (Fin.last (n + 1)).castSucc =
      ((D.cornerDiagram hP).extendBottom D.bottomMargin D.bottomMargin_pos).schur := by
  unfold unsignedMinor schur
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply, matrix, Matrix.of_apply, Fin.zero_succAbove,
    extendBottom, cornerDiagram]
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    rw [Fin.succAbove_castSucc_self]
    simp only [Fin.succ_last, ite_true]
    change complete (D.row i.succ - D.col (Fin.last (n + 2))) =
      complete (D.row i.succ - (D.col (Fin.last (n + 1)).castSucc - D.bottomMargin))
    congr 1
    change D.row i.succ - D.col (Fin.last (n + 2)) =
      D.row i.succ - (D.col (Fin.last (n + 1)).castSucc -
        (D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2))))
    ring
  · have hlt : j < Fin.last (n + 1) := Fin.lt_last_iff_ne_last.mpr hj
    rw [Fin.succAbove_castSucc_of_lt _ _ hlt, if_neg hj]

/-- The bottom-site unsigned minor is the child's actual top extension. -/
theorem endpoint_bottom_minor (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner) :
    D.unsignedMinor (0 : Fin (n + 2)).succ (Fin.last (n + 2)) =
      ((D.cornerDiagram hP).extendTop D.topMargin D.topMargin_pos).schur := by
  unfold unsignedMinor schur
  rw [D.border_top_minor hP]

/-- Symmetry of the maximal child, together with the tied exterior gaps,
forces symmetry of the full actual diagram. -/
theorem symmetric_of_tied_corner (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (htie : D.topMargin = D.bottomMargin)
    (hs : (D.cornerDiagram hP).Symmetric) : D.Symmetric := by
  obtain ⟨c, hr, hc⟩ := hs
  refine ⟨c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      have h := hr (0 : Fin (n + 2))
      change D.row (0 : Fin (n + 2)).succ =
        c - D.col (0 : Fin (n + 2)).rev.castSucc at h
      rw [Fin.rev_zero] at h
      change D.row 1 = c - D.col (Fin.last (n + 1)).castSucc at h
      change D.row 0 = c - D.col (Fin.last (n + 2))
      change D.row 0 - D.row 1 =
        D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2)) at htie
      omega
    | succ i =>
      have h := hr i
      change D.row i.succ = c - D.col i.rev.castSucc at h
      simpa only [Fin.rev_succ] using h
  · intro i
    by_cases hi : i = Fin.last (n + 2)
    · subst i
      have h := hc (Fin.last (n + 1))
      change D.col (Fin.last (n + 1)).castSucc =
        c - D.row (Fin.last (n + 1)).rev.succ at h
      rw [Fin.rev_last] at h
      change D.col (Fin.last (n + 1)).castSucc = c - D.row 1 at h
      rw [Fin.rev_last]
      change D.row 0 - D.row 1 =
        D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2)) at htie
      omega
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      have h := hc j
      change D.col j.castSucc = c - D.row j.rev.succ at h
      simpa only [Fin.rev_castSucc] using h

set_option backward.isDefEq.respectTransparency false in
/-- The full sign is bridged to the same actual unsigned minor. -/
theorem cofactor_eq_signed_unsignedMinor (D : BetaDiagram (n + 1))
    (i j : Fin (n + 1)) :
    D.cofactor i j = (-1) ^ (i.val + j.val) * D.unsignedMinor i j := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The top offset wins when the row margin is the smaller margin. -/
theorem endpointKappa_eq_row_offset (D : BetaDiagram (n + 3))
    (h : D.topMargin ≤ D.bottomMargin) :
    D.endpointKappa = D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2)) := by
  rw [endpointKappa_eq_secondLabel, secondLabel, min_eq_left h]
  exact D.exterior_candidate_labels.1.symm

set_option backward.isDefEq.respectTransparency false in
/-- The column offset wins when the column margin is the smaller margin. -/
theorem endpointKappa_eq_col_offset (D : BetaDiagram (n + 3))
    (h : D.bottomMargin ≤ D.topMargin) :
    D.endpointKappa = D.row 0 - D.col (Fin.last (n + 1)).castSucc := by
  rw [endpointKappa_eq_secondLabel, secondLabel, min_eq_right h]
  exact D.exterior_candidate_labels.2.symm

set_option backward.isDefEq.respectTransparency false in
/-- With a positive maximal child, the tied coefficient is its endpoint difference,
up to the actual Laplace sign. -/
theorem endpointCoefficient_tied (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (htie : D.topMargin = D.bottomMargin) :
    D.endpointCoefficient = (-1) ^ (n + 2) *
      (D.cornerDiagram hP).endpointDifference D.topMargin D.topMargin_pos := by
  rw [D.endpointCoefficient_eq_sites]
  have he₁ : D.row 0 - D.col (Fin.last (n + 1)).castSucc = D.endpointKappa := by
    exact (D.endpointKappa_eq_col_offset htie.ge).symm
  have he₂ : D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2)) =
      D.endpointKappa := by
    exact (D.endpointKappa_eq_row_offset htie.le).symm
  rw [if_pos he₁, if_pos he₂]
  rw [D.cofactor_eq_signed_unsignedMinor, D.cofactor_eq_signed_unsignedMinor]
  simp only [Fin.val_zero, Fin.val_castSucc, Fin.val_last, Fin.val_succ, zero_add]
  rw [D.endpoint_top_minor hP, D.endpoint_bottom_minor hP]
  have hpow : (-1 : CompleteRing) ^ (1 + (n + 2)) = (-1) ^ (n + 1) := by
    rw [show 1 + (n + 2) = (n + 1) + 2 by omega, pow_add]
    norm_num
  rw [hpow]
  simp only [endpointDifference, htie, pow_succ]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Untied levels are nonzero actual extension determinants, without a sign hypothesis
on the other entries of the parent or its child. -/
theorem endpointCoefficient_ne_zero_untied (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hne : D.topMargin ≠ D.bottomMargin) :
    D.endpointCoefficient ≠ 0 := by
  rw [D.endpointCoefficient_eq_sites]
  rcases lt_or_gt_of_ne hne with h | h
  · have he₁ : D.row 0 - D.col (Fin.last (n + 1)).castSucc ≠ D.endpointKappa := by
      rw [D.endpointKappa_eq_row_offset h.le]
      change D.row 0 - D.col (Fin.last (n + 1)).castSucc ≠
        D.row 1 - D.col (Fin.last (n + 2))
      change D.row 0 - D.row 1 <
        D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2)) at h
      omega
    have he₂ : D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2)) =
        D.endpointKappa := by
      exact (D.endpointKappa_eq_row_offset h.le).symm
    rw [if_neg he₁, if_pos he₂, zero_sub]
    apply neg_ne_zero.mpr
    rw [D.cofactor_eq_signed_unsignedMinor]
    rw [D.endpoint_bottom_minor hP]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (schur_ne_zero _)
  · have he₁ : D.row 0 - D.col (Fin.last (n + 1)).castSucc = D.endpointKappa := by
      exact (D.endpointKappa_eq_col_offset h.le).symm
    have he₂ : D.row (0 : Fin (n + 2)).succ - D.col (Fin.last (n + 2)) ≠
        D.endpointKappa := by
      rw [D.endpointKappa_eq_col_offset h.le]
      change D.row 1 - D.col (Fin.last (n + 2)) ≠
        D.row 0 - D.col (Fin.last (n + 1)).castSucc
      change D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2)) <
        D.row 0 - D.row 1 at h
      omega
    rw [if_pos he₁, if_neg he₂, sub_zero]
    rw [D.cofactor_eq_signed_unsignedMinor]
    rw [D.endpoint_top_minor hP]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (schur_ne_zero _)

/-- A connected nonnegative maximal child produces the full fixed leader. -/
theorem endpointCoefficient_ne_zero_of_nonnegative_corner (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected)
    (hN : (D.cornerDiagram hP).Nonnegative) (hS : ¬ D.Symmetric) :
    D.endpointCoefficient ≠ 0 := by
  by_cases htie : D.topMargin = D.bottomMargin
  · rw [D.endpointCoefficient_tied hP htie]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    apply endpointDifference_ne_zero_nonnegative _ hC hN
    exact fun hs => hS (D.symmetric_of_tied_corner hP htie hs)
  · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- The geometric coefficient producer supplies the endpoint-leading property. -/
theorem endpointLeader_of_nonnegative_corner (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected)
    (hN : (D.cornerDiagram hP).Nonnegative) (hS : ¬ D.Symmetric) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_of_nonnegative_corner hP hC hN hS)

/-- A connected maximal child with at most three rows produces the same leader,
without adding a nonnegative-index condition. -/
theorem endpointCoefficient_ne_zero_of_small_corner (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected)
    (hn : n + 2 ≤ 3) (hS : ¬ D.Symmetric) : D.endpointCoefficient ≠ 0 := by
  by_cases htie : D.topMargin = D.bottomMargin
  · rw [D.endpointCoefficient_tied hP htie]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    apply endpointDifference_ne_zero_small_rows _ hC hn
    exact fun hs => hS (D.symmetric_of_tied_corner hP htie hs)
  · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- The small actual child supplies the endpoint-leading property. -/
theorem endpointLeader_of_small_corner (D : BetaDiagram (n + 3))
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected)
    (hn : n + 2 ≤ 3) (hS : ¬ D.Symmetric) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_of_small_corner hP hC hn hS)

/-- Dense boards of at least three rows supply all child hypotheses geometrically. -/
theorem endpointLeader_dense_ge_three (D : BetaDiagram (n + 3))
    (hD : D.Dense) (hS : ¬ D.Symmetric) : D.EndpointLeader := by
  let hP := D.positiveCorner_of_nonnegative hD.nonnegative
  exact D.endpointLeader_of_nonnegative_corner hP
    (D.cornerDiagram_connected hD.nonnegative hP (by omega))
    (D.cornerDiagram_nonnegative hD.nonnegative hP) hS

set_option backward.isDefEq.respectTransparency false in
/-- In two rows, an equal pair of endpoint offsets is literal symmetry. -/
theorem symmetric_two_of_tied_offsets (D : BetaDiagram 2)
    (h : D.row 0 - D.col 0 = D.row 1 - D.col 1) : D.Symmetric := by
  refine ⟨D.row 0 + D.col 1, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
    simp [Fin.rev] <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- Every nonsymmetric two-row diagram has the full fixed endpoint leader. -/
theorem endpointCoefficient_ne_zero_two (D : BetaDiagram 2) (hS : ¬ D.Symmetric) :
    D.endpointCoefficient ≠ 0 := by
  have hne : D.row 0 - D.col 0 ≠ D.row 1 - D.col 1 :=
    fun h => hS (D.symmetric_two_of_tied_offsets h)
  rw [D.endpointCoefficient_eq_sites]
  have hm₀ : D.cofactor 0 0 = complete (D.row 1 - D.col 1) := by
    simp [cofactor, matrix, Matrix.det_unique]
  have hm₁ : D.cofactor 1 1 = complete (D.row 0 - D.col 0) := by
    simp [cofactor, matrix, Matrix.det_unique]
  change (if D.row 0 - D.col 0 = D.endpointKappa then D.cofactor 0 0 else 0) -
    (if D.row 1 - D.col 1 = D.endpointKappa then D.cofactor 1 1 else 0) ≠ 0
  rw [hm₀, hm₁]
  rcases lt_or_gt_of_ne hne with h | h
  · have he₀ : D.row 0 - D.col 0 ≠ D.endpointKappa := by
      dsimp [endpointKappa]; omega
    have he₁ : D.row 1 - D.col 1 = D.endpointKappa := by
      dsimp [endpointKappa]; omega
    rw [if_neg he₀, if_pos he₁, zero_sub]
    exact neg_ne_zero.mpr ((complete_ne_zero_iff _).mpr (by have := D.row_nonempty 0; omega))
  · have he₀ : D.row 0 - D.col 0 = D.endpointKappa := by
      dsimp [endpointKappa]; omega
    have he₁ : D.row 1 - D.col 1 ≠ D.endpointKappa := by
      dsimp [endpointKappa]; omega
    rw [if_pos he₀, if_neg he₁, sub_zero]
    exact (complete_ne_zero_iff _).mpr (by have := D.row_nonempty 1; omega)

/-- The geometric two-row coefficient supplies the endpoint-leading property. -/
theorem endpointLeader_two (D : BetaDiagram 2) (hS : ¬ D.Symmetric) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero (D.endpointCoefficient_ne_zero_two hS)

/-- `lem:endpoint-top`, for every dense order at least two. -/
theorem endpointLeader_dense (D : BetaDiagram (n + 2))
    (hD : D.Dense) (hS : ¬ D.Symmetric) : D.EndpointLeader := by
  cases n with
  | zero => exact D.endpointLeader_two hS
  | succ n => exact D.endpointLeader_dense_ge_three hD hS

/-- At most one negative site forces every other site to be nonnegative.
The southwest site is derived, not assumed as a board-pattern certificate. -/
theorem nonnegative_off_southwest_of_one_negative (D : BetaDiagram (n + 1))
    (hN : negativeCount D ≤ 1) (i j : Fin (n + 1))
    (h : i ≠ Fin.last n ∨ j ≠ 0) : D.col j ≤ D.row i := by
  classical
  by_contra hn
  have hneg : D.row i < D.col j := by omega
  have hr := D.row_strictAnti.antitone (Fin.le_last i)
  have hc := D.col_strictAnti.antitone (Fin.zero_le j)
  have hsw : D.row (Fin.last n) < D.col 0 := by omega
  have hne : (i, j) ≠ (Fin.last n, (0 : Fin (n + 1))) := by
    intro he
    have hi := congrArg Prod.fst he
    have hj := congrArg Prod.snd he
    rcases h with h | h
    · exact h hi
    · exact h hj
  have hsubset : {(i, j), (Fin.last n, (0 : Fin (n + 1)))} ⊆ negativeSites D := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [negativeSites, hneg, hsw]
  have hh := Finset.card_le_card hsubset
  have hcard : ({(i, j), (Fin.last n, (0 : Fin (n + 1)))} :
      Finset (Fin (n + 1) × Fin (n + 1))).card = 2 := by simp [hne]
  rw [hcard] at hh
  change (negativeSites D).card ≤ 1 at hN
  omega


/-- In at least four rows, a one-negative board has a genuinely connected maximal child. -/
theorem corner_connected_of_one_negative (D : BetaDiagram (n + 4))
    (hN : negativeCount D ≤ 1) (hP : D.PositiveCorner) :
    (D.cornerDiagram hP).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  apply D.nonnegative_off_southwest_of_one_negative hN
  have h₁ : (⟨i.val + 1, hi⟩ : Fin (n + 3)).succ ≠ Fin.last (n + 3) ∨
      i.castSucc ≠ (0 : Fin (n + 4)) := by
    by_cases hz : i.val = 0
    · left
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv
      omega
    · right
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_zero] at hv
      exact hz hv
  exact h₁

/-- `lem:endpoint-top`, one-negative four-row core, with every child premise produced. -/
theorem endpointLeader_one_negative_four (D : BetaDiagram 4)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1)
    (hS : ¬ D.Symmetric) : D.EndpointLeader := by
  let hP := D.positiveCorner_of_connected_zeroFree hC hZ
  exact D.endpointLeader_of_small_corner hP
    (D.corner_connected_of_one_negative hN.le hP) (by omega) hS

private theorem pderiv_complete_at (a : ℤ) (ha : 0 < a) :
    MvPolynomial.pderiv (⟨a.toNat, by omega⟩ : ℕ+) (complete a) = 1 := by
  let v : ℕ+ := ⟨a.toNat, by omega⟩
  change MvPolynomial.pderiv v (complete a) = 1
  have hg : complete a = (MvPolynomial.X v : CompleteRing) := complete_of_pos ha
  rw [hg]
  exact MvPolynomial.pderiv_X_self (R := ℚ) v

private theorem pderiv_complete_other (a b : ℤ) (hb : 0 < b) (hne : a ≠ b) :
    MvPolynomial.pderiv (⟨b.toNat, by omega⟩ : ℕ+) (complete a) = 0 := by
  let v : ℕ+ := ⟨b.toNat, by omega⟩
  change MvPolynomial.pderiv v (complete a) = 0
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  rw [mem_vars_complete_iff]
  have h : (v.val : ℤ) = b := by dsimp [v]; omega
  rw [h]
  exact Ne.symm hne

set_option backward.isDefEq.respectTransparency false in
/-- The explicit one-negative three-row tied binomial vanishes exactly at symmetry. -/
theorem endpoint_binomial_eq_zero_iff (α π ρ : ℤ)
    (hα : 0 < α) (hπ : 0 < π) (hρ : 0 < ρ) :
    complete ρ * complete (α + π) - complete (ρ + α) * complete π = 0 ↔ ρ = π := by
  constructor
  · intro hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hb : 0 < α + π := by omega
      have hd := congrArg
        (MvPolynomial.pderiv (⟨(α + π).toNat, by omega⟩ : ℕ+)) hz
      rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
        pderiv_complete_at _ hb,
        pderiv_complete_other ρ (α + π) hb (by omega),
        pderiv_complete_other (ρ + α) (α + π) hb (by omega),
        pderiv_complete_other π (α + π) hb (by omega), map_zero] at hd
      have hcz : complete ρ = 0 := by simpa using hd
      exact ((complete_ne_zero_iff ρ).mpr hρ.le) hcz
    · have hb : 0 < ρ + α := by omega
      have hd := congrArg
        (MvPolynomial.pderiv (⟨(ρ + α).toNat, by omega⟩ : ℕ+)) hz
      rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
        pderiv_complete_at _ hb,
        pderiv_complete_other ρ (ρ + α) hb (by omega),
        pderiv_complete_other (α + π) (ρ + α) hb (by omega),
        pderiv_complete_other π (ρ + α) hb (by omega), map_zero] at hd
      have hcz : complete π = 0 := by simpa using hd
      exact ((complete_ne_zero_iff π).mpr hπ.le) hcz
  · intro h
    rw [h, add_comm α π]
    ring

/-- A unique negative exists precisely at the southwest site. -/
theorem southwest_negative_of_one_negative (D : BetaDiagram (n + 1))
    (hN : negativeCount D = 1) : D.row (Fin.last n) < D.col 0 := by
  classical
  by_contra hn
  have hsw : D.col 0 ≤ D.row (Fin.last n) := by omega
  have hnon : D.Nonnegative := by
    intro i j
    have hr := D.row_strictAnti.antitone (Fin.le_last i)
    have hc := D.col_strictAnti.antitone (Fin.zero_le j)
    omega
  have he : negativeSites D = ∅ := by
    ext p
    simp only [negativeSites, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    exact not_lt.mpr (hnon p.1 p.2)
  have hz : negativeCount D = 0 := by simp [negativeCount, he]
  omega

/-- The strict chain is a consequence of the board and zero-free connectedness. -/
theorem one_negative_three_chain (D : BetaDiagram 3)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1) :
    D.col 2 < D.col 1 ∧ D.col 1 < D.row 2 ∧ D.row 2 < D.col 0 ∧
      D.col 0 < D.row 1 ∧ D.row 1 < D.row 0 := by
  have hp := D.positiveCorner_of_connected_zeroFree hC hZ
  exact ⟨D.col_strictAnti (by decide), hp 1,
    D.southwest_negative_of_one_negative hN, hp 0, D.row_strictAnti (by decide)⟩

set_option backward.isDefEq.respectTransparency false in
/-- In three rows the tied coefficient is the actual two-term binomial,
with the unique negative entry removed by its defining algebraic convention. -/
theorem endpointCoefficient_one_negative_three_tied (D : BetaDiagram 3)
    (hneg : D.row 2 < D.col 0) (htie : D.topMargin = D.bottomMargin) :
    D.endpointCoefficient =
      -(complete (D.row 1 - D.col 0) * complete (D.row 2 - D.col 2) -
        complete (D.row 1 - D.col 0 + (D.col 1 - D.col 2)) *
          complete (D.row 2 - D.col 1)) := by
  rw [D.endpointCoefficient_eq_sites]
  have he₁ : D.row 0 - D.col 1 = D.endpointKappa := by
    dsimp [endpointKappa, topMargin, bottomMargin] at *
    omega
  have he₂ : D.row 1 - D.col 2 = D.endpointKappa := by
    dsimp [endpointKappa, topMargin, bottomMargin] at *
    omega
  have hrow : D.row 0 - D.col 0 =
      D.row 1 - D.col 0 + (D.col 1 - D.col 2) := by
    dsimp [topMargin, bottomMargin] at htie
    omega
  change (if D.row 0 - D.col 1 = D.endpointKappa then D.cofactor 0 1 else 0) -
    (if D.row 1 - D.col 2 = D.endpointKappa then D.cofactor 1 2 else 0) = _
  rw [if_pos he₁, if_pos he₂]
  have hz : complete (D.row 2 - D.col 0) = 0 := complete_of_neg (by omega)
  simp only [cofactor, Matrix.det_fin_two, Matrix.submatrix_apply,
    matrix, Matrix.of_apply]
  simp [Fin.succAbove, hz, hrow] <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- At the tied top level, equality of the remaining gaps is literal symmetry. -/
theorem symmetric_one_negative_three_of_gaps (D : BetaDiagram 3)
    (htie : D.topMargin = D.bottomMargin)
    (hgap : D.row 1 - D.col 0 = D.row 2 - D.col 1) : D.Symmetric := by
  have ht : D.row 0 - D.row 1 = D.col 1 - D.col 2 := by
    simpa [topMargin, bottomMargin] using htie
  refine ⟨D.row 0 + D.col 2, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
    simp [Fin.rev] <;> omega

/-- `lem:endpoint-top`, one-negative three-row core, including the binomial tie. -/
theorem endpointCoefficient_ne_zero_one_negative_three (D : BetaDiagram 3)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1)
    (hS : ¬ D.Symmetric) : D.endpointCoefficient ≠ 0 := by
  by_cases htie : D.topMargin = D.bottomMargin
  · obtain ⟨hα, hπ, hneg, hρ, hγ⟩ := D.one_negative_three_chain hC hZ hN
    rw [D.endpointCoefficient_one_negative_three_tied hneg htie]
    apply neg_ne_zero.mpr
    have he : D.row 2 - D.col 2 = (D.col 1 - D.col 2) + (D.row 2 - D.col 1) := by ring
    rw [he]
    intro hz
    have hgap := (endpoint_binomial_eq_zero_iff
      (D.col 1 - D.col 2) (D.row 2 - D.col 1) (D.row 1 - D.col 0)
      (by omega) (by omega) (by omega)).mp hz
    exact hS (D.symmetric_one_negative_three_of_gaps htie hgap)
  · exact D.endpointCoefficient_ne_zero_untied
      (D.positiveCorner_of_connected_zeroFree hC hZ) htie

/-- The explicit three-row binomial supplies the endpoint-leading property. -/
theorem endpointLeader_one_negative_three (D : BetaDiagram 3)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1)
    (hS : ¬ D.Symmetric) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_one_negative_three hC hZ hN hS)

set_option backward.isDefEq.respectTransparency false in
/-- The fixed coefficient is nonzero at every shift, and its marker is the actual
maximum occurring generator index. -/
theorem endpointLeader_maxLabel (D : BetaDiagram (n + 1)) (h : D.EndpointLeader) :
    ∃ (κ : ℤ) (hκ : 0 < κ), κ < D.largestLabel ∧
      ∃ c : CompleteRing, c ≠ 0 ∧ ∀ (t : ℤ) (ht : 0 < t),
        MvPolynomial.pderiv (⟨(κ + t).toNat, by omega⟩ : ℕ+)
          (D.endpointDifference t ht) = c ∧
        (⟨(κ + t).toNat, by omega⟩ : ℕ+) ∈ (D.endpointDifference t ht).vars ∧
        ∀ v ∈ (D.endpointDifference t ht).vars, (v.val : ℤ) ≤ κ + t := by
  obtain ⟨κ, hκ, hlt, c, hc, hs⟩ := h
  refine ⟨κ, hκ, hlt, c, hc, ?_⟩
  intro t ht
  obtain ⟨r, he, hcl, hrl⟩ := hs t ht
  let marker : ℕ+ := ⟨(κ + t).toNat, by omega⟩
  have hm : (marker.val : ℤ) = κ + t := by dsimp [marker]; omega
  have hd : MvPolynomial.pderiv marker (D.endpointDifference t ht) = c := by
    rw [he, complete_of_pos (by omega), map_add, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_self,
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hcl.not_mem marker hm),
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hrl.not_mem marker hm)]
    ring
  refine ⟨hd, ?_, ?_⟩
  · by_contra hn
    exact hc (hd.symm.trans (MvPolynomial.pderiv_eq_zero_of_notMem_vars hn))
  · intro v hv
    rw [he] at hv
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with hv | hv
    · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
      · have hh := (mem_vars_complete_iff (κ + t) v).mp hv
        exact hh.le
      · exact (hcl v hv).le
    · exact (hrl v hv).le

/-- The polynomial-linear leader prevents vanishing for every positive shift. -/
theorem EndpointLeader.difference_ne_zero (D : BetaDiagram (n + 1))
    (h : D.EndpointLeader) (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  obtain ⟨κ, hκ, hlt, c, hc, hd⟩ := D.endpointLeader_pderiv h
  intro hz
  have hh := hd t ht
  let v : ℕ+ := ⟨(κ + t).toNat, by omega⟩
  have hh' : MvPolynomial.pderiv v (D.endpointDifference t ht) = c := hh
  rw [hz] at hh'
  exact hc (hh'.symm.trans (map_zero (MvPolynomial.pderiv v)))

/-- Removing the top row and last column preserves the unique negative site. -/
theorem corner_one_negative (D : BetaDiagram (n + 3))
    (hN : negativeCount D = 1) (hP : D.PositiveCorner) :
    negativeCount (D.cornerDiagram hP) = 1 := by
  classical
  have hsw := D.southwest_negative_of_one_negative hN
  have he : negativeSites (D.cornerDiagram hP) =
      {(Fin.last (n + 1), (0 : Fin (n + 2)))} := by
    ext p
    simp only [negativeSites, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hp
      by_contra hne
      have hoff : p.1.succ ≠ Fin.last (n + 2) ∨
          p.2.castSucc ≠ (0 : Fin (n + 3)) := by
        by_cases hi : p.1 = Fin.last (n + 1)
        · right
          intro hj
          have hz : p.2 = 0 := by
            apply Fin.ext
            have hv := congrArg Fin.val hj
            simpa only [Fin.val_castSucc, Fin.val_zero] using hv
          exact hne (Prod.ext hi hz)
        · left
          intro hj
          apply hi
          have hj' : p.1.succ = (Fin.last (n + 1)).succ := by
            simpa only [Fin.succ_last] using hj
          exact Fin.succ_inj.mp hj'
      have hh := D.nonnegative_off_southwest_of_one_negative hN.le
        p.1.succ p.2.castSucc hoff
      change D.row p.1.succ < D.col p.2.castSucc at hp
      omega
    · rintro rfl
      simpa only [cornerDiagram, Fin.succ_last, Fin.castSucc_zero] using hsw
  simp only [negativeCount, he, Finset.card_singleton]

/-- `lem:one-negative-endpoint`: all one-negative orders, using the actual child
and the explicit three-row base, with no assumed cofactor nonvanishing. -/
theorem endpointCoefficient_ne_zero_one_negative (D : BetaDiagram (n + 3))
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1)
    (hS : ¬ D.Symmetric) : D.endpointCoefficient ≠ 0 := by
  induction n with
  | zero => exact D.endpointCoefficient_ne_zero_one_negative_three hC hZ hN hS
  | succ n ih =>
    let hP := D.positiveCorner_of_connected_zeroFree hC hZ
    by_cases htie : D.topMargin = D.bottomMargin
    · rw [D.endpointCoefficient_tied hP htie]
      apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      have hChild : (D.cornerDiagram hP).EndpointLeader :=
        (D.cornerDiagram hP).endpointLeader_of_endpointCoefficient_ne_zero (ih _
          (D.corner_connected_of_one_negative hN.le hP)
          (fun i j => hZ i.succ j.castSucc)
          (D.corner_one_negative hN hP)
          (fun hs => hS (D.symmetric_of_tied_corner hP htie hs)))
      exact EndpointLeader.difference_ne_zero _ hChild D.topMargin D.topMargin_pos
    · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- The full one-negative induction supplies the endpoint-leading property. -/
theorem endpointLeader_one_negative (D : BetaDiagram (n + 3))
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1)
    (hS : ¬ D.Symmetric) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_one_negative hC hZ hN hS)

set_option backward.isDefEq.respectTransparency false in
/-- A connected dense two-row factor has no coordinate-variable divisor,
expressed directly as nonvanishing under generator erasure. -/
theorem dense_two_erased_ne_zero (D : BetaDiagram 2) (hD : D.Dense) (v : ℕ+) :
    eraseGenerator v D.schur ≠ 0 := by
  classical
  have hdiag : complete (D.row 0 - D.col 0) * complete (D.row 1 - D.col 1) ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff _).mpr (sub_nonneg.mpr (hD 0 0).le))
      ((complete_ne_zero_iff _).mpr (sub_nonneg.mpr (hD 1 1).le))
  have hcross : complete (D.row 0 - D.col 1) * complete (D.row 1 - D.col 0) ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff _).mpr (sub_nonneg.mpr (hD 0 1).le))
      ((complete_ne_zero_iff _).mpr (sub_nonneg.mpr (hD 1 0).le))
  have hr := D.row_strictAnti (show (0 : Fin 2) < 1 by decide)
  have hc := D.col_strictAnti (show (0 : Fin 2) < 1 by decide)
  unfold schur
  rw [Matrix.det_fin_two]
  simp only [matrix, Matrix.of_apply, map_sub, map_mul, eraseGenerator_complete]
  by_cases ha : D.row 0 - D.col 0 = (v.val : ℤ)
  · have hcn : D.row 0 - D.col 1 ≠ (v.val : ℤ) := by omega
    have hdn : D.row 1 - D.col 0 ≠ (v.val : ℤ) := by omega
    simpa [ha, hcn, hdn] using neg_ne_zero.mpr hcross
  by_cases hb : D.row 1 - D.col 1 = (v.val : ℤ)
  · have hcn : D.row 0 - D.col 1 ≠ (v.val : ℤ) := by omega
    have hdn : D.row 1 - D.col 0 ≠ (v.val : ℤ) := by omega
    simpa [hb, hcn, hdn] using neg_ne_zero.mpr hcross
  by_cases hcn : D.row 0 - D.col 1 = (v.val : ℤ)
  · simpa [ha, hb, hcn] using hdiag
  by_cases hdn : D.row 1 - D.col 0 = (v.val : ℤ)
  · simpa [ha, hb, hdn] using hdiag
  have hn := D.schur_ne_zero
  unfold schur at hn
  rw [Matrix.det_fin_two] at hn
  simpa [ha, hb, hcn, hdn, matrix] using hn

set_option backward.isDefEq.respectTransparency false in
/-- Rotation exchanges the actual top and bottom endpoint polynomials. -/
theorem rotate_extendTop_schur (D : BetaDiagram (n + 1)) (t : ℤ) (ht : 0 < t) :
    (D.rotate.extendTop t ht).schur = (D.extendBottom t ht).schur := by
  have hm : (D.rotate.extendTop t ht).rotate.matrix = (D.extendBottom t ht).matrix := by
    ext i j
    have hj : j.rev = 0 ↔ j = Fin.last n := by rw [Fin.rev_eq_iff, Fin.rev_zero]
    simp only [matrix, Matrix.of_apply, rotate, extendTop, extendBottom, Fin.rev_rev]
    by_cases h : j = Fin.last n <;> simp [h, hj] <;> congr 1 <;> ring
  exact (D.rotate.extendTop t ht).rotate_schur.symm.trans (congrArg Matrix.det hm)

set_option backward.isDefEq.respectTransparency false in
/-- The complementary rotation identity retains all fixed entries as well. -/
theorem rotate_extendBottom_schur (D : BetaDiagram (n + 1)) (t : ℤ) (ht : 0 < t) :
    (D.rotate.extendBottom t ht).schur = (D.extendTop t ht).schur := by
  have hm : (D.rotate.extendBottom t ht).rotate.matrix = (D.extendTop t ht).matrix := by
    ext i j
    have hi : i.rev = Fin.last n ↔ i = 0 := by rw [Fin.rev_eq_iff, Fin.rev_last]
    simp only [matrix, Matrix.of_apply, rotate, extendTop, extendBottom, Fin.rev_rev]
    by_cases h : i = 0 <;> simp [h, hi] <;> congr 1 <;> ring
  exact (D.rotate.extendBottom t ht).rotate_schur.symm.trans (congrArg Matrix.det hm)

/-- The full moving endpoint difference changes sign under literal half-turn. -/
theorem endpointDifference_rotate (D : BetaDiagram (n + 1)) (t : ℤ) (ht : 0 < t) :
    D.rotate.endpointDifference t ht = -D.endpointDifference t ht := by
  unfold endpointDifference
  rw [D.rotate_extendTop_schur t ht, D.rotate_extendBottom_schur t ht]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Exact endpoint binomial for a dense two-row component followed by a singleton. -/
theorem endpointDifference_two_then_singleton (D : BetaDiagram 3)
    (hcut : D.row 2 < D.col 1) (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht =
      complete (D.row 2 - D.col 2) * (D.init.extendTop t ht).schur -
        complete (D.row 2 - D.col 2 + t) * D.init.schur := by
  have hc := D.col_strictAnti (show (0 : Fin 3) < 1 by decide)
  have hz₀ : complete (D.row 2 - D.col 0) = 0 := complete_of_neg (by omega)
  have hz₁ : complete (D.row 2 - D.col 1) = 0 := complete_of_neg (by omega)
  have he : D.row 2 - (D.col 2 - t) = D.row 2 - D.col 2 + t := by ring
  unfold endpointDifference schur
  rw [Matrix.det_fin_three, Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [matrix, init, extendTop, extendBottom, hz₀, hz₁, he] <;> ring

/-- The singleton/dense-two-row binomial is nonzero by actual coordinate erasure. -/
theorem endpointDifference_ne_zero_two_then_singleton (D : BetaDiagram 3)
    (hcut : D.row 2 < D.col 1) (hdense : D.col 0 < D.row 1)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  have hs : 0 < D.row 2 - D.col 2 := sub_pos.mpr (D.row_nonempty 2)
  let v : ℕ+ := ⟨(D.row 2 - D.col 2).toNat, by omega⟩
  have hv : (v.val : ℤ) = D.row 2 - D.col 2 := by dsimp [v]; omega
  have hT : D.init.Dense := by
    intro i j
    have hr := D.row_strictAnti.antitone
      (show i.castSucc ≤ (1 : Fin 3) by
        change i.val ≤ 1
        exact Nat.le_of_lt_succ i.isLt)
    have hc := D.col_strictAnti.antitone (Fin.zero_le j.castSucc)
    change D.col j.castSucc < D.row i.castSucc
    omega
  intro hz
  rw [D.endpointDifference_two_then_singleton hcut t ht] at hz
  have hh := congrArg (eraseGenerator v) hz
  rw [map_sub, map_mul, map_mul, eraseGenerator_complete, eraseGenerator_complete,
    if_pos hv.symm,
    if_neg (show D.row 2 - D.col 2 + t ≠ (v.val : ℤ) by omega), map_zero] at hh
  have hp : complete (D.row 2 - D.col 2 + t) * eraseGenerator v D.init.schur ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega))
      (D.init.dense_two_erased_ne_zero hT v)
  exact (neg_ne_zero.mpr hp) (by simpa using hh)

/-- Exactly two negatives in three rows force one of the two literal cut placements. -/
theorem two_negative_three_cuts (D : BetaDiagram 3)
    (hZ : D.ZeroFree) (hN : negativeCount D = 2) :
    (D.row 2 < D.col 1 ∧ D.col 0 < D.row 1) ∨
      (D.row 1 < D.col 0 ∧ D.col 1 < D.row 2) := by
  classical
  have hr := D.row_strictAnti (show (1 : Fin 3) < 2 by decide)
  have hc := D.col_strictAnti (show (0 : Fin 3) < 1 by decide)
  have hnoboth : ¬ (D.row 2 < D.col 1 ∧ D.row 1 < D.col 0) := by
    rintro ⟨h₂, h₁⟩
    have hsw : D.row 2 < D.col 0 := by omega
    have hsubset : {((1 : Fin 3), (0 : Fin 3)), (2, 0), (2, 1)} ⊆ negativeSites D := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> simp [negativeSites, h₁, h₂, hsw]
    have hh := Finset.card_le_card hsubset
    have hn : negativeCount D ≥ 3 := by
      simpa [negativeCount] using hh
    omega
  have hsome : D.row 2 < D.col 1 ∨ D.row 1 < D.col 0 := by
    by_contra h
    have h₂ : D.col 1 ≤ D.row 2 := by omega
    have h₁ : D.col 0 ≤ D.row 1 := by omega
    have h00 := D.row_nonempty 0
    have h11 := D.row_nonempty 1
    have h22 := D.row_nonempty 2
    have hc12 := D.col_strictAnti (show (1 : Fin 3) < 2 by decide)
    have hr01 := D.row_strictAnti (show (0 : Fin 3) < 1 by decide)
    have hsubset : negativeSites D ⊆ {((2 : Fin 3), (0 : Fin 3))} := by
      rintro ⟨i, j⟩ hp
      have hneg : D.row i < D.col j := by simpa [negativeSites] using hp
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    have hh := Finset.card_le_card hsubset
    have hn : negativeCount D ≤ 1 := by simpa [negativeCount] using hh
    omega
  rcases hsome with h₂ | h₁
  · left
    refine ⟨h₂, ?_⟩
    have h := hZ 1 0
    have hn : ¬ D.row 1 < D.col 0 := fun h₁ => hnoboth ⟨h₂, h₁⟩
    omega
  · right
    refine ⟨h₁, ?_⟩
    have h := hZ 2 1
    have hn : ¬ D.row 2 < D.col 1 := fun h₂ => hnoboth ⟨h₂, h₁⟩
    omega

/-- A true three-row two-negative child has nonzero opposite endpoint functions. -/
theorem endpointDifference_ne_zero_two_negative_three (D : BetaDiagram 3)
    (hZ : D.ZeroFree) (hN : negativeCount D = 2)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  rcases D.two_negative_three_cuts hZ hN with ⟨hcut, hdense⟩ | ⟨hcut, hdense⟩
  · exact D.endpointDifference_ne_zero_two_then_singleton hcut hdense t ht
  · have hcutR : D.rotate.row 2 < D.rotate.col 1 := by
      simpa [rotate, Fin.rev] using hcut
    have hdenseR : D.rotate.col 0 < D.rotate.row 1 := by
      simpa [rotate, Fin.rev] using hdense
    have hn := D.rotate.endpointDifference_ne_zero_two_then_singleton hcutR hdenseR t ht
    rw [D.endpointDifference_rotate t ht] at hn
    exact neg_ne_zero.mp hn


/-- `lem:two-negative-endpoint`: the disconnected three-row child is treated
by its actual singleton/dense-two-row binomial, not by a rigidity certificate. -/
theorem endpointCoefficient_ne_zero_two_negative_four (D : BetaDiagram 4)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 2) :
    D.endpointCoefficient ≠ 0 := by
  let hP := D.positiveCorner_of_connected_zeroFree hC hZ
  by_cases htie : D.topMargin = D.bottomMargin
  · rw [D.endpointCoefficient_tied hP htie]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    exact endpointDifference_ne_zero_two_negative_three (D.cornerDiagram hP)
      (fun i j => hZ i.succ j.castSucc)
      ((D.corner_negativeCount hP).trans hN) D.topMargin D.topMargin_pos
  · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- The actual disconnected-child calculation supplies the endpoint-leading property. -/
theorem endpointLeader_two_negative_four (D : BetaDiagram 4)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 2) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_two_negative_four hC hZ hN)

/-- The fixed geometric coefficient is nonzero for every dense order at least two. -/
theorem endpointCoefficient_ne_zero_dense (D : BetaDiagram (n + 2))
    (hD : D.Dense) (hS : ¬ D.Symmetric) : D.endpointCoefficient ≠ 0 := by
  cases n with
  | zero => exact D.endpointCoefficient_ne_zero_two hS
  | succ n =>
    let hP := D.positiveCorner_of_nonnegative hD.nonnegative
    exact D.endpointCoefficient_ne_zero_of_nonnegative_corner hP
      (D.cornerDiagram_connected hD.nonnegative hP (by omega))
      (D.cornerDiagram_nonnegative hD.nonnegative hP) hS


/-- The exact generator at the shifted geometric top level. -/
def endpointGenerator (D : BetaDiagram (n + 2)) (t : ℤ) (ht : 0 < t) : ℕ+ :=
  ⟨(D.endpointKappa + t).toNat, by have := D.endpointKappa_pos; omega⟩

set_option backward.isDefEq.respectTransparency false in
/-- The full coefficient at the prescribed geometric maximum is independent of the shift. -/
theorem endpointDifference_pderiv (D : BetaDiagram (n + 2)) (t : ℤ) (ht : 0 < t) :
    MvPolynomial.pderiv (D.endpointGenerator t ht) (D.endpointDifference t ht) =
      D.endpointCoefficient := by
  have hκ := D.endpointKappa_pos
  have hv : ((D.endpointGenerator t ht).val : ℤ) = D.endpointKappa + t := by
    dsimp [endpointGenerator]
    omega
  have hg : complete (D.endpointKappa + t) =
      (MvPolynomial.X (D.endpointGenerator t ht) : CompleteRing) :=
    complete_of_pos (by omega)
  rw [D.endpointDifference_split t ht, hg, map_add,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      ((D.endpointCoefficient_labels t ht).not_mem (D.endpointGenerator t ht) hv),
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      ((D.endpointRemainder_labels t ht).not_mem (D.endpointGenerator t ht) hv)]
  ring

/-- `eq:endpoint-top` with the prescribed max of the actual endpoint offsets.
The displayed derivative is a true polynomial coefficient by `endpointDifference_split`. -/
def EndpointTop (D : BetaDiagram (n + 2)) : Prop :=
  0 < D.endpointKappa ∧ D.endpointKappa < D.largestLabel ∧
    D.endpointCoefficient ≠ 0 ∧ ∀ (t : ℤ) (ht : 0 < t),
      MvPolynomial.pderiv (D.endpointGenerator t ht) (D.endpointDifference t ht) =
        D.endpointCoefficient ∧
      D.endpointGenerator t ht ∈ (D.endpointDifference t ht).vars ∧
      ∀ v ∈ (D.endpointDifference t ht).vars, (v.val : ℤ) ≤ D.endpointKappa + t

/-- The generic fixed split turns actual coefficient nonvanishing into the precise
geometric maximum assertion.  Concrete clauses below discharge its sole premise. -/
theorem endpointTop_of_endpointCoefficient_ne_zero (D : BetaDiagram (n + 2))
    (hc : D.endpointCoefficient ≠ 0) : D.EndpointTop := by
  refine ⟨D.endpointKappa_pos, D.endpointKappa_lt_largestLabel, hc, ?_⟩
  intro t ht
  refine ⟨D.endpointDifference_pderiv t ht, ?_, ?_⟩
  · by_contra hn
    have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars hn
    rw [D.endpointDifference_pderiv t ht] at hz
    exact hc hz
  · intro v hv
    rw [D.endpointDifference_split t ht] at hv
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with hv | hv
    · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hv) with hv | hv
      · exact ((mem_vars_complete_iff _ v).mp hv).le
      · exact (D.endpointCoefficient_labels t ht v hv).le
    · exact (D.endpointRemainder_labels t ht v hv).le

/-- `lem:endpoint-top`: the full fixed geometric leader for every nonsymmetric dense board. -/
theorem endpoint_top_dense (D : BetaDiagram (n + 2))
    (hD : D.Dense) (hS : ¬ D.Symmetric) : D.EndpointTop :=
  D.endpointTop_of_endpointCoefficient_ne_zero (D.endpointCoefficient_ne_zero_dense hD hS)

/-- `lem:one-negative-endpoint`: the same prescribed geometric maximum at every order. -/
theorem endpoint_top_one_negative (D : BetaDiagram (n + 3))
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 1)
    (hS : ¬ D.Symmetric) : D.EndpointTop :=
  D.endpointTop_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_one_negative hC hZ hN hS)

/-- `lem:two-negative-endpoint`: all shifts and the full fixed coefficient,
including the disconnected-child tie. -/
theorem endpoint_top_two_negative_four (D : BetaDiagram 4)
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D = 2) : D.EndpointTop :=
  D.endpointTop_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_two_negative_four hC hZ hN)

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of erasing one actual independent variable is its principal ideal. -/
theorem eraseGenerator_eq_zero_implies_dvd (v : ℕ+) (p : CompleteRing)
    (hz : eraseGenerator v p = 0) : (MvPolynomial.X v : CompleteRing) ∣ p := by
  classical
  have hd : (MvPolynomial.X v : CompleteRing) ∣ p - eraseGenerator v p := by
    clear hz
    induction p using MvPolynomial.induction_on with
    | C a => simp [eraseGenerator]
    | add p q hp hq =>
      rw [map_add, show p + q - (eraseGenerator v p + eraseGenerator v q) =
        (p - eraseGenerator v p) + (q - eraseGenerator v q) by ring]
      exact dvd_add hp hq
    | mul_X p w hp =>
      rw [map_mul]
      by_cases hw : w = v
      · subst w
        have hX : eraseGenerator v (MvPolynomial.X v : CompleteRing) = 0 := by
          simp [eraseGenerator]
        rw [hX, mul_zero, sub_zero]
        exact dvd_mul_left _ _
      · have hX : eraseGenerator v (MvPolynomial.X w : CompleteRing) =
            MvPolynomial.X w := by simp [eraseGenerator, hw]
        rw [hX, show p * MvPolynomial.X w - eraseGenerator v p * MvPolynomial.X w =
          (p - eraseGenerator v p) * MvPolynomial.X w by ring]
        exact dvd_mul_of_dvd_left hp _
  simpa only [hz, sub_zero] using hd

/-- A connected factor with at least two nonempty rows has no coordinate divisor,
at any order and with arbitrary negative or zero entries. -/
theorem connected_erased_ne_zero (D : BetaDiagram (n + 2)) (hC : D.Connected)
    (v : ℕ+) : eraseGenerator v D.schur ≠ 0 := by
  intro hz
  obtain ⟨q, he⟩ := eraseGenerator_eq_zero_implies_dvd v D.schur hz
  rcases (D.schur_irreducible hC).isUnit_or_isUnit he with hX | hq
  · have hdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hX).2
    norm_num [MvPolynomial.totalDegree_X] at hdeg
  · have hqdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hq).2
    have hd := MvPolynomial.totalDegree_mul (MvPolynomial.X v : CompleteRing) q
    rw [← he, D.schur_totalDegree, MvPolynomial.totalDegree_X, hqdeg] at hd
    omega

set_option backward.isDefEq.respectTransparency false in
/-- The actual last-singleton cut has the full determinant factorization. -/
theorem schur_last_singleton (D : BetaDiagram (n + 3))
    (hcut : D.row (Fin.last (n + 2)) < D.col (Fin.last (n + 1)).castSucc) :
    D.schur = D.init.schur *
      complete (D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2))) := by
  have hc : D.row (⟨n + 2, by omega⟩ : Fin ((n + 2) + 1)) <
      D.col ⟨(n + 2) - 1, by omega⟩ := hcut
  have hf := D.schur_factor_at_cut (a := n + 2) (b := 1) (by omega) (by omega) hc
  have hp : (D.betaPrefix (a := n + 2) (b := 1)).schur = D.init.schur := rfl
  have hs : (D.suffix (a := n + 2) (b := 1)).schur =
      complete (D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2))) := by
    have hlast : (0 : Fin 1).natAdd (n + 2) = (Fin.last (n + 2) : Fin (n + 3)) := by
      apply Fin.ext
      simp
    simp [schur, matrix, suffix, Matrix.det_unique]
    rw [hlast]
  rw [hp, hs] at hf
  exact hf

set_option backward.isDefEq.respectTransparency false in
/-- A terminal singleton gives the actual two-factor endpoint binomial
for an arbitrary preceding component. -/
theorem endpointDifference_last_singleton (D : BetaDiagram (n + 3))
    (hcut : D.row (Fin.last (n + 2)) < D.col (Fin.last (n + 1)).castSucc)
    (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht =
      complete (D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2))) *
        (D.init.extendTop t ht).schur -
      complete (D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2)) + t) *
        D.init.schur := by
  have hl0 : (Fin.last (n + 2) : Fin (n + 3)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    have hn : n + 2 = 0 := by simpa only [Fin.val_last, Fin.val_zero] using hv
    omega
  have hpL : (Fin.last (n + 1)).castSucc ≠ (Fin.last (n + 2) : Fin (n + 3)) :=
    Fin.castSucc_ne_last _
  have htopcut : (D.extendTop t ht).row (Fin.last (n + 2)) <
      (D.extendTop t ht).col (Fin.last (n + 1)).castSucc := by
    simpa only [extendTop, if_neg hl0] using hcut
  have hbotcut : (D.extendBottom t ht).row (Fin.last (n + 2)) <
      (D.extendBottom t ht).col (Fin.last (n + 1)).castSucc := by
    simpa only [extendBottom, if_neg hpL] using hcut
  have htopinit : (D.extendTop t ht).init.schur = (D.init.extendTop t ht).schur := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    have hi : i.castSucc = (0 : Fin (n + 3)) ↔ i = (0 : Fin (n + 2)) := by
      constructor
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        simpa only [Fin.val_castSucc, Fin.val_zero] using hv
      · rintro rfl
        rfl
    simp only [matrix, Matrix.of_apply, init, extendTop]
    simp only [hi]
  have hbotinit : (D.extendBottom t ht).init.schur = D.init.schur := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    simp [matrix, init, extendBottom, Fin.castSucc_ne_last]
  unfold endpointDifference
  rw [(D.extendTop t ht).schur_last_singleton htopcut,
    (D.extendBottom t ht).schur_last_singleton hbotcut, htopinit, hbotinit]
  simp only [extendTop, extendBottom, if_neg hl0, ite_true]
  rw [show D.row (Fin.last (n + 2)) - (D.col (Fin.last (n + 2)) - t) =
    D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2)) + t by ring]
  ring

/-- All singleton-plus-connected-component child cases of unequal orders have
nonzero endpoint differences, without a low-negative classification premise. -/
theorem endpointDifference_ne_zero_last_singleton (D : BetaDiagram (n + 3))
    (hcut : D.row (Fin.last (n + 2)) < D.col (Fin.last (n + 1)).castSucc)
    (hC : D.init.Connected) (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht ≠ 0 := by
  have hs : 0 < D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2)) :=
    sub_pos.mpr (D.row_nonempty _)
  let v : ℕ+ := ⟨(D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2))).toNat, by omega⟩
  have hv : (v.val : ℤ) =
      D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2)) := by dsimp [v]; omega
  intro hz
  rw [D.endpointDifference_last_singleton hcut t ht] at hz
  have hh := congrArg (eraseGenerator v) hz
  rw [map_sub, map_mul, map_mul, eraseGenerator_complete, eraseGenerator_complete,
    if_pos hv.symm,
    if_neg (show D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2)) + t ≠
      (v.val : ℤ) by omega), map_zero] at hh
  have hn : complete (D.row (Fin.last (n + 2)) - D.col (Fin.last (n + 2)) + t) *
      eraseGenerator v D.init.schur ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega)) (D.init.connected_erased_ne_zero hC v)
  exact (neg_ne_zero.mpr hn) (by simpa using hh)

set_option backward.isDefEq.respectTransparency false in
/-- Rotation also proves nonvanishing for a first singleton followed by a
connected component of any larger order. -/
theorem endpointDifference_ne_zero_first_singleton (D : BetaDiagram (n + 3))
    (hcut : D.row (0 : Fin (n + 2)).succ < D.col 0)
    (hC : D.tail.Connected) (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht ≠ 0 := by
  have hcutR : D.rotate.row (Fin.last (n + 2)) <
      D.rotate.col (Fin.last (n + 1)).castSucc := by
    simpa only [rotate, Fin.rev_last, Fin.rev_castSucc, neg_lt_neg_iff] using hcut
  have hCR : D.rotate.init.Connected := by
    simpa only [Connected, init, rotate, tail, Fin.rev_castSucc] using
      D.tail.rotate_connected hC
  have hn := D.rotate.endpointDifference_ne_zero_last_singleton hcutR hCR t ht
  rw [D.endpointDifference_rotate t ht] at hn
  exact neg_ne_zero.mp hn

set_option backward.isDefEq.respectTransparency false in
/-- The exact endpoint identity at an actual two-plus-two cut. -/
theorem endpointDifference_two_two (D : BetaDiagram 4)
    (hcut : D.row 2 < D.col 1) (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht =
      ((D.betaPrefix (a := 2) (b := 2)).extendTop t ht).schur *
        (D.suffix (a := 2) (b := 2)).schur -
      (D.betaPrefix (a := 2) (b := 2)).schur *
        ((D.suffix (a := 2) (b := 2)).extendBottom t ht).schur := by
  have htc : (D.extendTop t ht).row 2 < (D.extendTop t ht).col 1 := by
    simpa only [extendTop, show (2 : Fin 4) ≠ 0 by decide, ite_false] using hcut
  have hbc : (D.extendBottom t ht).row 2 < (D.extendBottom t ht).col 1 := by
    simpa only [extendBottom, show (1 : Fin 4) ≠ Fin.last 3 by decide, ite_false] using hcut
  have hTT : ((D.extendTop t ht).betaPrefix (a := 2) (b := 2)).schur =
      ((D.betaPrefix (a := 2) (b := 2)).extendTop t ht).schur := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [matrix, betaPrefix, extendTop]
  have hTU : ((D.extendTop t ht).suffix (a := 2) (b := 2)).schur =
      (D.suffix (a := 2) (b := 2)).schur := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [matrix, suffix, extendTop]
  have hBT : ((D.extendBottom t ht).betaPrefix (a := 2) (b := 2)).schur =
      (D.betaPrefix (a := 2) (b := 2)).schur := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [matrix, betaPrefix, extendBottom]
  have hBU : ((D.extendBottom t ht).suffix (a := 2) (b := 2)).schur =
      ((D.suffix (a := 2) (b := 2)).extendBottom t ht).schur := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [matrix, suffix, extendBottom]
  unfold endpointDifference
  rw [(D.extendTop t ht).schur_factor_at_cut (a := 2) (b := 2)
      (by decide) (by decide) htc,
    (D.extendBottom t ht).schur_factor_at_cut (a := 2) (b := 2)
      (by decide) (by decide) hbc, hTT, hTU, hBT, hBU]

set_option backward.isDefEq.respectTransparency false in
/-- Reverse-partner two-row components make the actual four-row cut diagram symmetric;
the intervening beta gap is retained rather than normalized away. -/
theorem symmetric_of_two_two_rotation (D : BetaDiagram 4)
    (h : (D.betaPrefix (a := 2) (b := 2)).RotationEquivalent
      (D.suffix (a := 2) (b := 2))) : D.Symmetric := by
  obtain ⟨c, hr, hc⟩ := h
  have hr0 := hr 0
  have hr1 := hr 1
  have hc0 := hc 0
  have hc1 := hc 1
  simp only [betaPrefix, suffix, Fin.rev] at hr0 hr1 hc0 hc1
  change D.row 0 = c - D.col 3 at hr0
  change D.row 1 = c - D.col 2 at hr1
  change D.col 0 = c - D.row 3 at hc0
  change D.col 1 = c - D.row 2 at hc1
  refine ⟨c, ?_, ?_⟩ <;> intro i <;> fin_cases i <;> simp [Fin.rev] <;> omega

/-- Opposite endpoint equality at a two-plus-two cut forces reverse partners,
using irreducible actual factors and two-row rigidity against the actual mate. -/
theorem endpointDifference_two_two_eq_zero_implies_symmetric (D : BetaDiagram 4)
    (hcut : D.row 2 < D.col 1)
    (hT : (D.betaPrefix (a := 2) (b := 2)).Connected)
    (hU : (D.suffix (a := 2) (b := 2)).Connected)
    (t : ℤ) (ht : 0 < t) (hz : D.endpointDifference t ht = 0) : D.Symmetric := by
  let T := D.betaPrefix (a := 2) (b := 2)
  let U := D.suffix (a := 2) (b := 2)
  have hTC : T.Connected := hT
  have hUC : U.Connected := hU
  have hTopC := T.extendTop_connected hTC t ht
  have hBottomC := U.extendBottom_connected hUC t ht
  have hTopI := (T.extendTop t ht).schur_irreducible hTopC
  have hTI := T.schur_irreducible hTC
  have hBottomI := (U.extendBottom t ht).schur_irreducible hBottomC
  have he : (T.extendTop t ht).schur * U.schur =
      T.schur * (U.extendBottom t ht).schur :=
    sub_eq_zero.mp ((D.endpointDifference_two_two hcut t ht).symm.trans hz)
  have hd : (T.extendTop t ht).schur ∣ T.schur * (U.extendBottom t ht).schur := by
    rw [← he]
    exact dvd_mul_right _ _
  have hCross : (T.extendTop t ht).schur = (U.extendBottom t ht).schur := by
    rcases hTopI.prime.dvd_mul.mp hd with hSame | hCross
    · have hs := (T.extendTop t ht).schur_eq_of_associated T
        (hTopI.associated_of_dvd hTI hSame)
      have hl := (T.extendTop t ht).largestLabel_eq_of_schur_eq T hTopC hTC hs
      rw [border_extendTop_largestLabel] at hl
      exact False.elim (by omega)
    · exact (T.extendTop t ht).schur_eq_of_associated (U.extendBottom t ht)
        (hTopI.associated_of_dvd hBottomI hCross)
  have hTU : T.schur = U.schur := by
    rw [hCross] at he
    have hh : (U.extendBottom t ht).schur * U.schur =
        (U.extendBottom t ht).schur * T.schur := by simpa only [mul_comm] using he
    exact (mul_left_cancel₀ (U.extendBottom t ht).schur_ne_zero hh).symm
  apply D.symmetric_of_two_two_rotation
  rcases T.rigidity_two U hTC hUC hTU with htr | hrot
  · have hBot := extendBottom_schur_eq_of_translation T U htr t ht
    have hsT : T.Symmetric :=
      T.symmetric_of_extendTop_rotation_extendBottom t ht (by
        rcases (T.extendTop t ht).rigidity_two (T.extendBottom t ht)
          hTopC (T.extendBottom_connected hTC t ht) (hCross.trans hBot.symm)
          with hbad | hgood
        · exact False.elim (T.extendTop_not_translation_extendBottom t ht hbad)
        · exact hgood)
    obtain ⟨k, hsr, hsc⟩ := hsT
    obtain ⟨c, htrr, htrc⟩ := htr
    refine ⟨k - c, ?_, ?_⟩
    · intro i
      have hs := hsr i
      have hq := htrc i.rev
      change T.row i = k - T.col i.rev at hs
      change T.col i.rev = U.col i.rev + c at hq
      change T.row i = (k - c) - U.col i.rev
      omega
    · intro i
      have hs := hsc i
      have hq := htrr i.rev
      change T.col i = k - T.row i.rev at hs
      change T.row i.rev = U.row i.rev + c at hq
      change T.col i = (k - c) - U.row i.rev
      omega
  · exact hrot

/-- A last-singleton maximal child supplies the full fixed geometric parent leader,
at arbitrary orders and without a negative-budget premise. -/
theorem endpoint_top_last_singleton_corner (D : BetaDiagram (n + 4))
    (hP : D.PositiveCorner)
    (hcut : (D.cornerDiagram hP).row (Fin.last (n + 2)) <
      (D.cornerDiagram hP).col (Fin.last (n + 1)).castSucc)
    (hCore : (D.cornerDiagram hP).init.Connected) : D.EndpointTop := by
  apply D.endpointTop_of_endpointCoefficient_ne_zero
  by_cases htie : D.topMargin = D.bottomMargin
  · rw [D.endpointCoefficient_tied hP htie]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    exact (D.cornerDiagram hP).endpointDifference_ne_zero_last_singleton
      hcut hCore D.topMargin D.topMargin_pos
  · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- The first-singleton placement supplies the same complete parent conclusion. -/
theorem endpoint_top_first_singleton_corner (D : BetaDiagram (n + 4))
    (hP : D.PositiveCorner)
    (hcut : (D.cornerDiagram hP).row (0 : Fin (n + 2)).succ <
      (D.cornerDiagram hP).col 0)
    (hCore : (D.cornerDiagram hP).tail.Connected) : D.EndpointTop := by
  apply D.endpointTop_of_endpointCoefficient_ne_zero
  by_cases htie : D.topMargin = D.bottomMargin
  · rw [D.endpointCoefficient_tied hP htie]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    exact (D.cornerDiagram hP).endpointDifference_ne_zero_first_singleton
      hcut hCore D.topMargin D.topMargin_pos
  · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- The actual two-plus-two maximal child supplies the nonsymmetric five-row
parent's fixed leader; its factor comparison produces symmetry rather than assuming rigidity. -/
theorem endpoint_top_two_two_corner (D : BetaDiagram 5)
    (hP : D.PositiveCorner)
    (hcut : (D.cornerDiagram hP).row 2 < (D.cornerDiagram hP).col 1)
    (hT : ((D.cornerDiagram hP).betaPrefix (a := 2) (b := 2)).Connected)
    (hU : ((D.cornerDiagram hP).suffix (a := 2) (b := 2)).Connected)
    (hS : ¬ D.Symmetric) : D.EndpointTop := by
  apply D.endpointTop_of_endpointCoefficient_ne_zero
  by_cases htie : D.topMargin = D.bottomMargin
  · rw [D.endpointCoefficient_tied hP htie]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    intro hz
    have hs := (D.cornerDiagram hP).endpointDifference_two_two_eq_zero_implies_symmetric
      hcut hT hU D.topMargin D.topMargin_pos hz
    exact hS (D.symmetric_of_tied_corner hP htie hs)
  · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- Endpoint extensions preserve each individual overlap, not just its sorted multiset.
This is the literal word invariant needed to exclude exceptional child-orbit switches. -/
theorem opposite_endpoint_extensions_overlap (D : BetaDiagram (n + 1))
    (t : ℤ) (ht : 0 < t) (i : Fin (n + 1)) (hi : i.val + 1 < n + 1) :
    (D.extendTop t ht).overlap i hi = D.overlap i hi ∧
      (D.extendBottom t ht).overlap i hi = D.overlap i hi := by
  have hrow : (⟨i.val + 1, hi⟩ : Fin (n + 1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero] at hv
    omega
  have hcol : i ≠ Fin.last n := by
    intro h
    rw [h, Fin.val_last] at hi
    omega
  constructor
  · simp only [overlap, extendTop, if_neg hrow]
  · simp only [overlap, extendBottom, if_neg hcol]

private theorem complete_shift_sub (x y t : ℤ) :
    complete (x + t - y) = complete (x - y + t) := congrArg complete (by ring)

private theorem complete_sub_shift (x y t : ℤ) :
    complete (x - (y - t)) = complete (x - y + t) := congrArg complete (by ring)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine square-initial row product recovers equality of the endpoint row lengths
from opposite endpoint equality. -/
theorem endpoint_equality_four_endpoint_lengths (D : BetaDiagram 4)
    (t : ℤ) (ht : 0 < t) (hz : D.endpointDifference t ht = 0) :
    D.row 0 - D.col 0 = D.row 3 - D.col 3 := by
  have hp := congrArg (Base.initialForm Base.squareWeight.generatorWeight)
    (sub_eq_zero.mp hz)
  rw [square_initialForm, square_initialForm] at hp
  have hprod :
      complete (D.row 0 - D.col 0 + t) *
        (complete (D.row 1 - D.col 1) *
          (complete (D.row 2 - D.col 2) * complete (D.row 3 - D.col 3))) =
      complete (D.row 0 - D.col 0) *
        (complete (D.row 1 - D.col 1) *
          (complete (D.row 2 - D.col 2) * complete (D.row 3 - D.col 3 + t))) := by
    simpa [Fin.prod_univ_succ, extendTop, extendBottom,
      complete_shift_sub, complete_sub_shift] using hp
  have hmid : complete (D.row 1 - D.col 1) * complete (D.row 2 - D.col 2) ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff _).mpr (sub_nonneg.mpr (D.row_nonempty 1).le))
      ((complete_ne_zero_iff _).mpr (sub_nonneg.mpr (D.row_nonempty 2).le))
  have hfac : (complete (D.row 0 - D.col 0 + t) * complete (D.row 3 - D.col 3) -
      complete (D.row 0 - D.col 0) * complete (D.row 3 - D.col 3 + t)) *
        (complete (D.row 1 - D.col 1) * complete (D.row 2 - D.col 2)) = 0 := by
    calc
      _ = complete (D.row 0 - D.col 0 + t) *
          (complete (D.row 1 - D.col 1) *
            (complete (D.row 2 - D.col 2) * complete (D.row 3 - D.col 3))) -
          complete (D.row 0 - D.col 0) *
          (complete (D.row 1 - D.col 1) *
            (complete (D.row 2 - D.col 2) * complete (D.row 3 - D.col 3 + t))) := by ring
      _ = 0 := sub_eq_zero.mpr hprod
  have hbin := (mul_eq_zero.mp hfac).resolve_right hmid
  apply (endpoint_binomial_eq_zero_iff t (D.row 3 - D.col 3) (D.row 0 - D.col 0)
    ht (sub_pos.mpr (D.row_nonempty 3)) (sub_pos.mpr (D.row_nonempty 0))).mp
  rw [add_comm t (D.row 3 - D.col 3)]
  calc
    _ = -(complete (D.row 0 - D.col 0 + t) * complete (D.row 3 - D.col 3) -
      complete (D.row 0 - D.col 0) * complete (D.row 3 - D.col 3 + t)) := by ring
    _ = 0 := by rw [hbin]; simp

set_option backward.isDefEq.respectTransparency false in
/-- Tied exterior margins and palindromic rows are literal four-row symmetry. -/
theorem symmetric_four_of_balanced_rows (D : BetaDiagram 4)
    (htie : D.topMargin = D.bottomMargin)
    (hends : D.row 0 - D.col 0 = D.row 3 - D.col 3)
    (hmiddle : D.row 1 - D.col 1 = D.row 2 - D.col 2) : D.Symmetric := by
  have hm : D.row 0 - D.row 1 = D.col 2 - D.col 3 := htie
  refine ⟨D.row 0 + D.col 3, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
    simp [Fin.rev] <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- The three-row beta determinant left after balanced endpoint cancellation is
nonzero whenever the two middle row lengths differ.  Sorting its last two columns
is performed explicitly; the auxiliary board's positivity is derived. -/
theorem endpoint_auxiliary_det_ne_zero (a b c s t : ℤ)
    (hs : 0 < s) (has : s < a) (hbs : s < b) (hcs : s < c)
    (ht : 0 < t) (hne : b ≠ c) :
    (betaBoard ![a + t, a, s] ![0, s - b, s - c]).det ≠ 0 := by
  have hr : StrictAnti (![a + t, a, s] : Fin 3 → ℤ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  have hsorted : ∀ B C : ℤ, s < B → B < C →
      (betaBoard ![a + t, a, s] ![0, s - B, s - C]).det ≠ 0 := by
    intro B C hB hBC
    apply betaBoard_det_ne_zero _ _ hr
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i
      fin_cases i <;> simp <;> omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact hsorted b c hbs h
  · have he : (betaBoard ![a + t, a, s] ![0, s - b, s - c]).det =
        -(betaBoard ![a + t, a, s] ![0, s - c, s - b]).det := by
      rw [Matrix.det_fin_three, Matrix.det_fin_three]
      simp only [betaBoard, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_zero]
      ring
    rw [he]
    exact neg_ne_zero.mpr (hsorted c b hcs h)

-- The two actual four-row Laplace expansions are compared before factoring the residual.
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Exact residual determinant in the balanced three-negative four-row branch.
The factor is an actual beta board, not an asserted endpoint certificate. -/
theorem endpointDifference_balanced_hessenberg_four (D : BetaDiagram 4)
    (h20 : D.row 2 < D.col 0) (h30 : D.row 3 < D.col 0)
    (h31 : D.row 3 < D.col 1)
    (htie : D.topMargin = D.bottomMargin)
    (hends : D.row 0 - D.col 0 = D.row 3 - D.col 3)
    (t : ℤ) (ht : 0 < t) :
    D.endpointDifference t ht =
      complete (D.row 1 - D.col 0) *
        (betaBoard
          ![D.row 0 - D.col 0 + t, D.row 0 - D.col 0, D.row 1 - D.col 0]
          ![0, (D.row 1 - D.col 0) - (D.row 1 - D.col 1),
            (D.row 1 - D.col 0) - (D.row 2 - D.col 2)]).det := by
  have hm : D.row 0 - D.row 1 = D.col 2 - D.col 3 := htie
  have hz20 := complete_of_neg (show D.row 2 - D.col 0 < 0 by omega)
  have hz30 := complete_of_neg (show D.row 3 - D.col 0 < 0 by omega)
  have hz31 := complete_of_neg (show D.row 3 - D.col 1 < 0 by omega)
  have hend0 : complete (D.row 3 - D.col 3) = complete (D.row 0 - D.col 0) :=
    congrArg complete hends.symm
  have hendt : complete (D.row 3 - D.col 3 + t) = complete (D.row 0 - D.col 0 + t) :=
    congrArg complete (by omega)
  have hover : complete (D.row 3 - D.col 2) = complete (D.row 1 - D.col 0) :=
    congrArg complete (by omega)
  have hcross : complete (D.row 1 - D.col 3) = complete (D.row 0 - D.col 2) :=
    congrArg complete (by omega)
  have hcrosst : complete (D.row 1 - D.col 3 + t) = complete (D.row 0 - D.col 2 + t) :=
    congrArg complete (by omega)
  let K : Matrix (Fin 3) (Fin 3) CompleteRing :=
    ![![complete (D.row 0 - D.col 0 + t), complete (D.row 0 - D.col 1 + t),
        complete (D.row 2 - D.col 3 + t)],
      ![complete (D.row 0 - D.col 0), complete (D.row 0 - D.col 1),
        complete (D.row 2 - D.col 3)],
      ![complete (D.row 1 - D.col 0), complete (D.row 1 - D.col 1),
        complete (D.row 2 - D.col 2)]]
  have hK : K = betaBoard
      ![D.row 0 - D.col 0 + t, D.row 0 - D.col 0, D.row 1 - D.col 0]
      ![0, (D.row 1 - D.col 0) - (D.row 1 - D.col 1),
        (D.row 1 - D.col 0) - (D.row 2 - D.col 2)] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [K, betaBoard, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.tail_cons]
    all_goals apply congrArg complete
    all_goals omega
  rw [← hK]
  unfold endpointDifference schur
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero, Matrix.det_fin_three]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    matrix, extendTop, extendBottom, Fin.succAbove, K,
    complete_shift_sub, complete_sub_shift,
    hz20, hz30, hz31, hend0, hendt, hover, hcross, hcrosst] <;> ring

/-- The connected three-negative four-row branch has no nonsymmetric endpoint equality.
This uses a sorted three-row beta determinant instead of a four-row classification assumption. -/
theorem endpointDifference_ne_zero_hessenberg_four (D : BetaDiagram 4)
    (hC : D.Connected) (hZ : D.ZeroFree)
    (h20 : D.row 2 < D.col 0) (h30 : D.row 3 < D.col 0)
    (h31 : D.row 3 < D.col 1) (hS : ¬ D.Symmetric)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  intro hz
  let hP := D.positiveCorner_of_connected_zeroFree hC hZ
  have htie : D.topMargin = D.bottomMargin := by
    by_contra hne
    have hc := D.endpointCoefficient_ne_zero_untied hP hne
    have hd := D.endpointDifference_pderiv t ht
    rw [hz, map_zero] at hd
    exact hc hd.symm
  have hends := D.endpoint_equality_four_endpoint_lengths t ht hz
  have hmiddle : D.row 1 - D.col 1 ≠ D.row 2 - D.col 2 :=
    fun he => hS (D.symmetric_four_of_balanced_rows htie hends he)
  have hs : 0 < D.row 1 - D.col 0 := by
    have hh := hP 0
    change D.col 0 < D.row 1 at hh
    exact sub_pos.mpr hh
  have has : D.row 1 - D.col 0 < D.row 0 - D.col 0 := by
    have hh := D.row_strictAnti (show (0 : Fin 4) < 1 by decide)
    omega
  have hbs : D.row 1 - D.col 0 < D.row 1 - D.col 1 := by
    have hh := D.col_strictAnti (show (0 : Fin 4) < 1 by decide)
    omega
  have hcs : D.row 1 - D.col 0 < D.row 2 - D.col 2 := by
    have hh := D.row_strictAnti (show (2 : Fin 4) < 3 by decide)
    have hm : D.row 0 - D.row 1 = D.col 2 - D.col 3 := htie
    omega
  rw [D.endpointDifference_balanced_hessenberg_four h20 h30 h31 htie hends t ht] at hz
  exact mul_ne_zero ((complete_ne_zero_iff _).mpr hs.le)
    (endpoint_auxiliary_det_ne_zero
      (D.row 0 - D.col 0) (D.row 1 - D.col 1) (D.row 2 - D.col 2)
      (D.row 1 - D.col 0) t hs has hbs hcs ht hmiddle) hz

/-- Connectedness excludes all negative sites except the three lower-left
sites separated from the diagonal by at least two steps. -/
theorem connected_four_negative_sites_subset (D : BetaDiagram 4) (hC : D.Connected) :
    negativeSites D ⊆ {((2 : Fin 4), (0 : Fin 4)), (3, 0), (3, 1)} := by
  classical
  have ha0 : D.col 0 ≤ D.row 1 := hC.2 0 (by decide)
  have ha1 : D.col 1 ≤ D.row 2 := hC.2 1 (by decide)
  have ha2 : D.col 2 ≤ D.row 3 := hC.2 2 (by decide)
  have hd0 := D.row_nonempty 0
  have hd1 := D.row_nonempty 1
  have hd2 := D.row_nonempty 2
  have hd3 := D.row_nonempty 3
  have hc01 := D.col_strictAnti (show (0 : Fin 4) < 1 by decide)
  have hc12 := D.col_strictAnti (show (1 : Fin 4) < 2 by decide)
  have hc23 := D.col_strictAnti (show (2 : Fin 4) < 3 by decide)
  rintro ⟨i, j⟩ hp
  have hn : D.row i < D.col j := (Finset.mem_filter.mp hp).2
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

/-- The exact three-site pattern follows from the actual count, not from a
named Hessenberg certificate. -/
theorem three_negative_four_entries (D : BetaDiagram 4)
    (hC : D.Connected) (hN : negativeCount D = 3) :
    D.row 2 < D.col 0 ∧ D.row 3 < D.col 0 ∧ D.row 3 < D.col 1 := by
  classical
  let S : Finset (Fin 4 × Fin 4) := {(2, 0), (3, 0), (3, 1)}
  have hsub : negativeSites D ⊆ S := D.connected_four_negative_sites_subset hC
  have hcard : S.card = 3 := by decide
  have he : negativeSites D = S := Finset.eq_of_subset_of_card_le hsub (by
    change S.card ≤ (negativeSites D).card
    change (negativeSites D).card = 3 at hN
    rw [hcard, hN])
  have h20 : ((2 : Fin 4), (0 : Fin 4)) ∈ negativeSites D := by rw [he]; simp [S]
  have h30 : ((3 : Fin 4), (0 : Fin 4)) ∈ negativeSites D := by rw [he]; simp [S]
  have h31 : ((3 : Fin 4), (1 : Fin 4)) ∈ negativeSites D := by rw [he]; simp [S]
  exact ⟨(Finset.mem_filter.mp h20).2, (Finset.mem_filter.mp h30).2,
    (Finset.mem_filter.mp h31).2⟩

/-- All zero-free connected four-row opposite endpoint comparisons detect symmetry.
The three-negative case is a residual three-row determinant, so no unfinished
four-row arbitrary-mate classification is imported as a hypothesis. -/
theorem endpointDifference_ne_zero_four (D : BetaDiagram 4)
    (hC : D.Connected) (hZ : D.ZeroFree) (hS : ¬ D.Symmetric)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  classical
  have hmax : negativeCount D ≤ 3 := by
    have hh := Finset.card_le_card (D.connected_four_negative_sites_subset hC)
    simpa [negativeCount] using hh
  by_cases h0 : negativeCount D = 0
  · have hD : D.Dense := by
      intro i j
      have hnon : D.col j ≤ D.row i := by
        by_contra hn
        have hm : (i, j) ∈ negativeSites D :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            change D.row i < D.col j
            omega⟩
        have he : negativeSites D = ∅ := Finset.card_eq_zero.mp h0
        rw [he] at hm
        exact Finset.notMem_empty _ hm
      have hz := hZ i j
      omega
    exact EndpointLeader.difference_ne_zero D (D.endpointLeader_dense hD hS) t ht
  by_cases h1 : negativeCount D = 1
  · exact EndpointLeader.difference_ne_zero D (D.endpointLeader_one_negative hC hZ h1 hS) t ht
  by_cases h2 : negativeCount D = 2
  · exact EndpointLeader.difference_ne_zero D (D.endpointLeader_two_negative_four hC hZ h2) t ht
  have h3 : negativeCount D = 3 := by omega
  obtain ⟨h20, h30, h31⟩ := D.three_negative_four_entries hC h3
  exact D.endpointDifference_ne_zero_hessenberg_four hC hZ h20 h30 h31 hS t ht

/-- A connected four-row maximal child produces the five-row prescribed leader
by actual endpoint comparison, without assuming a classification or exception exclusion. -/
theorem endpoint_top_connected_four_corner (D : BetaDiagram 5)
    (hC : D.Connected) (hZ : D.ZeroFree)
    (hChild : (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hC hZ)).Connected)
    (hS : ¬ D.Symmetric) : D.EndpointTop := by
  let hP := D.positiveCorner_of_connected_zeroFree hC hZ
  apply D.endpointTop_of_endpointCoefficient_ne_zero
  by_cases htie : D.topMargin = D.bottomMargin
  · rw [D.endpointCoefficient_tied hP htie]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    exact (D.cornerDiagram hP).endpointDifference_ne_zero_four hChild
      (fun i j => hZ i.succ j.castSucc)
      (fun hs => hS (D.symmetric_of_tied_corner hP htie hs))
      D.topMargin D.topMargin_pos
  · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- An actual disconnected cut can be selected from failure of connectedness. -/
theorem exists_negative_cut {k : ℕ} (D : BetaDiagram k)
    (hk : 0 < k) (hC : ¬ D.Connected) :
    ∃ i : Fin k, ∃ hi : i.val + 1 < k, D.row ⟨i.val + 1, hi⟩ < D.col i := by
  by_contra h
  apply hC
  refine ⟨hk, ?_⟩
  intro i hi
  exact le_of_not_gt (fun hcut => h ⟨i, hi, hcut⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The lower-left rectangle of a real cut is a lower bound for the actual negative count. -/
theorem cut_rectangle_le_negativeCount {k : ℕ} (D : BetaDiagram k)
    (i : Fin k) (hi : i.val + 1 < k) (hcut : D.row ⟨i.val + 1, hi⟩ < D.col i) :
    (i.val + 1) * (k - (i.val + 1)) ≤ negativeCount D := by
  let a := i.val + 1
  let b := k - a
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [a, b]; omega
  have hab : a + b = k := by dsimp [a, b]; omega
  let E : BetaDiagram (a + b) := D.reindexOrder hab
  have hr : (Fin.cast hab (⟨a, by omega⟩ : Fin (a + b))) =
      (⟨i.val + 1, hi⟩ : Fin k) := by apply Fin.ext; rfl
  have hc : (Fin.cast hab (⟨a - 1, by omega⟩ : Fin (a + b))) = i := by
    apply Fin.ext
    dsimp [a]
  have hcutE : E.row ⟨a, by omega⟩ < E.col ⟨a - 1, by omega⟩ := by
    change D.row (Fin.cast hab ⟨a, by omega⟩) < D.col (Fin.cast hab ⟨a - 1, by omega⟩)
    rw [hr, hc]
    exact hcut
  have hbudget := E.negativeCount_at_cut ha hb hcutE
  have hcount : negativeCount E = negativeCount D := D.reindexOrder_negativeCount hab
  rw [hcount] at hbudget
  change a * b ≤ negativeCount D
  omega

/-- A cut in a board of order `k` costs at least `k-1` negatives.
Consequently every given board is connected once its order exceeds its count by two. -/
theorem connected_of_negativeCount_add_two_le {k : ℕ} (D : BetaDiagram k)
    (hN : negativeCount D + 2 ≤ k) : D.Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  by_contra h
  have hcut : D.row ⟨i.val + 1, hi⟩ < D.col i := by omega
  have hrect := D.cut_rectangle_le_negativeCount i hi hcut
  let a := i.val + 1
  let b := k - a
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [a, b]; omega
  have hab : a + b = k := by dsimp [a, b]; omega
  have hrect' : (a : ℤ) * (b : ℤ) ≤ negativeCount D := by exact_mod_cast hrect
  have hsum : (a : ℤ) + (b : ℤ) = k := by exact_mod_cast hab
  have hcount : (negativeCount D : ℤ) + 2 ≤ k := by exact_mod_cast hN
  have hprod : 0 ≤ ((a : ℤ) - 1) * ((b : ℤ) - 1) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- The four-row budget permits only singleton-plus-three and two-plus-two cuts.
The connectedness of every nontrivial remaining core is produced by the actual cut count. -/
theorem endpointDifference_ne_zero_four_budget (D : BetaDiagram 4)
    (hZ : D.ZeroFree) (hN : negativeCount D ≤ 4) (hS : ¬ D.Symmetric)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  classical
  by_cases hC : D.Connected
  · exact D.endpointDifference_ne_zero_four hC hZ hS t ht
  obtain ⟨i, hi, hcut⟩ := D.exists_negative_cut (by decide) hC
  fin_cases i
  · change D.row 1 < D.col 0 at hcut
    have hb := D.negativeCount_at_cut (a := 1) (b := 3) (by decide) (by decide) hcut
    have he : negativeCount (D.suffix (a := 1) (b := 3)) = negativeCount D.tail := by
      have hr : (D.suffix (a := 1) (b := 3)).row = D.tail.row := by
        funext j; fin_cases j <;> rfl
      have hc : (D.suffix (a := 1) (b := 3)).col = D.tail.col := by
        funext j; fin_cases j <;> rfl
      simp only [negativeCount, negativeSites, hr, hc]
    rw [he] at hb
    have hcore : D.tail.Connected := D.tail.connected_of_negativeCount_add_two_le (by omega)
    exact D.endpointDifference_ne_zero_first_singleton hcut hcore t ht
  · change D.row 2 < D.col 1 at hcut
    have hb := D.negativeCount_at_cut (a := 2) (b := 2) (by decide) (by decide) hcut
    have hT : (D.betaPrefix (a := 2) (b := 2)).Connected :=
      connected_of_negativeCount_add_two_le _ (by omega)
    have hU : (D.suffix (a := 2) (b := 2)).Connected :=
      connected_of_negativeCount_add_two_le _ (by omega)
    intro hz
    exact hS (D.endpointDifference_two_two_eq_zero_implies_symmetric hcut hT hU t ht hz)
  · change D.row 3 < D.col 2 at hcut
    have hb := D.negativeCount_at_cut (a := 3) (b := 1) (by decide) (by decide) hcut
    have he : negativeCount (D.betaPrefix (a := 3) (b := 1)) = negativeCount D.init := rfl
    rw [he] at hb
    have hcore : D.init.Connected := D.init.connected_of_negativeCount_add_two_le (by omega)
    exact D.endpointDifference_ne_zero_last_singleton hcut hcore t ht
  · norm_num at hi

set_option backward.isDefEq.respectTransparency false in
/-- A five-row disconnected board of budget four has exactly one terminal singleton,
and its four-row core is connected with no internal negatives. -/
theorem endpointDifference_ne_zero_five_disconnected_budget (D : BetaDiagram 5)
    (hN : negativeCount D ≤ 4) (hC : ¬ D.Connected)
    (t : ℤ) (ht : 0 < t) : D.endpointDifference t ht ≠ 0 := by
  obtain ⟨i, hi, hcut⟩ := D.exists_negative_cut (by decide) hC
  fin_cases i
  · change D.row 1 < D.col 0 at hcut
    have hb := D.negativeCount_at_cut (a := 1) (b := 4) (by decide) (by decide) hcut
    have he : negativeCount (D.suffix (a := 1) (b := 4)) = negativeCount D.tail := by
      have hr : (D.suffix (a := 1) (b := 4)).row = D.tail.row := by
        funext j; fin_cases j <;> rfl
      have hc : (D.suffix (a := 1) (b := 4)).col = D.tail.col := by
        funext j; fin_cases j <;> rfl
      simp only [negativeCount, negativeSites, hr, hc]
    rw [he] at hb
    have hcore : D.tail.Connected := D.tail.connected_of_negativeCount_add_two_le (by omega)
    exact D.endpointDifference_ne_zero_first_singleton hcut hcore t ht
  · change D.row 2 < D.col 1 at hcut
    have hb := D.negativeCount_at_cut (a := 2) (b := 3) (by decide) (by decide) hcut
    omega
  · change D.row 3 < D.col 2 at hcut
    have hb := D.negativeCount_at_cut (a := 3) (b := 2) (by decide) (by decide) hcut
    omega
  · change D.row 4 < D.col 3 at hcut
    have hb := D.negativeCount_at_cut (a := 4) (b := 1) (by decide) (by decide) hcut
    have he : negativeCount (D.betaPrefix (a := 4) (b := 1)) = negativeCount D.init := rfl
    rw [he] at hb
    have hcore : D.init.Connected := D.init.connected_of_negativeCount_add_two_le (by omega)
    exact D.endpointDifference_ne_zero_last_singleton hcut hcore t ht
  · norm_num at hi

/-- The endpoint-leading assertion in `lem:small-negative-endpoint`, at every order
at least five.  The induction consumes actual negative counts and actual cuts;
the four-row exception is excluded by a proved residual determinant. -/
theorem endpoint_top_small_negative (D : BetaDiagram (n + 5))
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D ≤ 4)
    (hS : ¬ D.Symmetric) : D.EndpointTop := by
  induction n with
  | zero =>
    let hP := D.positiveCorner_of_connected_zeroFree hC hZ
    apply D.endpointTop_of_endpointCoefficient_ne_zero
    by_cases htie : D.topMargin = D.bottomMargin
    · rw [D.endpointCoefficient_tied hP htie]
      apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      exact (D.cornerDiagram hP).endpointDifference_ne_zero_four_budget
        (fun i j => hZ i.succ j.castSucc)
        (by rw [D.corner_negativeCount hP]; exact hN)
        (fun hs => hS (D.symmetric_of_tied_corner hP htie hs))
        D.topMargin D.topMargin_pos
    · exact D.endpointCoefficient_ne_zero_untied hP htie
  | succ n ih =>
    let hP := D.positiveCorner_of_connected_zeroFree hC hZ
    have hChildN : negativeCount (D.cornerDiagram hP) ≤ 4 := by
      rw [D.corner_negativeCount hP]
      exact hN
    apply D.endpointTop_of_endpointCoefficient_ne_zero
    by_cases htie : D.topMargin = D.bottomMargin
    · rw [D.endpointCoefficient_tied hP htie]
      apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      by_cases hChildC : (D.cornerDiagram hP).Connected
      · have htop := ih (D.cornerDiagram hP) hChildC
          (fun i j => hZ i.succ j.castSucc) hChildN
          (fun hs => hS (D.symmetric_of_tied_corner hP htie hs))
        exact EndpointLeader.difference_ne_zero _
          ((D.cornerDiagram hP).endpointLeader_of_endpointCoefficient_ne_zero htop.2.2.1)
          D.topMargin D.topMargin_pos
      · cases n with
        | zero =>
          exact (D.cornerDiagram hP).endpointDifference_ne_zero_five_disconnected_budget
            hChildN hChildC D.topMargin D.topMargin_pos
        | succ n =>
          exact False.elim (hChildC
            ((D.cornerDiagram hP).connected_of_negativeCount_add_two_le (by omega)))
    · exact D.endpointCoefficient_ne_zero_untied hP htie

/-- The small-negative fixed geometric leader supplies the communicated lifting interface. -/
theorem endpointLeader_small_negative (D : BetaDiagram (n + 5))
    (hC : D.Connected) (hZ : D.ZeroFree) (hN : negativeCount D ≤ 4)
    (hS : ¬ D.Symmetric) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero (D.endpoint_top_small_negative hC hZ hN hS).2.2.1

end BetaDiagram
end SkewJacobiNegative
