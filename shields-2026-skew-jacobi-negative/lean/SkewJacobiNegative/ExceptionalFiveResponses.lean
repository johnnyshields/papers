/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewJacobiNegative.FiveExceptionalFamilies
import SkewJacobiNegative.EndpointLeaders

namespace SkewJacobiNegative.FiveExceptional

noncomputable def D1 (P : Parameters) : CompleteRing :=
  complete P.b ^ 2 * complete (P.b + 2 * P.g - P.q) -
  complete P.b * complete (P.b + P.g) * complete (P.b + P.g - P.q) -
  complete P.b * complete (P.b + 2 * P.g) * complete (P.b - P.q) +
  complete (P.b + P.g) ^ 2 * complete (P.b - P.q)

noncomputable def D2 (P : Parameters) : CompleteRing :=
  complete P.b * complete (P.b - P.q) * complete (P.b + 2 * P.g - P.q) -
  complete P.b * complete (P.b + P.g - P.q) ^ 2 +
  complete (P.b + P.g) * complete (P.b - P.q) * complete (P.b + P.g - P.q) -
  complete (P.b + 2 * P.g) * complete (P.b - P.q) ^ 2

noncomputable def W (P : Parameters) : CompleteRing :=
  complete P.b * complete (P.b + P.g - P.q) -
  complete (P.b + P.g) * complete (P.b - P.q)

/-- The algebraic cancellation used by the first-family up response. -/
theorem response_syzygy (P : Parameters) :
    complete (P.b - P.q) * D1 P - complete P.b * D2 P = W P ^ 2 := by
  unfold D1 D2 W
  ring

private theorem negative_label (P : Parameters) (k : ℤ) (hk : k ≤ -1)
    (e : ℤ) (he : 0 ≤ e) : complete (P.b + k * P.g - e) = 0 := by
  apply complete_of_neg
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  have hg : 0 < P.g := by omega
  nlinarith

private def tripleDet {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*e*i-a*f*h-b*d*i+b*f*g+c*d*h-c*e*g

private theorem det_four_expansion {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0*tripleDet (M 1 1) (M 1 2) (M 1 3) (M 2 1) (M 2 2) (M 2 3) (M 3 1) (M 3 2) (M 3 3) -
      M 0 1*tripleDet (M 1 0) (M 1 2) (M 1 3) (M 2 0) (M 2 2) (M 2 3) (M 3 0) (M 3 2) (M 3 3) +
      M 0 2*tripleDet (M 1 0) (M 1 1) (M 1 3) (M 2 0) (M 2 1) (M 2 3) (M 3 0) (M 3 1) (M 3 3) -
      M 0 3*tripleDet (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) (M 3 0) (M 3 1) (M 3 2) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,tripleDet] <;> ring

/-- Cofactor of the first-row `a_3(t)` entry, in the actual beta matrix. -/
noncomputable def upLeaderCofactor (P : Parameters) (second : Bool) : CompleteRing :=
  ((F P second).matrix.submatrix Fin.succ (2 : Fin 5).succAbove).det -
    (if second then 0 else
      ((H P second).matrix.submatrix Fin.succ (2 : Fin 5).succAbove).det)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Both families have the claimed parameter-uniform first-row cofactor. -/
theorem upLeaderCofactor_eq (P : Parameters) (second : Bool) :
    upLeaderCofactor P second =
      -complete (P.b - P.q) * (if second then D2 P else D1 P) := by
  have hq : 0 ≤ P.q := by have := P.q_pos; omega
  have hn1 := negative_label P (-1) (by omega) 0 (by omega)
  have hn2 := negative_label P (-2) (by omega) 0 (by omega)
  have hn3 := negative_label P (-3) (by omega) 0 (by omega)
  have hq1 := negative_label P (-1) (by omega) P.q hq
  have hq2 := negative_label P (-2) (by omega) P.q hq
  have hq3 := negative_label P (-3) (by omega) P.q hq
  ring_nf at hn1 hn2 hn3 hq1 hq2 hq3
  cases second <;>
    norm_num [upLeaderCofactor, BetaDiagram.matrix, F, H, rows, fCols, hCols,
      Matrix.det_succ_row_zero, Matrix.det_unique, Matrix.submatrix_apply,
      Matrix.of_apply, Fin.sum_univ_succ, Fin.succAbove, D1, D2] <;>
    ring_nf <;> simp only [hn1, hn2, hn3, hq1, hq2, hq3] <;> ring

/-- The two interlaced alphabets remain independent throughout the standing domain. -/
theorem alphabet_indices_distinct (P : Parameters) (j k : ℕ)
    (h : P.b + (j : ℤ) * P.g = P.b + (k : ℤ) * P.g - P.q) : False := by
  have hq := P.q_pos
  have hb := P.q_le_b
  have hg := P.b_lt_g
  have hG : 0 < P.g := by omega
  have hqG : P.q < P.g := by omega
  by_cases hjk : j < k
  · have hjk' : (j : ℤ) + 1 ≤ (k : ℤ) := by omega
    have hm : ((j : ℤ) + 1) * P.g ≤ (k : ℤ) * P.g :=
      mul_le_mul_of_nonneg_right hjk' (le_of_lt hG)
    nlinarith
  · have hjk' : (k : ℤ) ≤ (j : ℤ) := by omega
    have hm := mul_le_mul_of_nonneg_right hjk' (le_of_lt hG)
    omega

/-- The sum-response leader is strictly above every fixed entry exactly in its stated regime. -/
theorem sum_leader_above_fixed (P : Parameters) (t : ℤ) (ht : P.q < t) :
    P.b + 3 * P.g < P.b + 3 * P.g - P.q + t := by omega

/-- The up-response offset lies strictly inside the core span. -/
theorem up_offset_bounds (P : Parameters) :
    0 < P.b + 3 * P.g ∧ P.b + 3 * P.g < P.b + 4 * P.g := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  omega

/-- The mixed-response offset has the same strict span bounds. -/
theorem mixed_offset_bounds (P : Parameters) :
    0 < P.b + 4 * P.g - P.q ∧
      P.b + 4 * P.g - P.q < P.b + 4 * P.g := by
  have := P.q_pos
  have := P.q_le_b
  have := P.b_lt_g
  omega

private noncomputable def responseEvaluation (P : Parameters) : CompleteRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun k =>
    if (k.val : ℤ) = P.b ∨ (k.val : ℤ) = P.b-P.q ∨
      (k.val : ℤ) = P.b+2*P.g then 1 else 0)

private theorem responseEvaluation_complete (P : Parameters) (k : ℤ) (hk : 0 < k) :
    responseEvaluation P (complete k) =
      if k = P.b ∨ k = P.b-P.q ∨ k = P.b+2*P.g then 1 else 0 := by
  let v : ℕ+ := ⟨k.toNat,by omega⟩
  have he : complete k=MvPolynomial.X v := complete_of_pos hk
  rw [he]
  unfold responseEvaluation
  rw [MvPolynomial.eval₂Hom_X']
  change (if (v.val : ℤ)=P.b ∨ (v.val : ℤ)=P.b-P.q ∨
    (v.val : ℤ)=P.b+2*P.g then (1 : ℚ) else 0) = _
  rw [show (v.val : ℤ)=k from Int.toNat_of_nonneg hk.le]

/-- A single exact algebra homomorphism witnesses nonvanishing in both families. -/
theorem D_ne_zero (P : Parameters) (hp : P.q < P.b) :
    D1 P ≠ 0 ∧ D2 P ≠ 0 := by
  have hq := P.q_pos
  have hb := P.b_lt_g
  have h0 : responseEvaluation P (complete P.b) = 1 := by
    rw [responseEvaluation_complete P _ (by omega)]
    simp
  have hb0 : responseEvaluation P (complete (P.b-P.q)) = 1 := by
    rw [responseEvaluation_complete P _ (by omega)]
    simp
  have h1 : responseEvaluation P (complete (P.b+P.g)) = 0 := by
    rw [responseEvaluation_complete P _ (by omega)]
    split_ifs <;> first | rfl | omega
  have hb1 : responseEvaluation P (complete (P.b+P.g-P.q)) = 0 := by
    rw [responseEvaluation_complete P _ (by omega)]
    split_ifs <;> first | rfl | omega
  have h2 : responseEvaluation P (complete (P.b+2*P.g)) = 1 := by
    rw [responseEvaluation_complete P _ (by omega)]
    simp
  have hb2 : responseEvaluation P (complete (P.b+2*P.g-P.q)) = 0 := by
    rw [responseEvaluation_complete P _ (by omega)]
    split_ifs <;> first | rfl | omega
  have hd1 : responseEvaluation P (D1 P) = -1 := by
    simp [D1, h0, hb0, h1, hb1, h2, hb2]
  have hd2 : responseEvaluation P (D2 P) = -1 := by
    simp [D2, h0, hb0, h1, hb1, h2, hb2]
  constructor <;> intro hz
  · rw [hz, map_zero] at hd1
    norm_num at hd1
  · rw [hz, map_zero] at hd2
    norm_num at hd2

theorem upLeaderCofactor_ne_zero (P : Parameters) (hp : P.q < P.b)
    (second : Bool) : upLeaderCofactor P second ≠ 0 := by
  rw [upLeaderCofactor_eq]
  apply mul_ne_zero
  · exact neg_ne_zero.mpr ((complete_ne_zero_iff _).2 (by omega))
  · cases second
    · exact (D_ne_zero P hp).1
    · exact (D_ne_zero P hp).2

noncomputable def downLeaderCofactor (P : Parameters) (second : Bool) : CompleteRing :=
  -((F P second).matrix.submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det +
    ((H P second).matrix.submatrix (1 : Fin 5).succAbove (4 : Fin 5).succAbove).det

noncomputable def sumLeaderCofactor (P : Parameters) (second : Bool) : CompleteRing :=
  -((F P second).matrix.submatrix Fin.succ (1 : Fin 5).succAbove).det -
    (if second then
      ((H P second).matrix.submatrix Fin.succ (2 : Fin 5).succAbove).det else 0)

noncomputable def mixedLeaderCofactor (P : Parameters) (second middle : Bool) :
    CompleteRing :=
  -((if middle then F P second else H P second).matrix.submatrix
      Fin.succ (3 : Fin 5).succAbove).det

noncomputable def K (P : Parameters) (second : Bool) : CompleteRing :=
  if second then complete P.b * complete (P.b-P.q) else complete P.b ^ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The remaining three rows of the response table, as actual matrix cofactors. -/
theorem remaining_response_cofactors (P : Parameters) (second : Bool) :
    downLeaderCofactor P second =
        complete (P.b-P.q) * (if second then D2 P else D1 P) ∧
    sumLeaderCofactor P second =
        complete P.b * (if second then D2 P else D1 P) ∧
    (∀ middle, mixedLeaderCofactor P second middle = -K P second * W P) := by
  have hq : 0 ≤ P.q := by have := P.q_pos; omega
  have hn1 := negative_label P (-1) (by omega) 0 (by omega)
  have hn2 := negative_label P (-2) (by omega) 0 (by omega)
  have hn3 := negative_label P (-3) (by omega) 0 (by omega)
  have hq1 := negative_label P (-1) (by omega) P.q hq
  have hq2 := negative_label P (-2) (by omega) P.q hq
  have hq3 := negative_label P (-3) (by omega) P.q hq
  ring_nf at hn1 hn2 hn3 hq1 hq2 hq3
  constructor
  · cases second
    all_goals
      unfold downLeaderCofactor
      simp_rw [det_four_expansion]
      norm_num [BetaDiagram.matrix,F,H,rows,fCols,hCols,Matrix.submatrix,
        Fin.succAbove,D1,D2,tripleDet]
      ring_nf
      simp only [hn1,hn2,hn3,hq1,hq2,hq3]
      ring
  constructor
  · cases second
    all_goals
      unfold sumLeaderCofactor
      simp only [Bool.false_eq_true,↓reduceIte]
      simp_rw [det_four_expansion]
      norm_num [BetaDiagram.matrix,F,H,rows,fCols,hCols,Matrix.submatrix,
        Fin.succAbove,D1,D2,tripleDet]
      ring_nf
      simp only [hn1,hn2,hn3,hq1,hq2,hq3]
      ring
  · intro middle
    cases middle <;> cases second
    all_goals
      unfold mixedLeaderCofactor
      simp only [Bool.false_eq_true,↓reduceIte]
      simp_rw [det_four_expansion]
      norm_num [BetaDiagram.matrix,F,H,rows,fCols,hCols,Matrix.submatrix,
        Fin.succAbove,K,W,tripleDet]
      ring_nf
      simp only [hn1,hn2,hn3,hq1,hq2,hq3]
      ring

private noncomputable def wEvaluation (P : Parameters) : CompleteRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun k =>
    if (k.val : ℤ) = P.b+P.g ∨ (k.val : ℤ) = P.b-P.q then 1 else 0)

private theorem wEvaluation_complete (P : Parameters) (k : ℤ) (hk : 0 < k) :
    wEvaluation P (complete k) =
      if k = P.b+P.g ∨ k = P.b-P.q then 1 else 0 := by
  let v : ℕ+ := ⟨k.toNat,by omega⟩
  have he : complete k=MvPolynomial.X v := complete_of_pos hk
  rw [he]
  unfold wEvaluation
  rw [MvPolynomial.eval₂Hom_X']
  change (if (v.val : ℤ)=P.b+P.g ∨ (v.val : ℤ)=P.b-P.q then (1 : ℚ) else 0) = _
  rw [show (v.val : ℤ)=k from Int.toNat_of_nonneg hk.le]

theorem W_ne_zero (P : Parameters) (hp : P.q < P.b) : W P ≠ 0 := by
  have hq := P.q_pos
  have hg := P.b_lt_g
  have h0 : wEvaluation P (complete P.b) = 0 := by
    rw [wEvaluation_complete P _ (by omega)]
    split_ifs <;> first | rfl | omega
  have hb0 : wEvaluation P (complete (P.b-P.q)) = 1 := by
    rw [wEvaluation_complete P _ (by omega)]
    simp
  have h1 : wEvaluation P (complete (P.b+P.g)) = 1 := by
    rw [wEvaluation_complete P _ (by omega)]
    simp
  have hb1 : wEvaluation P (complete (P.b+P.g-P.q)) = 0 := by
    rw [wEvaluation_complete P _ (by omega)]
    split_ifs <;> first | rfl | omega
  have hw : wEvaluation P (W P) = -1 := by simp [W, h0, hb0, h1, hb1]
  intro hz
  rw [hz, map_zero] at hw
  norm_num at hw

theorem remaining_response_cofactors_ne_zero (P : Parameters) (hp : P.q < P.b)
    (second : Bool) :
    downLeaderCofactor P second ≠ 0 ∧ sumLeaderCofactor P second ≠ 0 ∧
      (∀ middle, mixedLeaderCofactor P second middle ≠ 0) := by
  have hq := P.q_pos
  have hd : (if second then D2 P else D1 P) ≠ 0 := by
    cases second
    · exact (D_ne_zero P hp).1
    · exact (D_ne_zero P hp).2
  have ha : complete P.b ≠ 0 := (complete_ne_zero_iff _).2 (by omega)
  have hb : complete (P.b-P.q) ≠ 0 := (complete_ne_zero_iff _).2 (by omega)
  obtain ⟨hv, hc, hm⟩ := remaining_response_cofactors P second
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]
    exact mul_ne_zero hb hd
  · rw [hc]
    exact mul_ne_zero ha hd
  · intro middle
    rw [hm]
    apply mul_ne_zero
    · apply neg_ne_zero.mpr
      cases second <;> simp only [K, Bool.false_eq_true, ↓reduceIte]
      · exact pow_ne_zero _ ha
      · exact mul_ne_zero ha hb
    · exact W_ne_zero P hp

private def positiveIndex (k : ℤ) (hk : 0 < k) : ℕ+ :=
  ⟨k.toNat, by omega⟩

private theorem pderiv_complete_eq_zero (k : ℤ) (hk : 0 < k) (l : ℤ)
    (hl : l ≠ k) :
    MvPolynomial.pderiv (positiveIndex k hk) (complete l) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hm
  have h := (mem_vars_complete_iff l (positiveIndex k hk)).mp hm
  change (k.toNat : ℤ)=l at h
  rw [Int.toNat_of_nonneg hk.le] at h
  exact hl h.symm

private theorem pderiv_schur_private {n : ℕ} (D : BetaDiagram (n+1))
    (k : ℤ) (hk : 0 < k) (r c : Fin (n+1))
    (he : D.row r-D.col c = k)
    (hprivate : ∀ a b, a ≠ r ∨ b ≠ c → D.row a-D.col b ≠ k) :
    MvPolynomial.pderiv (positiveIndex k hk) D.schur = D.cofactor r c := by
  unfold BetaDiagram.schur BetaDiagram.cofactor
  apply pderiv_det_private_of_derivative_zero
  · change complete (D.row r-D.col c) = _
    rw [he, complete_of_pos hk]
    rfl
  · intro a b hab
    exact pderiv_complete_eq_zero k hk _ (hprivate a b hab)

private theorem pderiv_schur_absent {n : ℕ} (D : BetaDiagram n)
    (k : ℤ) (hk : 0 < k)
    (habsent : ∀ a b, D.row a-D.col b ≠ k) :
    MvPolynomial.pderiv (positiveIndex k hk) D.schur = 0 := by
  apply pderiv_det_eq_zero
  intro a b
  exact pderiv_complete_eq_zero k hk _ (habsent a b)

set_option maxHeartbeats 0 in
/-- Actual coefficient extraction of the up response at its largest moving generator. -/
theorem up_response_coefficient (P : Parameters) (second : Bool)
    (t : ℤ) (ht : 0 < t) :
    MvPolynomial.pderiv
      (positiveIndex (P.b+3*P.g+t) (by
        have := P.q_pos; have := P.q_le_b; have := P.b_lt_g; omega))
      ((F P second).extendTop t ht).schur -
    MvPolynomial.pderiv
      (positiveIndex (P.b+3*P.g+t) (by
        have := P.q_pos; have := P.q_le_b; have := P.b_lt_g; omega))
      ((H P second).extendTop t ht).schur =
        -complete (P.b-P.q)*(if second then D2 P else D1 P) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  have hk : 0 < P.b+3*P.g+t := by omega
  have hf := pderiv_schur_private ((F P second).extendTop t ht)
    (P.b+3*P.g+t) hk 0 2
    (by simp [BetaDiagram.extendTop, F, rows, fCols]; omega)
    (by
      intro a b hab
      cases second <;> fin_cases a <;> fin_cases b <;>
        norm_num [BetaDiagram.extendTop, F, rows, fCols] at * <;> omega)
  have hf' : MvPolynomial.pderiv (positiveIndex (P.b+3*P.g+t) hk)
      ((F P second).extendTop t ht).schur =
        ((F P second).matrix.submatrix Fin.succ (2 : Fin 5).succAbove).det := by
    rw [hf]
    change (-1 : CompleteRing)^(0+2) *
      ((F P second).extendTop t ht).unsignedMinor 0 2 = _
    rw [BetaDiagram.extendTop_unsignedMinor]
    norm_num [BetaDiagram.unsignedMinor]
  cases second
  · have hh := pderiv_schur_private ((H P false).extendTop t ht)
      (P.b+3*P.g+t) hk 0 2
      (by simp [BetaDiagram.extendTop, H, rows, hCols]; omega)
      (by
        intro a b hab
        fin_cases a <;> fin_cases b <;>
          norm_num [BetaDiagram.extendTop, H, rows, hCols] at * <;> omega)
    rw [hf', hh]
    change _ - (-1 : CompleteRing)^(0+2) *
      ((H P false).extendTop t ht).unsignedMinor 0 2 = _
    rw [BetaDiagram.extendTop_unsignedMinor]
    simpa [upLeaderCofactor, BetaDiagram.unsignedMinor] using upLeaderCofactor_eq P false
  · have hh := pderiv_schur_absent ((H P true).extendTop t ht)
      (P.b+3*P.g+t) hk (by
        intro a b
        fin_cases a <;> fin_cases b <;>
          norm_num [BetaDiagram.extendTop, H, rows, hCols] <;> omega)
    rw [hf', hh]
    simpa [upLeaderCofactor] using upLeaderCofactor_eq P true

private theorem top_private_coefficient (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t)
    (k : ℤ) (hk : 0 < k) (j : Fin 5)
    (he : (D.extendTop t ht).row 0-(D.extendTop t ht).col j = k)
    (hp : ∀ a b, a ≠ 0 ∨ b ≠ j →
      (D.extendTop t ht).row a-(D.extendTop t ht).col b ≠ k) :
    MvPolynomial.pderiv (positiveIndex k hk) (D.extendTop t ht).schur =
      (-1 : CompleteRing)^j.val *
        (D.matrix.submatrix Fin.succ j.succAbove).det := by
  rw [pderiv_schur_private _ k hk 0 j he hp]
  change (-1 : CompleteRing)^(0+j.val) * (D.extendTop t ht).unsignedMinor 0 j = _
  rw [BetaDiagram.extendTop_unsignedMinor]
  simp [BetaDiagram.unsignedMinor]

private theorem pderiv_complete_index (k : ℤ) (hk : 0 < k) (l : ℤ) :
    MvPolynomial.pderiv (positiveIndex k hk) (complete l) =
      if l = k then 1 else 0 := by
  classical
  by_cases hl : l = k
  · subst l
    rw [complete_of_pos hk]
    change MvPolynomial.pderiv (⟨k.toNat,by omega⟩ : ℕ+)
      (MvPolynomial.X (⟨k.toNat,by omega⟩ : ℕ+)) = _
    rw [MvPolynomial.pderiv_X_self,if_pos rfl] <;> rfl
  · rw [pderiv_complete_eq_zero k hk l hl, if_neg hl]

open scoped BigOperators

private theorem labels_pow {p : CompleteRing} {k : ℤ} (n : ℕ)
    (h : LabelsBelow p k) : LabelsBelow (p^n) k := by
  induction n with
  | zero => simp [LabelsBelow]
  | succ n ih => simpa only [pow_succ] using ih.mul h

private theorem labels_mono {p : CompleteRing} {k l : ℤ}
    (h : LabelsBelow p k) (hle : k ≤ l) : LabelsBelow p l :=
  fun v hv => lt_of_lt_of_le (h v hv) hle

private theorem derivative_zero_of_labels (k : ℤ) (hk : 0 < k)
    (p : CompleteRing) (hp : LabelsBelow p k) :
    MvPolynomial.pderiv (positiveIndex k hk) p=0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  apply hp.not_mem
  change (k.toNat : ℤ)=k
  exact Int.toNat_of_nonneg hk.le

private theorem top_schur_sum (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    (D.extendTop t ht).schur =
      ∑ j : Fin 5, complete (D.row 0-D.col j+t)*D.cofactor 0 j := by
  unfold BetaDiagram.schur
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j hj
  change (-1)^j.val*complete ((D.row 0+t)-D.col j)*
    (D.extendTop t ht).unsignedMinor 0 j = _
  rw [BetaDiagram.extendTop_unsignedMinor]
  simp only [BetaDiagram.cofactor,BetaDiagram.unsignedMinor,Fin.val_zero,zero_add]
  rw [show D.row 0+t-D.col j=D.row 0-D.col j+t by ring]
  ring

private theorem bottom_schur_sum (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    (D.extendBottom t ht).schur =
      ∑ i : Fin 5, complete (D.row i-D.col (Fin.last 4)+t)*D.cofactor i (Fin.last 4) := by
  unfold BetaDiagram.schur
  rw [Matrix.det_succ_column _ (Fin.last 4)]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (D.extendBottom t ht).matrix i (Fin.last 4) =
      complete (D.row i-D.col (Fin.last 4)+t) := by
    simp only [BetaDiagram.matrix,Matrix.of_apply,BetaDiagram.extendBottom,ite_true]
    congr 1
    ring
  rw [he]
  change (-1)^(i.val+4)*complete (D.row i-D.col (Fin.last 4)+t)*
    (D.extendBottom t ht).unsignedMinor i (Fin.last 4) = _
  rw [BetaDiagram.extendBottom_unsignedMinor]
  simp only [BetaDiagram.cofactor,BetaDiagram.unsignedMinor,Fin.val_last]
  ring

private theorem F_top_labels (P : Parameters) (second : Bool) (j : Fin 5) :
    (F P second).row 0-(F P second).col j =
      (![P.b+P.g-(if second then P.q else 0),P.b+3*P.g-P.q,P.b+3*P.g,
        P.b+4*P.g-P.q,P.b+4*P.g] : Fin 5 → ℤ) j := by
  cases second <;> fin_cases j <;> norm_num [F,rows,fCols] <;> ring

private theorem H_top_labels (P : Parameters) (second : Bool) (j : Fin 5) :
    (H P second).row 0-(H P second).col j =
      (![P.b+2*P.g-P.q,P.b+2*P.g,P.b+3*P.g-(if second then P.q else 0),
        P.b+4*P.g-P.q,P.b+4*P.g] : Fin 5 → ℤ) j := by
  cases second <;> fin_cases j <;> norm_num [H,rows,hCols] <;> ring

private theorem first_cofactor_labels (P : Parameters) (second middle : Bool) (j : Fin 5) :
    LabelsBelow ((if middle then F P second else H P second).cofactor 0 j)
      (P.b+3*P.g+1) := by
  let D := if middle then F P second else H P second
  intro v hv
  have hb := D.first_row_minor_labels j v (D.cofactor_vars_subset 0 j hv)
  change (v.val : ℤ) ≤ D.row 1-D.col 4 at hb
  cases middle <;> norm_num [D,F,H,rows,fCols,hCols] at hb <;> omega

private noncomputable def bottomDelta (P : Parameters) (second : Bool) (i : Fin 5) :
    CompleteRing := (F P second).cofactor i 4-(H P second).cofactor i 4

private theorem bottomDelta_zero (P : Parameters) (second : Bool) :
    bottomDelta P second 0=0 := by
  have hq : 0 ≤ P.q := by have := P.q_pos; omega
  have hn1 := negative_label P (-1) (by omega) 0 (by omega)
  have hn2 := negative_label P (-2) (by omega) 0 (by omega)
  have hn3 := negative_label P (-3) (by omega) 0 (by omega)
  have hq1 := negative_label P (-1) (by omega) P.q hq
  have hq2 := negative_label P (-2) (by omega) P.q hq
  have hq3 := negative_label P (-3) (by omega) P.q hq
  ring_nf at hn1 hn2 hn3 hq1 hq2 hq3
  unfold bottomDelta BetaDiagram.cofactor
  simp_rw [det_four_expansion]
  cases second <;>
    norm_num [BetaDiagram.matrix,F,H,rows,fCols,hCols,Matrix.submatrix,
      Fin.succAbove,tripleDet] <;>
    ring_nf <;> simp only [hn1,hn2,hn3,hq1,hq2,hq3] <;> ring

private theorem bottomDelta_one (P : Parameters) (second : Bool) :
    bottomDelta P second 1=downLeaderCofactor P second := by
  norm_num [bottomDelta,downLeaderCofactor,BetaDiagram.cofactor]

private def responseMatrix {R : Type*} [Zero R] (a b : Fin 5 → R)
    (second middle : Bool) : Matrix (Fin 5) (Fin 5) R :=
  if middle then
    if second then
      ![![b 1,b 3,a 3,b 4,a 4],![b 0,b 2,a 2,b 3,a 3],![0,b 1,a 1,b 2,a 2],
        ![0,b 0,a 0,b 1,a 1],![0,0,0,b 0,a 0]]
    else
      ![![a 1,b 3,a 3,b 4,a 4],![a 0,b 2,a 2,b 3,a 3],![0,b 1,a 1,b 2,a 2],
        ![0,b 0,a 0,b 1,a 1],![0,0,0,b 0,a 0]]
  else
    if second then
      ![![b 2,a 2,b 3,b 4,a 4],![b 1,a 1,b 2,b 3,a 3],![b 0,a 0,b 1,b 2,a 2],
        ![0,0,b 0,b 1,a 1],![0,0,0,b 0,a 0]]
    else
      ![![b 2,a 2,a 3,b 4,a 4],![b 1,a 1,a 2,b 3,a 3],![b 0,a 0,a 1,b 2,a 2],
        ![0,0,a 0,b 1,a 1],![0,0,0,b 0,a 0]]

private noncomputable def actualA (P : Parameters) (j : Fin 5) : CompleteRing :=
  complete (P.b+(j.val : ℤ)*P.g)
private noncomputable def actualB (P : Parameters) (j : Fin 5) : CompleteRing :=
  complete (P.b+(j.val : ℤ)*P.g-P.q)
private def clipB {R : Type*} [Zero R] (b : Fin 5 → R) (j : Fin 5) : R :=
  if j=4 then 0 else b j

private theorem responseMatrix_F_first (P : Parameters) :
    (F P false).matrix=responseMatrix (actualA P) (actualB P) false true := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [responseMatrix,actualA,actualB,BetaDiagram.matrix,F,rows,fCols,Matrix.cons_val] <;>
    first | rfl | (solve | congr 1 <;> ring) | exact complete_of_neg (by omega) |
      (symm; exact complete_of_neg (by omega))

private theorem responseMatrix_F_second (P : Parameters) :
    (F P true).matrix=responseMatrix (actualA P) (actualB P) true true := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [responseMatrix,actualA,actualB,BetaDiagram.matrix,F,rows,fCols,Matrix.cons_val] <;>
    first | rfl | (solve | congr 1 <;> ring) | exact complete_of_neg (by omega) |
      (symm; exact complete_of_neg (by omega))

private theorem responseMatrix_H_first (P : Parameters) :
    (H P false).matrix=responseMatrix (actualA P) (actualB P) false false := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [responseMatrix,actualA,actualB,BetaDiagram.matrix,H,rows,hCols,Matrix.cons_val] <;>
    first | rfl | (solve | congr 1 <;> ring) | exact complete_of_neg (by omega) |
      (symm; exact complete_of_neg (by omega))

private theorem responseMatrix_H_second (P : Parameters) :
    (H P true).matrix=responseMatrix (actualA P) (actualB P) true false := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [responseMatrix,actualA,actualB,BetaDiagram.matrix,H,rows,hCols,Matrix.cons_val] <;>
    first | rfl | (solve | congr 1 <;> ring) | exact complete_of_neg (by omega) |
      (symm; exact complete_of_neg (by omega))

private theorem responseMatrix_actual (P : Parameters) (second middle : Bool) :
    (if middle then F P second else H P second).matrix =
      responseMatrix (actualA P) (actualB P) second middle := by
  cases middle <;> cases second
  · exact responseMatrix_H_first P
  · exact responseMatrix_H_second P
  · exact responseMatrix_F_first P
  · exact responseMatrix_F_second P

private theorem bottom_minor_clip {R : Type*} [CommRing R]
    (a b : Fin 5 → R) (second : Bool) (i : Fin 5) :
    ((responseMatrix a b second true).submatrix i.succAbove (4 : Fin 5).succAbove).det -
        ((responseMatrix a b second false).submatrix i.succAbove (4 : Fin 5).succAbove).det =
      ((responseMatrix a (clipB b) second true).submatrix i.succAbove (4 : Fin 5).succAbove).det -
        ((responseMatrix a (clipB b) second false).submatrix i.succAbove (4 : Fin 5).succAbove).det := by
  simp_rw [det_four_expansion]
  cases second <;> fin_cases i <;>
    norm_num [responseMatrix,clipB,Matrix.submatrix,Fin.succAbove,tripleDet] <;> ring

private theorem labels_det {n : ℕ} (M : Matrix (Fin n) (Fin n) CompleteRing) (k : ℤ)
    (h : ∀ i j, LabelsBelow (M i j) k) : LabelsBelow M.det k := by
  intro v hv
  by_contra hge
  have hn : v ∉ M.det.vars := not_mem_vars_det M v (by
    intro i j hm
    have hh := h i j v hm
    omega)
  exact hn hv

private theorem clipped_entry_labels (P : Parameters) (second middle : Bool)
    (i : Fin 5) (j : Fin 4) :
    LabelsBelow (responseMatrix (actualA P) (clipB (actualB P)) second middle i j.castSucc)
      (P.b+3*P.g+1) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  cases second <;> cases middle <;> fin_cases i <;> fin_cases j <;>
    norm_num [responseMatrix,actualA,actualB,clipB,Fin.castSucc] <;>
    first | exact LabelsBelow.zero _ | exact LabelsBelow.complete (by omega)

private theorem bottomDelta_labels (P : Parameters) (second : Bool) (i : Fin 5) :
    LabelsBelow (bottomDelta P second i) (P.b+3*P.g+1) := by
  have hF : (F P second).matrix=responseMatrix (actualA P) (actualB P) second true :=
    responseMatrix_actual P second true
  have hH : (H P second).matrix=responseMatrix (actualA P) (actualB P) second false :=
    responseMatrix_actual P second false
  have he : bottomDelta P second i =
      (-1 : CompleteRing)^(i.val+4) *
        ((((F P second).matrix).submatrix i.succAbove (4 : Fin 5).succAbove).det -
          (((H P second).matrix).submatrix i.succAbove (4 : Fin 5).succAbove).det) := by
    unfold bottomDelta BetaDiagram.cofactor
    simp only [show (4 : Fin 5).val=4 from rfl]
    ring
  rw [he,hF,hH,bottom_minor_clip]
  apply LabelsBelow.mul
  · apply labels_pow
    simp [LabelsBelow]
  · apply LabelsBelow.sub
    · apply labels_det
      intro r c
      change LabelsBelow (responseMatrix (actualA P) (clipB (actualB P)) second true
        (i.succAbove r) ((4 : Fin 5).succAbove c)) _
      rw [show (4 : Fin 5)=Fin.last 4 by decide,Fin.succAbove_last]
      exact clipped_entry_labels P second true _ _
    · apply labels_det
      intro r c
      change LabelsBelow (responseMatrix (actualA P) (clipB (actualB P)) second false
        (i.succAbove r) ((4 : Fin 5).succAbove c)) _
      rw [show (4 : Fin 5)=Fin.last 4 by decide,Fin.succAbove_last]
      exact clipped_entry_labels P second false _ _

private theorem upLeader_signed (P : Parameters) (second : Bool) :
    upLeaderCofactor P second =
      (F P second).cofactor 0 2-(if second then 0 else (H P second).cofactor 0 2) := by
  cases second <;> norm_num [upLeaderCofactor,BetaDiagram.cofactor]

private theorem sumLeader_signed (P : Parameters) (second : Bool) :
    sumLeaderCofactor P second =
      (F P second).cofactor 0 1-(if second then (H P second).cofactor 0 2 else 0) := by
  cases second <;> norm_num [sumLeaderCofactor,BetaDiagram.cofactor]

private theorem third_cofactor_eq (P : Parameters) (second : Bool) :
    (F P second).cofactor 0 3=(H P second).cofactor 0 3 := by
  have hf := (remaining_response_cofactors P second).2.2 true
  have hh := (remaining_response_cofactors P second).2.2 false
  have hfc : (F P second).cofactor 0 3=mixedLeaderCofactor P second true := by
    norm_num [BetaDiagram.cofactor,mixedLeaderCofactor]
  have hhc : (H P second).cofactor 0 3=mixedLeaderCofactor P second false := by
    norm_num [BetaDiagram.cofactor,mixedLeaderCofactor]
  exact hfc.trans (hf.trans (hh.symm.trans hhc.symm))

private theorem corner_cofactor_eq (P : Parameters) (second : Bool) :
    (F P second).cofactor 0 4=(H P second).cofactor 0 4 :=
  sub_eq_zero.mp (bottomDelta_zero P second)

private noncomputable def topLower (P : Parameters) (second : Bool) (t : ℤ) : CompleteRing :=
  complete (P.b+P.g-(if second then P.q else 0)+t)*(F P second).cofactor 0 0 -
  complete (P.b+2*P.g-P.q+t)*(H P second).cofactor 0 0 -
  complete (P.b+2*P.g+t)*(H P second).cofactor 0 1

private noncomputable def bottomLower (P : Parameters) (second : Bool) (t : ℤ) : CompleteRing :=
  complete (P.b+2*P.g+t)*bottomDelta P second 2 +
  complete (P.b+P.g+t)*bottomDelta P second 3 +
  complete (P.b+t)*bottomDelta P second 4

private theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    (∑ i, f i)=f 0+(f 1+(f 2+(f 3+f 4))) := by
  norm_num [Fin.sum_univ_succ]

private theorem up_normal_form (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t) :
    ((F P second).extendTop t ht).schur-((H P second).extendTop t ht).schur =
      complete (P.b+3*P.g+t)*upLeaderCofactor P second +
        complete (P.b+3*P.g-P.q+t)*sumLeaderCofactor P second + topLower P second t := by
  rw [top_schur_sum,top_schur_sum,upLeader_signed,sumLeader_signed]
  rw [sum_fin_five,sum_fin_five]
  simp_rw [F_top_labels,H_top_labels]
  rw [third_cofactor_eq,corner_cofactor_eq]
  cases second <;> norm_num [Matrix.cons_val,topLower] <;> ring

private theorem bottom_difference_sum (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t) :
    ((F P second).extendBottom t ht).schur-((H P second).extendBottom t ht).schur =
      ∑ i : Fin 5, complete (P.b+(4-(i.val : ℤ))*P.g+t)*bottomDelta P second i := by
  rw [bottom_schur_sum,bottom_schur_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hrF : (F P second).row i=P.b+(4-(i.val : ℤ))*P.g := by
    fin_cases i <;> norm_num [F,rows] <;> ring
  have hrH : (H P second).row i=P.b+(4-(i.val : ℤ))*P.g := hrF
  have hcF : (F P second).col (Fin.last 4)=0 := by
    change fCols P second 4=0
    cases second <;> rfl
  have hcH : (H P second).col (Fin.last 4)=0 := by
    change hCols P second 4=0
    cases second <;> rfl
  change complete (_-_+t)*(F P second).cofactor i 4 -
    complete (_-_+t)*(H P second).cofactor i 4 = _
  rw [hrF,hrH,hcF,hcH]
  unfold bottomDelta
  ring

private theorem down_normal_form (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t) :
    ((F P second).extendBottom t ht).schur-((H P second).extendBottom t ht).schur =
      complete (P.b+3*P.g+t)*downLeaderCofactor P second+bottomLower P second t := by
  rw [bottom_difference_sum,sum_fin_five]
  rw [bottomDelta_zero,bottomDelta_one]
  norm_num [bottomLower] <;> ring

private theorem sum_normal_form (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t) :
    (((F P second).extendTop t ht).schur-((H P second).extendTop t ht).schur) +
      (((F P second).extendBottom t ht).schur-((H P second).extendBottom t ht).schur) =
      complete (P.b+3*P.g-P.q+t)*sumLeaderCofactor P second +
        topLower P second t+bottomLower P second t := by
  rw [up_normal_form,down_normal_form,upLeaderCofactor_eq,
    (remaining_response_cofactors P second).1]
  ring

private theorem topLower_labels (P : Parameters) (second : Bool) (t k : ℤ)
    (hfixed : P.b+3*P.g<k) (hmoving : P.b+2*P.g+t<k) :
    LabelsBelow (topLower P second t) k := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  unfold topLower
  apply LabelsBelow.sub
  · apply LabelsBelow.sub
    · apply LabelsBelow.mul
      · apply LabelsBelow.complete
        cases second <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
      · exact labels_mono (first_cofactor_labels P second true 0) (by omega)
    · exact (LabelsBelow.complete (by omega)).mul
        (labels_mono (first_cofactor_labels P second false 0) (by omega))
  · exact (LabelsBelow.complete (by omega)).mul
      (labels_mono (first_cofactor_labels P second false 1) (by omega))

private theorem bottomLower_labels (P : Parameters) (second : Bool) (t k : ℤ)
    (hfixed : P.b+3*P.g<k) (hmoving : P.b+2*P.g+t<k) :
    LabelsBelow (bottomLower P second t) k := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  unfold bottomLower
  apply LabelsBelow.add
  · apply LabelsBelow.add
    · exact (LabelsBelow.complete (by omega)).mul
        (labels_mono (bottomDelta_labels P second 2) (by omega))
    · exact (LabelsBelow.complete (by omega)).mul
        (labels_mono (bottomDelta_labels P second 3) (by omega))
  · exact (LabelsBelow.complete (by omega)).mul
      (labels_mono (bottomDelta_labels P second 4) (by omega))

private theorem sumLeader_labels (P : Parameters) (second : Bool) :
    LabelsBelow (sumLeaderCofactor P second) (P.b+3*P.g+1) := by
  rw [sumLeader_signed]
  apply LabelsBelow.sub
  · exact first_cofactor_labels P second true 1
  · cases second
    · exact LabelsBelow.zero _
    · exact first_cofactor_labels P true false 2

private theorem upLeader_labels (P : Parameters) (second : Bool) :
    LabelsBelow (upLeaderCofactor P second) (P.b+3*P.g+1) := by
  rw [upLeader_signed]
  apply LabelsBelow.sub
  · exact first_cofactor_labels P second true 2
  · cases second
    · exact first_cofactor_labels P false false 2
    · exact LabelsBelow.zero _

private theorem downLeader_labels (P : Parameters) (second : Bool) :
    LabelsBelow (downLeaderCofactor P second) (P.b+3*P.g+1) := by
  rw [← bottomDelta_one]
  exact bottomDelta_labels P second 1

set_option maxHeartbeats 0 in
theorem down_response_coefficient (P : Parameters) (second : Bool)
    (t : ℤ) (ht : 0 < t) :
    MvPolynomial.pderiv
      (positiveIndex (P.b+3*P.g+t) (by
        have := P.q_pos; have := P.q_le_b; have := P.b_lt_g; omega))
      (((F P second).extendBottom t ht).schur -
        ((H P second).extendBottom t ht).schur) =
      complete (P.b-P.q)*(if second then D2 P else D1 P) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  have hk : 0 < P.b+3*P.g+t := by omega
  have hc := derivative_zero_of_labels (P.b+3*P.g+t) hk
    (downLeaderCofactor P second) (labels_mono (downLeader_labels P second) (by omega))
  have hr := derivative_zero_of_labels (P.b+3*P.g+t) hk (bottomLower P second t)
    (bottomLower_labels P second t _ (by omega) (by omega))
  rw [down_normal_form,map_add,MvPolynomial.pderiv_mul,pderiv_complete_index,if_pos rfl,hc,hr]
  simpa using (remaining_response_cofactors P second).1

set_option maxHeartbeats 0 in
/-- Both mixed differences have the claimed actual highest-generator coefficient. -/
theorem mixed_response_coefficient (P : Parameters) (second middle : Bool)
    (t : ℤ) (ht : 0 < t) :
    MvPolynomial.pderiv
      (positiveIndex (P.b+4*P.g-P.q+t) (by
        have := P.q_pos; have := P.q_le_b; have := P.b_lt_g; omega))
      (((if middle then F P second else H P second).extendTop t ht).schur -
        ((if middle then H P second else F P second).extendBottom t ht).schur) =
      -K P second * W P := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  have hk : 0 < P.b+4*P.g-P.q+t := by omega
  have hf := top_private_coefficient (if middle then F P second else H P second)
    t ht (P.b+4*P.g-P.q+t) hk 3
    (by cases middle <;> simp [BetaDiagram.extendTop, F, H, rows, fCols, hCols] <;> omega)
    (by intro a b hab
        cases middle <;> cases second <;> fin_cases a <;> fin_cases b <;>
          norm_num [BetaDiagram.extendTop, F, H, rows, fCols, hCols] at * <;> omega)
  have hh := pderiv_schur_absent
    ((if middle then H P second else F P second).extendBottom t ht)
    (P.b+4*P.g-P.q+t) hk (by
      intro a b
      cases middle <;> cases second <;> fin_cases a <;> fin_cases b <;>
        norm_num [BetaDiagram.extendBottom, F, H, rows, fCols, hCols] <;> omega)
  rw [map_sub, hf, hh]
  have hs : (-1 : CompleteRing)^(3 : Fin 5).val = -1 := by norm_num
  rw [hs,neg_one_mul,sub_zero]
  change mixedLeaderCofactor P second middle = _
  exact (remaining_response_cofactors P second).2.2 middle

set_option maxHeartbeats 0 in
theorem sum_response_coefficient (P : Parameters) (second : Bool)
    (t : ℤ) (htq : P.q < t) :
    MvPolynomial.pderiv
      (positiveIndex (P.b+3*P.g-P.q+t) (by
        have := P.q_pos; have := P.q_le_b; have := P.b_lt_g; omega))
      ((((F P second).extendTop t (by have := P.q_pos; omega)).schur -
        ((H P second).extendTop t (by have := P.q_pos; omega)).schur) +
       (((F P second).extendBottom t (by have := P.q_pos; omega)).schur -
        ((H P second).extendBottom t (by have := P.q_pos; omega)).schur)) =
      complete P.b*(if second then D2 P else D1 P) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  have ht : 0 < t := by omega
  have hk : 0 < P.b+3*P.g-P.q+t := by omega
  have hc := derivative_zero_of_labels (P.b+3*P.g-P.q+t) hk
    (sumLeaderCofactor P second) (labels_mono (sumLeader_labels P second) (by omega))
  have hu := derivative_zero_of_labels (P.b+3*P.g-P.q+t) hk (topLower P second t)
    (topLower_labels P second t _ (by omega) (by omega))
  have hv := derivative_zero_of_labels (P.b+3*P.g-P.q+t) hk (bottomLower P second t)
    (bottomLower_labels P second t _ (by omega) (by omega))
  rw [sum_normal_form,map_add,map_add,MvPolynomial.pderiv_mul,pderiv_complete_index,
    if_pos rfl,hc,hu,hv]
  simpa using (remaining_response_cofactors P second).2.1

/-- Equal positive top extensions are excluded uniformly, not by a parameter census. -/
theorem top_response_ne_zero (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((F P second).extendTop t ht).schur ≠ ((H P second).extendTop t ht).schur := by
  intro he
  have hc := up_response_coefficient P second t ht
  rw [he, sub_self] at hc
  apply upLeaderCofactor_ne_zero P hp second
  rw [upLeaderCofactor_eq]
  exact hc.symm

theorem bottom_response_ne_zero (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((F P second).extendBottom t ht).schur ≠
      ((H P second).extendBottom t ht).schur := by
  intro he
  have hc := down_response_coefficient P second t ht
  rw [he, sub_self, map_zero] at hc
  apply (remaining_response_cofactors_ne_zero P hp second).1
  rw [(remaining_response_cofactors P second).1]
  exact hc.symm

theorem mixed_response_ne_zero (P : Parameters) (hp : P.q < P.b)
    (second middle : Bool) (t : ℤ) (ht : 0 < t) :
    ((if middle then F P second else H P second).extendTop t ht).schur ≠
      ((if middle then H P second else F P second).extendBottom t ht).schur := by
  intro he
  have hc := mixed_response_coefficient P second middle t ht
  rw [he, sub_self, map_zero] at hc
  apply (remaining_response_cofactors_ne_zero P hp second).2.2 middle
  rw [(remaining_response_cofactors P second).2.2 middle]
  exact hc.symm

theorem sum_response_ne_zero (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (t : ℤ) (htq : P.q < t) :
    ((((F P second).extendTop t (by have := P.q_pos; omega)).schur -
      ((H P second).extendTop t (by have := P.q_pos; omega)).schur) +
     (((F P second).extendBottom t (by have := P.q_pos; omega)).schur -
      ((H P second).extendBottom t (by have := P.q_pos; omega)).schur)) ≠ 0 := by
  intro he
  have hc := sum_response_coefficient P second t htq
  rw [he, map_zero] at hc
  apply (remaining_response_cofactors_ne_zero P hp second).2.1
  rw [(remaining_response_cofactors P second).2.1]
  exact hc.symm

/-- Rotation exchanges up and down responses and fixes their sum, with no convention change. -/
theorem rotated_response_transport (P : Parameters) (second : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((F P second).rotate.extendTop t ht).schur -
        ((H P second).rotate.extendTop t ht).schur =
      ((F P second).extendBottom t ht).schur -
        ((H P second).extendBottom t ht).schur ∧
    ((F P second).rotate.extendBottom t ht).schur -
        ((H P second).rotate.extendBottom t ht).schur =
      ((F P second).extendTop t ht).schur -
        ((H P second).extendTop t ht).schur := by
  constructor
  · rw [BetaDiagram.rotate_extendTop_schur,BetaDiagram.rotate_extendTop_schur]
  · rw [BetaDiagram.rotate_extendBottom_schur,BetaDiagram.rotate_extendBottom_schur]

theorem rotated_endpoint_separation (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (t : ℤ) (ht : 0 < t) :
    ((F P second).rotate.extendTop t ht).schur ≠
        ((H P second).rotate.extendTop t ht).schur ∧
    ((F P second).rotate.extendBottom t ht).schur ≠
        ((H P second).rotate.extendBottom t ht).schur := by
  simpa only [BetaDiagram.rotate_extendTop_schur, BetaDiagram.rotate_extendBottom_schur]
    using ⟨bottom_response_ne_zero P hp second t ht, top_response_ne_zero P hp second t ht⟩

inductive ResponseKind
  | up | down | sum | mixedFH | mixedHF
  deriving DecidableEq

noncomputable def responsePolynomial (P : Parameters) (second : Bool)
    (t : ℤ) (ht : 0 < t) : ResponseKind → CompleteRing
  | .up => ((F P second).extendTop t ht).schur - ((H P second).extendTop t ht).schur
  | .down => ((F P second).extendBottom t ht).schur - ((H P second).extendBottom t ht).schur
  | .sum => (((F P second).extendTop t ht).schur - ((H P second).extendTop t ht).schur) +
      (((F P second).extendBottom t ht).schur - ((H P second).extendBottom t ht).schur)
  | .mixedFH => ((F P second).extendTop t ht).schur - ((H P second).extendBottom t ht).schur
  | .mixedHF => ((H P second).extendTop t ht).schur - ((F P second).extendBottom t ht).schur

def responseLeader (P : Parameters) (t : ℤ) : ResponseKind → ℤ
  | .up | .down => P.b+3*P.g+t
  | .sum => P.b+3*P.g-P.q+t
  | .mixedFH | .mixedHF => P.b+4*P.g-P.q+t

noncomputable def responseCoefficient (P : Parameters) (second : Bool) :
    ResponseKind → CompleteRing
  | .up => -complete (P.b-P.q)*(if second then D2 P else D1 P)
  | .down => complete (P.b-P.q)*(if second then D2 P else D1 P)
  | .sum => complete P.b*(if second then D2 P else D1 P)
  | .mixedFH | .mixedHF => -K P second * W P


private theorem up_labels (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t) :
    LabelsBelow (((F P second).extendTop t ht).schur-((H P second).extendTop t ht).schur)
      (P.b+3*P.g+t+1) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  rw [up_normal_form]
  apply LabelsBelow.add
  · apply LabelsBelow.add
    · exact (LabelsBelow.complete (by omega)).mul
        (labels_mono (upLeader_labels P second) (by omega))
    · exact (LabelsBelow.complete (by omega)).mul
        (labels_mono (sumLeader_labels P second) (by omega))
  · exact topLower_labels P second t _ (by omega) (by omega)

private theorem down_labels (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t) :
    LabelsBelow (((F P second).extendBottom t ht).schur-((H P second).extendBottom t ht).schur)
      (P.b+3*P.g+t+1) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  rw [down_normal_form]
  exact ((LabelsBelow.complete (by omega)).mul
    (labels_mono (downLeader_labels P second) (by omega))).add
      (bottomLower_labels P second t _ (by omega) (by omega))

private theorem sum_labels (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t)
    (htq : P.q < t) :
    LabelsBelow
      ((((F P second).extendTop t ht).schur-((H P second).extendTop t ht).schur) +
        (((F P second).extendBottom t ht).schur-((H P second).extendBottom t ht).schur))
      (P.b+3*P.g-P.q+t+1) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  rw [sum_normal_form]
  exact (((LabelsBelow.complete (by omega)).mul
    (labels_mono (sumLeader_labels P second) (by omega))).add
      (topLower_labels P second t _ (by omega) (by omega))).add
        (bottomLower_labels P second t _ (by omega) (by omega))

private theorem endpoint_labels (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    LabelsBelow (D.endpointDifference t ht) (D.endpointKappa+t+1) := by
  rw [D.endpointDifference_split]
  exact ((LabelsBelow.complete (by omega)).mul
    (labels_mono (D.endpointCoefficient_labels t ht) (by omega))).add
      (labels_mono (D.endpointRemainder_labels t ht) (by omega))

private theorem actual_endpointKappa (P : Parameters) (second middle : Bool) :
    (if middle then F P second else H P second).endpointKappa = P.b+4*P.g-P.q := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  let D := if middle then F P second else H P second
  change max (D.row 1-D.col 4) (D.row 0-D.col 3)=_
  cases middle <;> cases second <;>
    norm_num [D,F,H,rows,fCols,hCols] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- No generator above the tabulated leader survives the literal determinant subtraction.
The sum requires precisely its stated stronger regime. -/
theorem response_labels_bound (P : Parameters) (second : Bool) (t : ℤ) (ht : 0 < t)
    (kind : ResponseKind) (hsum : kind = .sum → P.q < t) :
    LabelsBelow (responsePolynomial P second t ht kind) (responseLeader P t kind+1) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  cases kind
  · exact up_labels P second t ht
  · exact down_labels P second t ht
  · exact sum_labels P second t ht (hsum rfl)
  · have he : responsePolynomial P second t ht .mixedFH =
        (F P second).endpointDifference t ht+responsePolynomial P second t ht .down := by
      unfold responsePolynomial BetaDiagram.endpointDifference
      ring
    rw [he]
    apply LabelsBelow.add
    · have h := endpoint_labels (F P second) t ht
      have hk := actual_endpointKappa P second true
      change (F P second).endpointKappa=P.b+4*P.g-P.q at hk
      rw [hk] at h
      exact h
    · exact labels_mono (down_labels P second t ht) (by dsimp [responseLeader]; omega)
  · have he : responsePolynomial P second t ht .mixedHF =
        (H P second).endpointDifference t ht-responsePolynomial P second t ht .down := by
      unfold responsePolynomial BetaDiagram.endpointDifference
      ring
    rw [he]
    apply LabelsBelow.sub
    · have h := endpoint_labels (H P second) t ht
      have hk := actual_endpointKappa P second false
      change (H P second).endpointKappa=P.b+4*P.g-P.q at hk
      rw [hk] at h
      exact h
    · exact labels_mono (down_labels P second t ht) (by dsimp [responseLeader]; omega)

theorem response_coefficient_nonzero (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (kind : ResponseKind) : responseCoefficient P second kind ≠ 0 := by
  obtain ⟨hv,hc,hm⟩ := remaining_response_cofactors_ne_zero P hp second
  have hu := upLeaderCofactor_ne_zero P hp second
  rw [upLeaderCofactor_eq] at hu
  rw [(remaining_response_cofactors P second).1] at hv
  rw [(remaining_response_cofactors P second).2.1] at hc
  have hmix := hm true
  rw [(remaining_response_cofactors P second).2.2 true] at hmix
  cases kind <;> simp only [responseCoefficient] <;> assumption

/-- The full uniform response table on the actual beta polynomials. -/
theorem response_table (P : Parameters) (hp : P.q < P.b) (second : Bool)
    (t : ℤ) (ht : 0 < t) (kind : ResponseKind)
    (hsum : kind = .sum → P.q < t) :
    ∃ hk : 0 < responseLeader P t kind,
      MvPolynomial.pderiv (positiveIndex (responseLeader P t kind) hk)
        (responsePolynomial P second t ht kind) = responseCoefficient P second kind ∧
      responseCoefficient P second kind ≠ 0 ∧
      LabelsBelow (responsePolynomial P second t ht kind) (responseLeader P t kind+1) := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  have hk : 0 < responseLeader P t kind := by cases kind <;> simp [responseLeader] <;> omega
  refine ⟨hk, ?_, response_coefficient_nonzero P hp second kind,
    response_labels_bound P second t ht kind hsum⟩
  cases kind
  · simpa [responsePolynomial, responseLeader, responseCoefficient, map_sub] using
      up_response_coefficient P second t ht
  · exact down_response_coefficient P second t ht
  · exact sum_response_coefficient P second t (hsum rfl)
  · exact mixed_response_coefficient P second true t ht
  · exact mixed_response_coefficient P second false t ht

/-- The four actual core candidates, parameterized without a classifier certificate. -/
def coreCandidate (P : Parameters) (second middle rotated : Bool) : BetaDiagram 5 :=
  let D := if middle then F P second else H P second
  if rotated then D.rotate else D

theorem coreCandidate_connected (P : Parameters) (second middle rotated : Bool) :
    (coreCandidate P second middle rotated).Connected := by
  cases rotated <;> cases middle
  · exact H_connected P second
  · exact F_connected P second
  · exact (H P second).rotate_connected (H_connected P second)
  · exact (F P second).rotate_connected (F_connected P second)

theorem coreCandidate_zeroFree (P : Parameters) (hp : P.q < P.b)
    (second middle rotated : Bool) : (coreCandidate P second middle rotated).ZeroFree := by
  have hq := P.q_pos
  have hg := P.b_lt_g
  intro i j he
  cases rotated <;> cases middle <;> cases second <;> fin_cases i <;> fin_cases j <;>
    norm_num [coreCandidate, BetaDiagram.rotate, F, H, rows, fCols, hCols, Fin.rev] at he <;>
    omega

theorem coreCandidate_endpointLeader (P : Parameters) (hp : P.q < P.b)
    (second middle rotated : Bool) : (coreCandidate P second middle rotated).EndpointLeader := by
  let D := coreCandidate P second middle rotated
  apply D.endpointLeader_of_endpointCoefficient_ne_zero
  apply D.endpointCoefficient_ne_zero_untied
    (D.positiveCorner_of_connected_zeroFree
      (coreCandidate_connected P second middle rotated)
      (coreCandidate_zeroFree P hp second middle rotated))
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  change D.row (0 : Fin 5)-D.row 1 ≠ D.col 3-D.col 4
  cases rotated <;> cases middle <;> cases second <;>
    norm_num [D, coreCandidate, BetaDiagram.topMargin, BetaDiagram.bottomMargin,
      BetaDiagram.rotate, F, H, rows, fCols, hCols, Fin.rev] <;> omega

/-- Differentiation with respect to a positive signed complete-generator index. -/
noncomputable def labelDerivative (k : ℤ) (hk : 0 < k) :
    CompleteRing →ₗ[ℚ] CompleteRing :=
  (MvPolynomial.pderiv (positiveIndex k hk)).toLinearMap

theorem labelDerivative_complete (k : ℤ) (hk : 0 < k) (l : ℤ) :
    labelDerivative k hk (complete l) = if l = k then 1 else 0 :=
  pderiv_complete_index k hk l

theorem labelDerivative_mul (k : ℤ) (hk : 0 < k) (p q : CompleteRing) :
    labelDerivative k hk (p*q) =
      labelDerivative k hk p*q + p*labelDerivative k hk q :=
  MvPolynomial.pderiv_mul

theorem labelDerivative_of_labelsBelow (k : ℤ) (hk : 0 < k)
    (p : CompleteRing) (hp : LabelsBelow p k) : labelDerivative k hk p = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  apply hp.not_mem
  simp [positiveIndex, Int.toNat_of_nonneg hk.le]

theorem labelDerivative_response (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (t : ℤ) (ht : 0 < t) (kind : ResponseKind)
    (hsum : kind = .sum → P.q < t) (hk : 0 < responseLeader P t kind) :
    labelDerivative (responseLeader P t kind) hk (responsePolynomial P second t ht kind) =
      responseCoefficient P second kind :=
  (response_table P hp second t ht kind hsum).choose_spec.1

theorem labelDerivative_response_above (P : Parameters) (second : Bool)
    (t : ℤ) (ht : 0 < t) (kind : ResponseKind)
    (hsum : kind = .sum → P.q < t) (k : ℤ) (hk : 0 < k)
    (hhigh : responseLeader P t kind < k) :
    labelDerivative k hk (responsePolynomial P second t ht kind) = 0 := by
  apply labelDerivative_of_labelsBelow k hk
  intro v hv
  have h := response_labels_bound P second t ht kind hsum v hv
  omega

private theorem coreCandidate_schur (P : Parameters) (second middle rotated : Bool) :
    (coreCandidate P second middle rotated).schur =
      (if middle then F P second else H P second).schur := by
  cases rotated
  · rfl
  · exact (if middle then F P second else H P second).rotate_schur

private theorem rotate_top_five (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    (D.rotate.extendTop t ht).schur=(D.extendBottom t ht).schur :=
  BetaDiagram.rotate_extendTop_schur (n := 4) D t ht

private theorem rotate_bottom_five (D : BetaDiagram 5) (t : ℤ) (ht : 0 < t) :
    (D.rotate.extendBottom t ht).schur=(D.extendTop t ht).schur :=
  BetaDiagram.rotate_extendBottom_schur (n := 4) D t ht

private def endpointChoice {α : Type*} (a b c d : α) (middle rotated : Bool) : α :=
  if middle then (if rotated then b else a) else (if rotated then d else c)

private theorem endpoint_choice_separation {α : Type*} {a b c d : α}
    {mf rf mr rr : Bool} (hne : (mf,rf)≠(mr,rr))
    (hab : a≠b) (hcd : c≠d) (hac : a≠c) (hbd : b≠d) (had : a≠d) (hcb : c≠b) :
    endpointChoice a b c d mf rf ≠ endpointChoice a b c d mr rr ∧
      endpointChoice a b c d mf (!rf) ≠ endpointChoice a b c d mr (!rr) := by
  cases mf <;> cases rf <;> cases mr <;> cases rr <;>
    simp only [endpointChoice,Bool.false_eq_true,↓reduceIte] <;> first
      | exact False.elim (hne rfl)
      | (constructor <;> first
          | assumption
          | exact Ne.symm hab
          | exact Ne.symm hcd
          | exact Ne.symm hac
          | exact Ne.symm hbd
          | exact Ne.symm had
          | exact Ne.symm hcb)

private theorem diagram_top_choice (D E : BetaDiagram 5) (middle rotated : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((if rotated then (if middle then D else E).rotate else (if middle then D else E)).extendTop t ht).schur =
      endpointChoice (D.extendTop t ht).schur (D.extendBottom t ht).schur
        (E.extendTop t ht).schur (E.extendBottom t ht).schur middle rotated := by
  cases middle <;> cases rotated
  · simp only [endpointChoice,Bool.false_eq_true,↓reduceIte]
  · exact rotate_top_five E t ht
  · simp only [endpointChoice,Bool.false_eq_true,↓reduceIte]
  · exact rotate_top_five D t ht

private theorem diagram_bottom_choice (D E : BetaDiagram 5) (middle rotated : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((if rotated then (if middle then D else E).rotate else (if middle then D else E)).extendBottom t ht).schur =
      endpointChoice (D.extendTop t ht).schur (D.extendBottom t ht).schur
        (E.extendTop t ht).schur (E.extendBottom t ht).schur middle (!rotated) := by
  cases middle <;> cases rotated
  · simp only [endpointChoice,Bool.not_false,Bool.false_eq_true,↓reduceIte]
  · exact rotate_bottom_five E t ht
  · simp only [endpointChoice,Bool.not_false,Bool.false_eq_true,↓reduceIte]
  · exact rotate_bottom_five D t ht

private theorem candidate_top_choice (P : Parameters) (second middle rotated : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((coreCandidate P second middle rotated).extendTop t ht).schur =
      endpointChoice ((F P second).extendTop t ht).schur
        ((F P second).extendBottom t ht).schur ((H P second).extendTop t ht).schur
        ((H P second).extendBottom t ht).schur middle rotated := by
  unfold coreCandidate
  exact diagram_top_choice (F P second) (H P second) middle rotated t ht

private theorem candidate_bottom_choice (P : Parameters) (second middle rotated : Bool)
    (t : ℤ) (ht : 0 < t) :
    ((coreCandidate P second middle rotated).extendBottom t ht).schur =
      endpointChoice ((F P second).extendTop t ht).schur
        ((F P second).extendBottom t ht).schur ((H P second).extendTop t ht).schur
        ((H P second).extendBottom t ht).schur middle (!rotated) := by
  unfold coreCandidate
  exact diagram_bottom_choice (F P second) (H P second) middle rotated t ht

private theorem coreCandidate_to_F (P : Parameters) (second middle rotated : Bool) :
    (coreCandidate P second middle rotated).schur=(F P second).schur := by
  have h := coreCandidate_schur P second middle rotated
  cases middle
  · change (coreCandidate P second false rotated).schur=(H P second).schur at h
    exact h.trans (F_schur_eq_H P second).symm
  · exact h

theorem coreCandidate_schur_eq (P : Parameters) (second mf rf mr rr : Bool) :
    (coreCandidate P second mf rf).schur = (coreCandidate P second mr rr).schur := by
  exact (coreCandidate_to_F P second mf rf).trans (coreCandidate_to_F P second mr rr).symm

theorem coreCandidate_span (P : Parameters) (second middle rotated : Bool) :
    (coreCandidate P second middle rotated).largestLabel = P.b+4*P.g := by
  cases middle <;> cases rotated <;> cases second <;>
    norm_num [coreCandidate, BetaDiagram.largestLabel, BetaDiagram.rotate,
      F, H, rows, fCols, hCols, Fin.rev] <;> omega

theorem coreCandidate_top_ne_bottom (P : Parameters) (hp : P.q < P.b)
    (second middle rotated : Bool) (t : ℤ) (ht : 0 < t) :
    ((coreCandidate P second middle rotated).extendTop t ht).schur ≠
      ((coreCandidate P second middle rotated).extendBottom t ht).schur := by
  have h := BetaDiagram.EndpointLeader.difference_ne_zero _
    (coreCandidate_endpointLeader P hp second middle rotated) t ht
  exact sub_ne_zero.mp h

private theorem ne_transport {α : Type*} {a b c d : α}
    (ha : a=c) (hb : b=d) (h : c≠d) : a≠b :=
  fun he => h (ha.symm.trans (he.trans hb))

set_option maxHeartbeats 0 in
/-- All six unordered exceptional core pairs have distinct positive top and bottom responses. -/
theorem coreCandidate_endpoint_separation (P : Parameters) (hp : P.q < P.b)
    (second mf rf mr rr : Bool) (hne : (mf,rf) ≠ (mr,rr))
    (t : ℤ) (ht : 0 < t) :
    ((coreCandidate P second mf rf).extendTop t ht).schur ≠
        ((coreCandidate P second mr rr).extendTop t ht).schur ∧
    ((coreCandidate P second mf rf).extendBottom t ht).schur ≠
        ((coreCandidate P second mr rr).extendBottom t ht).schur := by
  have hf : ((F P second).extendTop t ht).schur ≠ ((F P second).extendBottom t ht).schur :=
    coreCandidate_top_ne_bottom P hp second true false t ht
  have hh : ((H P second).extendTop t ht).schur ≠ ((H P second).extendBottom t ht).schur :=
    coreCandidate_top_ne_bottom P hp second false false t ht
  have hu := top_response_ne_zero P hp second t ht
  have hv := bottom_response_ne_zero P hp second t ht
  have hm1 := mixed_response_ne_zero P hp second true t ht
  have hm2 := mixed_response_ne_zero P hp second false t ht
  have hchoices := endpoint_choice_separation hne hf hh hu hv hm1 hm2
  exact ⟨ne_transport (candidate_top_choice P second mf rf t ht)
      (candidate_top_choice P second mr rr t ht) hchoices.1,
    ne_transport (candidate_bottom_choice P second mf rf t ht)
      (candidate_bottom_choice P second mr rr t ht) hchoices.2⟩

theorem response_double_top_ne_zero (P : Parameters) (hp : P.q < P.b)
    (second : Bool) (kind : ResponseKind) (s u A : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hA : s < A)
    (hsum : kind = .sum → P.q < A) :
    complete (s+u)*responsePolynomial P second A (by omega) kind -
      complete s*responsePolynomial P second (A+u) (by omega) kind ≠ 0 := by
  have hq := P.q_pos
  have hqb := P.q_le_b
  have hg := P.b_lt_g
  let k := responseLeader P (A+u) kind
  have hk : 0 < k := by cases kind <;> dsimp [k,responseLeader] <;> omega
  have hsu : s+u < k := by cases kind <;> dsimp [k,responseLeader] <;> omega
  have hsk : s < k := by omega
  have hhigh : responseLeader P A kind < k := by cases kind <;> dsimp [k,responseLeader] <;> omega
  have hd0 := labelDerivative_response_above P second A (by omega) kind hsum k hk hhigh
  have hd1 := labelDerivative_response P hp second (A+u) (by omega) kind
    (by intro h; have := hsum h; omega) hk
  have hx0 : labelDerivative k hk (complete (s+u)) = 0 := by
    rw [labelDerivative_complete, if_neg (by omega)]
  have hx1 : labelDerivative k hk (complete s) = 0 := by
    rw [labelDerivative_complete, if_neg (by omega)]
  intro hz
  have hd := congrArg (labelDerivative k hk) hz
  rw [map_sub, labelDerivative_mul, labelDerivative_mul, hx0, hx1, hd0, hd1, map_zero] at hd
  have hn := mul_ne_zero ((complete_ne_zero_iff s).2 (by omega))
    (response_coefficient_nonzero P hp second kind)
  apply hn
  simpa using hd

end SkewJacobiNegative.FiveExceptional
