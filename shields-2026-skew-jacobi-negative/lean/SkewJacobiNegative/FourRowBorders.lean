/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.LowNegativePatterns
import SkewJacobiNegative.LowNegativeShapeDichotomy

-- Complete-ring and normalized-profile instances use semireducible aliases.
set_option backward.isDefEq.respectTransparency false

/-!
# Exceptional four-row endpoint separators

The actual endpoint expansions and private-generator separator used in
`lem:four-border` and `eq:four-border-separator` of
`shields-2026-skew-jacobi-negative.tex`.  The parameters satisfy
`1 ≤ c < w` and `c + w < b`; all interval identities retain coincident
nonprivate labels.
-/

namespace SkewJacobiNegative
namespace FourRowBorders
open Gluing HessenbergExpansion FourRowHessenberg

/-- Increasing the first actual row gives the same four-row interval
expansion with only its first row length increased. -/
theorem top_extension_interval (P : Profile 3) (hP : P.Hessenberg)
    (t : ℤ) (ht : 0 < t) :
    (P.toBetaDiagram.extendTop t ht).schur =
      fourInterval complete ((P.r 0 : ℤ) + t) (P.r 1) (P.r 2) (P.r 3)
        (P.g 0) (P.g 1) (P.g 2) := by
  have hdom := P.four_domain hP
  have hdom' : FourDomain ((P.r 0 : ℤ) + t) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2) := by
    unfold FourDomain at *
    omega
  have hm : (P.toBetaDiagram.extendTop t ht).matrix =
      (fourIndices ((P.r 0 : ℤ) + t) (P.r 1) (P.r 2) (P.r 3)
        (P.g 0) (P.g 1) (P.g 2)).map complete := by
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M i j) P.indices_four
    change complete ((if i = 0 then P.xi i + t else P.xi i) - P.zeta j) = _
    congr 1
    fin_cases i <;> fin_cases j <;> simp [fourIndices] at hh ⊢ <;> omega
  rw [BetaDiagram.schur, hm]
  exact four_indices_det complete (fun _ hk => complete_of_neg hk) hdom'

/-- Decreasing the last actual column increases only the final row length. -/
theorem bottom_extension_interval (P : Profile 3) (hP : P.Hessenberg)
    (t : ℤ) (ht : 0 < t) :
    (P.toBetaDiagram.extendBottom t ht).schur =
      fourInterval complete (P.r 0) (P.r 1) (P.r 2) ((P.r 3 : ℤ) + t)
        (P.g 0) (P.g 1) (P.g 2) := by
  have hdom := P.four_domain hP
  have hdom' : FourDomain (P.r 0) (P.r 1) (P.r 2) ((P.r 3 : ℤ) + t)
      (P.g 0) (P.g 1) (P.g 2) := by
    unfold FourDomain at *
    omega
  have hm : (P.toBetaDiagram.extendBottom t ht).matrix =
      (fourIndices (P.r 0) (P.r 1) (P.r 2) ((P.r 3 : ℤ) + t)
        (P.g 0) (P.g 1) (P.g 2)).map complete := by
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M i j) P.indices_four
    change complete (P.xi i - (if j = Fin.last 3 then P.zeta j - t else P.zeta j)) = _
    congr 1
    fin_cases i <;> fin_cases j <;> simp [fourIndices] at hh ⊢ <;> omega
  rw [BetaDiagram.schur, hm]
  exact four_indices_det complete (fun _ hk => complete_of_neg hk) hdom'

/-- Differentiation at an independent positive complete generator, including
all zero and negative input indices. -/
theorem deriv_complete (v : ℕ+) (k : ℤ) :
    MvPolynomial.pderiv v (complete k) =
      if k = (v.val : ℤ) then (1 : CompleteRing) else 0 := by
  classical
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hne : k ≠ (v.val : ℤ) := by have := v.pos; omega
    simp [complete_of_neg hk, hne]
  · have hne : (0 : ℤ) ≠ (v.val : ℤ) := by have := v.pos; omega
    simp [hne]
  · let a : ℕ+ := ⟨k.toNat, by omega⟩
    have he : a = v ↔ k = (v.val : ℤ) := by
      constructor
      · intro h
        have hh := congrArg Subtype.val h
        change k.toNat = v.val at hh
        omega
      · intro h
        apply Subtype.ext
        change k.toNat = v.val
        omega
    rw [complete_of_pos hk]
    change MvPolynomial.pderiv v (MvPolynomial.X a : CompleteRing) = _
    by_cases hkv : k = (v.val : ℤ)
    · have hav := he.mpr hkv
      simp [MvPolynomial.pderiv_X, Pi.single_apply, hav, hkv]
    · have hav : a ≠ v := fun h => hkv (he.mp h)
      have hva : v ≠ a := Ne.symm hav
      simp [MvPolynomial.pderiv_X, Pi.single_apply, hav, hva, hkv]

/-- The symbolic endpoint sum has the private `T = 3b - 2c` coefficient.
Every derivative here is of an actual complete-ring polynomial. -/
theorem endpoint_interval_separator (w b c : ℤ) (hc : 0 < c)
    (hcw : c < w) (hb : c + w < b) :
    let t := b - c
    let d := w - c
    let T : ℕ+ := ⟨(3 * b - 2 * c).toNat, by omega⟩
    MvPolynomial.pderiv T
      (fourInterval complete (w + t) b b (b + d) c c w +
       fourInterval complete w b b (b + d + t) c c w -
       fourInterval complete (w + t) b (b + d) b c w c -
       fourInterval complete w b (b + d) (b + t) c w c) =
      complete w * (complete c * complete (b + d) - complete w * complete b) := by
  classical
  dsimp only
  let T : ℕ+ := ⟨(3 * b - 2 * c).toNat, by omega⟩
  have hTval : (T.val : ℤ) = 3 * b - 2 * c := by
    change ((3 * b - 2 * c).toNat : ℤ) = 3 * b - 2 * c
    omega
  change MvPolynomial.pderiv T _ = _
  simp (disch := omega) only [fourInterval, map_add, map_sub, MvPolynomial.pderiv_mul,
    deriv_complete, hTval, ite_eq_left, ite_eq_right, zero_mul, mul_zero, add_zero, zero_add,
    sub_zero, zero_sub, one_mul, mul_one]
  have hlabel : w + (b - c) = b + (w - c) := by omega
  rw [hlabel]
  have hmerge : w + b - c = b + (w - c) := by omega
  rw [hmerge]
  ring

/-- The two-term coefficient is nonzero because its unordered generator
pairs cannot match in the strict exceptional parameter domain. -/
theorem separator_ne_zero (w b c : ℤ) (hc : 0 < c)
    (hcw : c < w) (hb : c + w < b) :
    complete w * (complete c * complete (b + (w - c)) - complete w * complete b) ≠ 0 := by
  apply mul_ne_zero
  · exact (complete_ne_zero_iff w).mpr (by omega)
  · intro he
    have hp : complete c * complete (b + (w - c)) = complete w * complete b :=
      sub_eq_zero.mp he
    rcases complete_two_product_reading hc (by omega) (by omega) (by omega) hp with
      ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega

/-- The tied endpoint sums of the actual exceptional children are distinct,
with `c ≥ 1`, so no unit was silently dropped in obtaining the separator. -/
theorem exceptional_endpoint_sums_ne (w b c : ℕ) (hc : 1 ≤ c)
    (hcw : c < w) (hb : c + w < b) :
    let t : ℤ := (b : ℤ) - c
    let ht : 0 < t := by omega
    ((familyF w b c hcw hb).toBetaDiagram.extendTop t ht).schur +
      ((familyF w b c hcw hb).toBetaDiagram.extendBottom t ht).schur ≠
    ((familyH w b c hcw hb).toBetaDiagram.extendTop t ht).schur +
      ((familyH w b c hcw hb).toBetaDiagram.extendBottom t ht).schur := by
  dsimp only
  intro he
  rw [top_extension_interval _ (familyF_hessenberg w b c hcw hb),
    bottom_extension_interval _ (familyF_hessenberg w b c hcw hb),
    top_extension_interval _ (familyH_hessenberg w b c hcw hb),
    bottom_extension_interval _ (familyH_hessenberg w b c hcw hb)] at he
  have hsub : ((b + w - c : ℕ) : ℤ) = (b : ℤ) + w - c := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
  simp only [familyF, familyH, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, hsub] at he
  have harg : (b : ℤ) + w - c = (b : ℤ) + (w - c) := by omega
  rw [harg] at he
  let T : ℕ+ := ⟨(3 * (b : ℤ) - 2 * c).toNat, by omega⟩
  have hz : MvPolynomial.pderiv T
      (fourInterval complete ((w : ℤ) + ((b : ℤ) - c)) b b ((b : ℤ) + (w - c)) c c w +
       fourInterval complete w b b ((b : ℤ) + (w - c) + ((b : ℤ) - c)) c c w -
       fourInterval complete ((w : ℤ) + ((b : ℤ) - c)) b ((b : ℤ) + (w - c)) b c w c -
       fourInterval complete w b ((b : ℤ) + (w - c)) ((b : ℤ) + ((b : ℤ) - c)) c w c) = 0 := by
    have hdiff :
        fourInterval complete ((w : ℤ) + ((b : ℤ) - c)) b b ((b : ℤ) + (w - c)) c c w +
        fourInterval complete w b b ((b : ℤ) + (w - c) + ((b : ℤ) - c)) c c w -
        fourInterval complete ((w : ℤ) + ((b : ℤ) - c)) b ((b : ℤ) + (w - c)) b c w c -
        fourInterval complete w b ((b : ℤ) + (w - c)) ((b : ℤ) + ((b : ℤ) - c)) c w c = 0 := by
      linear_combination he
    simpa only [map_zero] using congrArg (MvPolynomial.pderiv T) hdiff
  rw [endpoint_interval_separator (w : ℤ) b c (by omega) (by omega) (by omega)] at hz
  exact separator_ne_zero (w : ℤ) b c (by omega) (by omega) (by omega) hz


set_option backward.isDefEq.respectTransparency false in
/-- The first derivative at the two actual exterior occurrences is the sum
of their signed full complementary minors, with the shared square term retained. -/
theorem pderiv_det_exterior_pair {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) CompleteRing) (v : ℕ+)
    (ht : M 0 (Fin.last n).castSucc = MvPolynomial.X v)
    (hb : M (0 : Fin (n + 1)).succ (Fin.last (n + 1)) = MvPolynomial.X v)
    (hprivate : ∀ a b,
      (a ≠ 0 ∨ b ≠ (Fin.last n).castSucc) →
      (a ≠ (0 : Fin (n + 1)).succ ∨ b ≠ Fin.last (n + 1)) →
      MvPolynomial.pderiv v (M a b) = 0) :
    MvPolynomial.pderiv v M.det =
      (-1) ^ n * ((M.submatrix Fin.succ (Fin.last n).castSucc.succAbove).det +
        (M.submatrix (0 : Fin (n + 1)).succ.succAbove Fin.castSucc).det) := by
  classical
  let B (j : Fin (n + 2)) := M.submatrix Fin.succ j.succAbove
  let U := M.submatrix (0 : Fin (n + 1)).succ.succAbove Fin.castSucc
  have hrow (j : Fin (n + 2)) (hj : j ≠ (Fin.last n).castSucc) :
      MvPolynomial.pderiv v (M 0 j) = 0 :=
    hprivate 0 j (Or.inr hj) (Or.inl (by simp))
  have hlast : MvPolynomial.pderiv v (B (Fin.last (n + 1))).det = 0 := by
    apply pderiv_det_eq_zero
    intro a b
    exact hprivate _ _ (Or.inl (Fin.succ_ne_zero a))
      (Or.inr (Fin.succAbove_ne _ _))
  have hminor (j : Fin (n + 1)) :
      MvPolynomial.pderiv v (B j.castSucc).det =
        (-1) ^ n * (U.submatrix Fin.succ j.succAbove).det := by
    have he : B j.castSucc 0 (Fin.last n) = MvPolynomial.X v := by
      have hl : j.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) :=
        Fin.succAbove_ne_last_last (Fin.castSucc_ne_last j)
      simpa only [B, Matrix.submatrix_apply, hl] using hb
    have hp : ∀ a b : Fin (n + 1), a ≠ 0 ∨ b ≠ Fin.last n →
        MvPolynomial.pderiv v (B j.castSucc a b) = 0 := by
      intro a b hab
      apply hprivate _ _ (Or.inl (Fin.succ_ne_zero a))
      rcases hab with ha | hb'
      · left
        intro hh
        exact ha (Fin.succ_injective _ hh)
      · right
        intro hh
        have hl : j.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) :=
          Fin.succAbove_ne_last_last (Fin.castSucc_ne_last j)
        exact hb' (Fin.succAbove_right_injective (hh.trans hl.symm))
    rw [pderiv_det_private_of_derivative_zero (B j.castSucc) v 0 (Fin.last n) he hp]
    have hm : (B j.castSucc).submatrix
        (0 : Fin (n + 1)).succAbove (Fin.last n).succAbove =
        U.submatrix Fin.succ j.succAbove := by
      ext a b
      simp [B, U, Matrix.submatrix_apply, Fin.castSucc_succAbove_castSucc]
    simp only [Fin.val_zero, Fin.val_last, zero_add, hm]
  have hsign (j : Fin (n + 2)) :
      MvPolynomial.pderiv v ((-1 : CompleteRing) ^ j.val) = 0 := by
    have he : (-1 : CompleteRing) ^ j.val = MvPolynomial.C ((-1 : ℚ) ^ j.val) := by simp
    rw [he]
    exact MvPolynomial.pderiv_C
  have htop :
      (∑ j : Fin (n + 2), (-1 : CompleteRing) ^ j.val *
        MvPolynomial.pderiv v (M 0 j) * (B j).det) =
      (-1) ^ n * (B (Fin.last n).castSucc).det := by
    rw [Finset.sum_eq_single (Fin.last n).castSucc]
    · simp [ht, MvPolynomial.pderiv_X_self]
    · intro j _ hj
      simp [hrow j hj]
    · simp
  have hbottom :
      (∑ j : Fin (n + 2), (-1 : CompleteRing) ^ j.val * M 0 j *
        MvPolynomial.pderiv v (B j).det) = (-1) ^ n * U.det := by
    rw [Fin.sum_univ_castSucc]
    simp only [hlast, mul_zero, add_zero, hminor, Fin.val_castSucc]
    rw [Matrix.det_succ_row_zero U, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hu : U 0 j = M 0 j.castSucc := by simp [U, Matrix.submatrix_apply]
    rw [hu]
    ring
  rw [Matrix.det_succ_row_zero M, map_sum]
  change (∑ j : Fin (n + 2),
    MvPolynomial.pderiv v ((-1) ^ j.val * M 0 j * (B j).det)) = _
  simp only [MvPolynomial.pderiv_mul, hsign, zero_mul, zero_add]
  have hexpand :
      (∑ j : Fin (n + 2),
        ((-1) ^ j.val * MvPolynomial.pderiv v (M 0 j) * (B j).det +
          (-1) ^ j.val * M 0 j * MvPolynomial.pderiv v (B j).det)) =
      (-1) ^ n * ((B (Fin.last n).castSucc).det + U.det) := by
    rw [Finset.sum_add_distrib, htop, hbottom]
    ring
  simpa only [mul_add, B, U] using hexpand

namespace BetaDiagram
open SkewJacobiNegative.BetaDiagram

/-- The full tied marker of an actual positive border is the sum of its actual
endpoint extensions.  This identity retains the shared quadratic term. -/
theorem positiveBorder_tied_first_derivative {n : ℕ} (D : BetaDiagram (n + 2))
    (q : ℤ) (hq : 0 < q) :
    let P := D.positiveBorder q q hq hq
    MvPolynomial.pderiv P.borderSecondGenerator P.schur =
      (-1) ^ (n + 1) * ((D.extendTop q hq).schur + (D.extendBottom q hq).schur) := by
  classical
  let P := D.positiveBorder q q hq hq
  have hgap : P.topMargin = P.bottomMargin := by simp [P]
  have hsecond : P.secondLabel = P.largestLabel - P.topMargin := by
    unfold SkewJacobiNegative.BetaDiagram.secondLabel
    rw [← hgap, min_self]
  have hindex : (⟨(P.largestLabel - P.topMargin).toNat,
      by have := P.exterior_top_label_pos; omega⟩ : ℕ+) = P.borderSecondGenerator := by
    apply Subtype.ext
    change (P.largestLabel - P.topMargin).toNat = P.secondLabel.toNat
    rw [hsecond]
  have hM : (P.borderSecondGenerator.val : ℤ) = P.largestLabel - P.topMargin := by
    rw [← hindex]
    change ((P.largestLabel - P.topMargin).toNat : ℤ) = P.largestLabel - P.topMargin
    have hp := P.exterior_top_label_pos
    omega
  have hb : P.matrix (0 : Fin (n + 2)).succ (Fin.last (n + 2)) =
      MvPolynomial.X P.borderSecondGenerator := by
    change complete (P.row (0 : Fin (n + 2)).succ - P.col (Fin.last (n + 2))) = _
    rw [P.exterior_candidate_labels.1, complete_of_pos P.exterior_top_label_pos, hindex]
  have ht : P.matrix 0 (Fin.last (n + 1)).castSucc =
      MvPolynomial.X P.borderSecondGenerator := by
    change complete (P.row 0 - P.col (Fin.last (n + 1)).castSucc) = _
    rw [P.exterior_candidate_labels.2, ← hgap,
      complete_of_pos P.exterior_top_label_pos, hindex]
  have hprivate : ∀ a b,
      (a ≠ 0 ∨ b ≠ (Fin.last (n + 1)).castSucc) →
      (a ≠ (0 : Fin (n + 2)).succ ∨ b ≠ Fin.last (n + 2)) →
      MvPolynomial.pderiv P.borderSecondGenerator (P.matrix a b) = 0 := by
    intro a b ha hb'
    change MvPolynomial.pderiv P.borderSecondGenerator (complete (P.row a - P.col b)) = 0
    rw [deriv_complete, hM]
    by_cases hc : a = 0 ∧ b = Fin.last (n + 2)
    · rcases hc with ⟨rfl, rfl⟩
      change (if P.largestLabel = P.largestLabel - P.topMargin then _ else _) = _
      rw [if_neg (by have := P.topMargin_pos; omega)]
    · have hh := P.tied_margin_private hgap a b (by tauto) ha hb'
      rw [if_neg (by omega)]
  let hP := D.positiveBorder_positiveCorner q q hq hq
  have htop :
      P.matrix.submatrix (0 : Fin (n + 2)).succ.succAbove Fin.castSucc =
      (D.extendTop q hq).matrix := by
    have hh := P.border_top_minor hP
    simpa only [Fin.succAbove_last, P, positiveBorder_cornerDiagram,
      positiveBorder_topMargin] using hh
  have hbottom :
      P.matrix.submatrix Fin.succ (Fin.last (n + 1)).castSucc.succAbove =
      (D.extendBottom q hq).matrix := by
    ext i j
    cases j using Fin.lastCases with
    | last =>
      simp [P, matrix, positiveBorder, extendBottom, Fin.succAbove_castSucc_self]
    | cast j =>
      have hj : j.castSucc.castSucc < (Fin.last (n + 1)).castSucc := by
        change j.val < n + 1
        exact j.isLt
      rw [Matrix.submatrix_apply, Fin.succAbove_of_castSucc_lt _ _ hj]
      simp [P, matrix, positiveBorder, extendBottom]
  have hh := pderiv_det_exterior_pair P.matrix P.borderSecondGenerator ht hb hprivate
  rw [htop, hbottom] at hh
  dsimp only
  simpa only [BetaDiagram.schur, add_comm] using hh

end BetaDiagram

/-- At the only equal-margin collision identified in the four-border row reading,
the actual five-row parent polynomials are different. -/
theorem exceptional_equal_margin_borders_ne (w b c : ℕ) (hc : 1 ≤ c)
    (hcw : c < w) (hb : c + w < b) :
    let t : ℤ := (b : ℤ) - c
    let ht : 0 < t := by omega
    ((familyF w b c hcw hb).toBetaDiagram.positiveBorder t t ht ht).schur ≠
      ((familyH w b c hcw hb).toBetaDiagram.positiveBorder t t ht ht).schur := by
  dsimp only
  let F := (familyF w b c hcw hb).toBetaDiagram
  let H := (familyH w b c hcw hb).toBetaDiagram
  let t : ℤ := (b : ℤ) - c
  have ht : 0 < t := by dsimp [t]; omega
  intro he
  have hspan : F.largestLabel = H.largestLabel := by
    apply F.largestLabel_eq_of_schur_eq H
      (Profile.toBetaDiagram_connected _) (Profile.toBetaDiagram_connected _)
    simpa only [F, H, Profile.toBetaDiagram_schur] using family_schur_eq w b c hcw hb
  have hg : (F.positiveBorder t t ht ht).borderSecondGenerator =
      (H.positiveBorder t t ht ht).borderSecondGenerator := by
    apply Subtype.ext
    simp only [SkewJacobiNegative.BetaDiagram.borderSecondGenerator,
      SkewJacobiNegative.BetaDiagram.secondLabel,
      SkewJacobiNegative.BetaDiagram.positiveBorder_largestLabel,
      SkewJacobiNegative.BetaDiagram.positiveBorder_topMargin,
      SkewJacobiNegative.BetaDiagram.positiveBorder_bottomMargin, min_self, hspan]
  have hd := congrArg
    (MvPolynomial.pderiv (F.positiveBorder t t ht ht).borderSecondGenerator) he
  rw [BetaDiagram.positiveBorder_tied_first_derivative F t ht] at hd
  rw [hg, BetaDiagram.positiveBorder_tied_first_derivative H t ht] at hd
  have hext : (F.extendTop t ht).schur + (F.extendBottom t ht).schur =
      (H.extendTop t ht).schur + (H.extendBottom t ht).schur := by
    simpa using hd
  exact exceptional_endpoint_sums_ne w b c hc hcw hb hext

/-- Rotating a genuine core exchanges its two positive border margins. -/
theorem positiveBorder_rotation_transport {n : ℕ} (D E : BetaDiagram (n + 1))
    (h : D.RotationEquivalent E) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    (D.positiveBorder u v hu hv).RotationEquivalent (E.positiveBorder v u hv hu) := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      have hh := hr 0
      rw [Fin.rev_zero] at hh
      simpa only [SkewJacobiNegative.BetaDiagram.positiveBorder_row_zero,
        Fin.rev_zero, SkewJacobiNegative.BetaDiagram.positiveBorder_col_last]
        using (show D.row 0 + u = c - (E.col (Fin.last n) - u) by omega)
    | succ i =>
      simpa only [SkewJacobiNegative.BetaDiagram.positiveBorder_row_succ,
        Fin.rev_succ, SkewJacobiNegative.BetaDiagram.positiveBorder_col_castSucc] using hr i
  · intro i
    cases i using Fin.lastCases with
    | last =>
      have hh := hc (Fin.last n)
      rw [Fin.rev_last] at hh
      simpa only [SkewJacobiNegative.BetaDiagram.positiveBorder_col_last,
        Fin.rev_last, SkewJacobiNegative.BetaDiagram.positiveBorder_row_zero]
        using (show D.col (Fin.last n) - v = c - (E.row 0 + v) by omega)
    | cast i =>
      simpa only [SkewJacobiNegative.BetaDiagram.positiveBorder_col_castSucc,
        Fin.rev_castSucc, SkewJacobiNegative.BetaDiagram.positiveBorder_row_succ] using hc i

/-- The natural profile's rotation is the actual beta half-turn with its
produced normalization constant. -/
theorem profile_rotation_equivalent {n : ℕ} (P : Profile n) :
    P.toBetaDiagram.RotationEquivalent P.rotate.toBetaDiagram := by
  refine ⟨P.xi 0, ?_, ?_⟩
  · intro i
    change P.xi i = P.xi 0 - P.rotate.zeta i.rev
    rw [Profile.zeta_rotate, Fin.rev_rev]
    ring
  · intro i
    change P.zeta i = P.xi 0 - P.rotate.xi i.rev
    rw [Profile.xi_rotate, Fin.rev_rev]
    ring

/-- Both orientations of a cofactor give the same equal-margin parent polynomial. -/
theorem equal_margin_border_rotate_schur {n : ℕ} (P : Profile n)
    (t : ℤ) (ht : 0 < t) :
    (P.toBetaDiagram.positiveBorder t t ht ht).schur =
      (P.rotate.toBetaDiagram.positiveBorder t t ht ht).schur := by
  let D := P.toBetaDiagram.positiveBorder t t ht ht
  let E := P.rotate.toBetaDiagram.positiveBorder t t ht ht
  have hR : D.RotationEquivalent E :=
    positiveBorder_rotation_transport _ _ (profile_rotation_equivalent P) t t ht ht
  have hT := (D.translation_rotate_iff_rotation E).mpr hR
  exact hT.schur_eq.trans E.rotate_schur

/-- The tied-margin separator excludes every orientation of both exceptional
cofactor orbits, not just the two displayed representatives. -/
theorem exceptional_equal_margin_both_orbits_ne (w b c : ℕ) (hc : 1 ≤ c)
    (hcw : c < w) (hb : c + w < b) (P Q : Profile 3)
    (hP : P = familyF w b c hcw hb ∨ P = (familyF w b c hcw hb).rotate)
    (hQ : Q = familyH w b c hcw hb ∨ Q = (familyH w b c hcw hb).rotate) :
    let t : ℤ := (b : ℤ) - c
    let ht : 0 < t := by omega
    (P.toBetaDiagram.positiveBorder t t ht ht).schur ≠
      (Q.toBetaDiagram.positiveBorder t t ht ht).schur := by
  dsimp only
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · exact exceptional_equal_margin_borders_ne w b c hc hcw hb
  · rw [← equal_margin_border_rotate_schur]
    exact exceptional_equal_margin_borders_ne w b c hc hcw hb
  · rw [← equal_margin_border_rotate_schur]
    exact exceptional_equal_margin_borders_ne w b c hc hcw hb
  · rw [← equal_margin_border_rotate_schur, ← equal_margin_border_rotate_schur]
    exact exceptional_equal_margin_borders_ne w b c hc hcw hb

/-- The literal top endpoint profile, without changing any overlap. -/
def topProfile (P : Profile 3) (a : ℕ) : Profile 3 where
  r i := if i = 0 then P.r i + a else P.r i
  g := P.g
  r_pos i := by have := P.r_pos i; split_ifs <;> omega
  g_lt_castSucc j := by have := P.g_lt_castSucc j; split_ifs <;> omega
  g_lt_succ j := by have := P.g_lt_succ j; split_ifs <;> omega

/-- The literal bottom endpoint profile, again with its original overlap word. -/
def bottomProfile (P : Profile 3) (a : ℕ) : Profile 3 where
  r i := if i = Fin.last 3 then P.r i + a else P.r i
  g := P.g
  r_pos i := by have := P.r_pos i; split_ifs <;> omega
  g_lt_castSucc j := by have := P.g_lt_castSucc j; split_ifs <;> omega
  g_lt_succ j := by have := P.g_lt_succ j; split_ifs <;> omega

theorem topProfile_hessenberg (P : Profile 3) (hP : P.Hessenberg) (a : ℕ) :
    (topProfile P a).Hessenberg := by
  rw [Profile.hessenberg_four_iff] at hP ⊢
  simpa [topProfile] using hP

theorem bottomProfile_hessenberg (P : Profile 3) (hP : P.Hessenberg) (a : ℕ) :
    (bottomProfile P a).Hessenberg := by
  rw [Profile.hessenberg_four_iff] at hP ⊢
  simpa [bottomProfile] using hP

/-- Identification with the actual top beta extension, not an abstract class representative. -/
theorem topProfile_schur (P : Profile 3) (hP : P.Hessenberg) (a : ℕ) (ha : 0 < a) :
    (topProfile P a).schur =
      (P.toBetaDiagram.extendTop (a : ℤ) (by omega)).schur := by
  rw [(topProfile P a).schur_four_interval (topProfile_hessenberg P hP a),
    top_extension_interval P hP]
  simp [topProfile, fourInterval, complete_eq_hh]

/-- Identification with the actual bottom beta extension. -/
theorem bottomProfile_schur (P : Profile 3) (hP : P.Hessenberg) (a : ℕ) (ha : 0 < a) :
    (bottomProfile P a).schur =
      (P.toBetaDiagram.extendBottom (a : ℤ) (by omega)).schur := by
  rw [(bottomProfile P a).schur_four_interval (bottomProfile_hessenberg P hP a),
    bottom_extension_interval P hP]
  simp [bottomProfile, fourInterval, complete_eq_hh]

/-- None of F's positive top extensions can itself be an exceptional family member. -/
theorem top_F_not_family (w b c a : ℕ) (hcw : c < w) (hb : c + w < b)
    (ha : 0 < a) (Q : Profile 3) :
    ¬ FamilyRelation (topProfile (familyF w b c hcw hb) a) Q := by
  rintro ⟨W, B, C, hCW, hB, hcase⟩
  have hrows (i : Fin 4) : w < (topProfile (familyF w b c hcw hb) a).r i := by
    fin_cases i <;> simp [topProfile, familyF] <;> omega
  rcases hcase with ⟨hsource, _⟩ | ⟨hsource, _⟩ <;>
    rcases hsource with he | he
  all_goals
    have hmax := congrArg (fun P : Profile 3 => max (P.g 0) (max (P.g 1) (P.g 2))) he
    simp [topProfile, familyF, familyH, Profile.rotate] at hmax
    have hw : w = W := by omega
    have hr0 := congrArg (fun P : Profile 3 => P.r 0) he
    have hr3 := congrArg (fun P : Profile 3 => P.r 3) he
    have hh0 := hrows 0
    have hh3 := hrows 3
    simp [topProfile, familyF, familyH, Profile.rotate] at hr0 hr3 hh0 hh3
    omega

/-- F's positive bottom extension cannot be exceptional either: its unchanged
two middle rows recover b, and its final row then forces the shift to vanish. -/
theorem bottom_F_not_family (w b c a : ℕ) (hcw : c < w) (hb : c + w < b)
    (ha : 0 < a) (Q : Profile 3) :
    ¬ FamilyRelation (bottomProfile (familyF w b c hcw hb) a) Q := by
  rintro ⟨W, B, C, hCW, hB, hcase⟩
  rcases hcase with ⟨hsource, _⟩ | ⟨hsource, _⟩ <;>
    rcases hsource with he | he
  all_goals
    have hg0 := congrArg (fun P : Profile 3 => P.g 0) he
    have hg1 := congrArg (fun P : Profile 3 => P.g 1) he
    have hg2 := congrArg (fun P : Profile 3 => P.g 2) he
    have hr1 := congrArg (fun P : Profile 3 => P.r 1) he
    have hr3 := congrArg (fun P : Profile 3 => P.r 3) he
    simp [bottomProfile, familyF, familyH, Profile.rotate] at hg0 hg1 hg2 hr1 hr3
    omega

/-- Any positive endpoint extension of F differs from either endpoint extension
of either orientation of H.  The mate classification is produced from full equality. -/
theorem exceptional_endpoint_pairs_ne (w b c a d : ℕ) (hcw : c < w)
    (hb : c + w < b) (ha : 0 < a) (hd : 0 < d)
    (P Q : Profile 3)
    (hP : P = topProfile (familyF w b c hcw hb) a ∨
      P = bottomProfile (familyF w b c hcw hb) a)
    (hQ : Q = topProfile (familyH w b c hcw hb) d ∨
      Q = bottomProfile (familyH w b c hcw hb) d ∨
      Q = topProfile (familyH w b c hcw hb).rotate d ∨
      Q = bottomProfile (familyH w b c hcw hb).rotate d) : P.schur ≠ Q.schur := by
  intro he
  have hPH : P.Hessenberg := by
    rcases hP with rfl | rfl
    · exact topProfile_hessenberg _ (familyF_hessenberg w b c hcw hb) a
    · exact bottomProfile_hessenberg _ (familyF_hessenberg w b c hcw hb) a
  have hQH : Q.Hessenberg := by
    rcases hQ with rfl | rfl | rfl | rfl
    · exact topProfile_hessenberg _ (familyH_hessenberg w b c hcw hb) d
    · exact bottomProfile_hessenberg _ (familyH_hessenberg w b c hcw hb) d
    · exact topProfile_hessenberg _
        ((familyH w b c hcw hb).hessenberg_rotate (familyH_hessenberg w b c hcw hb)) d
    · exact bottomProfile_hessenberg _
        ((familyH w b c hcw hb).hessenberg_rotate (familyH_hessenberg w b c hcw hb)) d
  rcases hessenberg_classification P Q hPH hQH he with heq | heq | hex
  · have hg := congrArg (fun T : Profile 3 => T.g 1) heq
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl | rfl | rfl <;>
      simp [topProfile, bottomProfile, familyF, familyH, Profile.rotate] at hg <;> omega
  · have hg := congrArg (fun T : Profile 3 => T.g 1) heq
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl | rfl | rfl <;>
      simp [topProfile, bottomProfile, familyF, familyH, Profile.rotate] at hg <;> omega
  · rcases hP with rfl | rfl
    · exact top_F_not_family w b c a hcw hb ha Q hex
    · exact bottom_F_not_family w b c a hcw hb ha Q hex

/-- Private strict-margin markers from F and from either orientation of H
cannot match, regardless of which endpoint the smaller margin selects. -/
theorem exceptional_actual_endpoints_ne (w b c : ℕ) (hcw : c < w)
    (hb : c + w < b) (Q : Profile 3)
    (hQ : Q = familyH w b c hcw hb ∨ Q = (familyH w b c hcw hb).rotate)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) (topF topQ : Bool) :
    (if topF then ((familyF w b c hcw hb).toBetaDiagram.extendTop u hu).schur
      else ((familyF w b c hcw hb).toBetaDiagram.extendBottom u hu).schur) ≠
    (if topQ then (Q.toBetaDiagram.extendTop v hv).schur
      else (Q.toBetaDiagram.extendBottom v hv).schur) := by
  have huc : (u.toNat : ℤ) = u := by omega
  have hvc : (v.toNat : ℤ) = v := by omega
  have hua : 0 < u.toNat := by omega
  have hva : 0 < v.toNat := by omega
  have hQH : Q.Hessenberg := by
    rcases hQ with rfl | rfl
    · exact familyH_hessenberg w b c hcw hb
    · exact (familyH w b c hcw hb).hessenberg_rotate (familyH_hessenberg w b c hcw hb)
  have hFt := topProfile_schur (familyF w b c hcw hb)
    (familyF_hessenberg w b c hcw hb) u.toNat hua
  have hFb := bottomProfile_schur (familyF w b c hcw hb)
    (familyF_hessenberg w b c hcw hb) u.toNat hua
  have hQt := topProfile_schur Q hQH v.toNat hva
  have hQb := bottomProfile_schur Q hQH v.toNat hva
  simp only [huc, hvc] at hFt hFb hQt hQb
  cases topF <;> cases topQ <;>
    simp only [Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true]
  all_goals
    intro he
    have hp := he
    first
      | rw [← hFb, ← hQb] at hp
      | rw [← hFb, ← hQt] at hp
      | rw [← hFt, ← hQb] at hp
      | rw [← hFt, ← hQt] at hp
    apply exceptional_endpoint_pairs_ne w b c u.toNat v.toNat hcw hb hua hva _ _
      (by first | exact Or.inl rfl | exact Or.inr rfl) _ hp
    rcases hQ with rfl | rfl
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))

/-- Connected children of the same actual span give common unordered margins
on Schur-equal parents.  No literal equality of the children is assumed. -/
theorem different_child_margins_recovered (D E : BetaDiagram 4)
    (hD : D.Connected) (hE : E.Connected) (hspan : D.largestLabel = E.largestLabel)
    (u v a b : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (he : (D.positiveBorder u v hu hv).schur = (E.positiveBorder a b ha hb).schur) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  let P := D.positiveBorder u v hu hv
  let Q := E.positiveBorder a b ha hb
  have hl := P.largestLabel_eq_of_schur_eq Q
    (D.positiveBorder_connected u v hu hv) (E.positiveBorder_connected a b ha hb) he
  have hm := P.border_minMargin_eq_of_schur_eq Q
    (D.positiveBorder_connected u v hu hv) (E.positiveBorder_connected a b ha hb)
    (D.positiveBorder_positiveCorner u v hu hv) (E.positiveBorder_positiveCorner a b ha hb)
    (by simpa only [P, SkewJacobiNegative.BetaDiagram.positiveBorder_cornerDiagram] using hD)
    (by simpa only [Q, SkewJacobiNegative.BetaDiagram.positiveBorder_cornerDiagram] using hE) he
  simp only [P, Q, SkewJacobiNegative.BetaDiagram.positiveBorder_largestLabel, hspan] at hl
  simp only [P, Q, SkewJacobiNegative.BetaDiagram.positiveBorder_topMargin,
    SkewJacobiNegative.BetaDiagram.positiveBorder_bottomMargin] at hm
  rcases le_total u v with huv | hvu <;> rcases le_total a b with hab | hba
  · rw [min_eq_left huv, min_eq_left hab] at hm
    exact Or.inl ⟨hm, by omega⟩
  · rw [min_eq_left huv, min_eq_right hba] at hm
    exact Or.inr ⟨hm, by omega⟩
  · rw [min_eq_right hvu, min_eq_left hab] at hm
    exact Or.inr ⟨by omega, hm⟩
  · rw [min_eq_right hvu, min_eq_right hba] at hm
    exact Or.inl ⟨by omega, hm⟩

/-- Strict margins on two equal actual parents identify the full selected
endpoint polynomials, not merely their highest-degree terms. -/
theorem different_child_strict_markers (D E : BetaDiagram 4)
    (hD : D.Connected) (hE : E.Connected)
    (u v a b : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (huv : u ≠ v) (hab : a ≠ b)
    (he : (D.positiveBorder u v hu hv).schur = (E.positiveBorder a b ha hb).schur) :
    (if u < v then (D.extendTop u hu).schur else (D.extendBottom v hv).schur) =
    (if a < b then (E.extendTop a ha).schur else (E.extendBottom b hb).schur) := by
  classical
  let P := D.positiveBorder u v hu hv
  let Q := E.positiveBorder a b ha hb
  have hl := P.largestLabel_eq_of_schur_eq Q
    (D.positiveBorder_connected u v hu hv) (E.positiveBorder_connected a b ha hb) he
  have hm := P.border_minMargin_eq_of_schur_eq Q
    (D.positiveBorder_connected u v hu hv) (E.positiveBorder_connected a b ha hb)
    (D.positiveBorder_positiveCorner u v hu hv) (E.positiveBorder_positiveCorner a b ha hb)
    (by simpa only [P, SkewJacobiNegative.BetaDiagram.positiveBorder_cornerDiagram] using hD)
    (by simpa only [Q, SkewJacobiNegative.BetaDiagram.positiveBorder_cornerDiagram] using hE) he
  have hn : P.borderLargestGenerator = Q.borderLargestGenerator := by
    apply Subtype.ext
    exact congrArg Int.toNat hl
  have hg : P.borderSecondGenerator = Q.borderSecondGenerator := by
    apply Subtype.ext
    apply congrArg Int.toNat
    unfold SkewJacobiNegative.BetaDiagram.secondLabel
    rw [hl, hm]
  have hsign : (-1 : CompleteRing) ^ 5 = -1 := by norm_num
  have hdc : MvPolynomial.pderiv P.borderSecondGenerator
      (eraseGenerator P.borderLargestGenerator P.schur) =
      -(if u < v then (D.extendTop u hu).schur else (D.extendBottom v hv).schur) := by
    by_cases h : u < v
    · simpa only [P, ite_eq_left h, hsign, neg_one_mul]
        using D.positiveBorder_top_coefficient u v hu hv h
    · have h' : v < u := by omega
      simpa only [P, ite_eq_right h, hsign, neg_one_mul]
        using D.positiveBorder_bottom_coefficient u v hu hv h'
  have hec : MvPolynomial.pderiv Q.borderSecondGenerator
      (eraseGenerator Q.borderLargestGenerator Q.schur) =
      -(if a < b then (E.extendTop a ha).schur else (E.extendBottom b hb).schur) := by
    by_cases h : a < b
    · simpa only [Q, ite_eq_left h, hsign, neg_one_mul]
        using E.positiveBorder_top_coefficient a b ha hb h
    · have h' : b < a := by omega
      simpa only [Q, ite_eq_right h, hsign, neg_one_mul]
        using E.positiveBorder_bottom_coefficient a b ha hb h'
  have hd := congrArg (fun p : CompleteRing =>
    MvPolynomial.pderiv P.borderSecondGenerator (eraseGenerator P.borderLargestGenerator p)) he
  rw [hdc, hn, hg, hec] at hd
  exact neg_injective hd

/-- Every unequal-margin border of F differs from every border of either
orientation of H.  Strict and tied margins cannot mix, by the produced margins. -/
theorem exceptional_unequal_margin_borders_ne (w b c : ℕ) (hcw : c < w)
    (hb : c + w < b) (Q : Profile 3)
    (hQ : Q = familyH w b c hcw hb ∨ Q = (familyH w b c hcw hb).rotate)
    (u v a d : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hd : 0 < d)
    (huv : u ≠ v) :
    ((familyF w b c hcw hb).toBetaDiagram.positiveBorder u v hu hv).schur ≠
      (Q.toBetaDiagram.positiveBorder a d ha hd).schur := by
  intro he
  let F := (familyF w b c hcw hb).toBetaDiagram
  have hcF : F.Connected := Profile.toBetaDiagram_connected _
  have hcQ : Q.toBetaDiagram.Connected := Profile.toBetaDiagram_connected _
  have hspan : F.largestLabel = Q.toBetaDiagram.largestLabel := by
    apply F.largestLabel_eq_of_schur_eq _ hcF hcQ
    rcases hQ with rfl | rfl <;>
      simpa only [F, Profile.toBetaDiagram_schur, Profile.schur_rotate] using
        family_schur_eq w b c hcw hb
  have hm := different_child_margins_recovered F Q.toBetaDiagram hcF hcQ hspan
    u v a d hu hv ha hd he
  have had : a ≠ d := by rcases hm with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
  have hmark := different_child_strict_markers F Q.toBetaDiagram hcF hcQ
    u v a d hu hv ha hd huv had he
  by_cases h0 : u < v <;> by_cases h1 : a < d
  · exact exceptional_actual_endpoints_ne w b c hcw hb Q hQ u a hu ha true true
      (by simpa only [F, ite_eq_left h0, ite_eq_left h1, Bool.false_eq_true,
        eq_self_iff_true, ite_true, ite_false] using hmark)
  · exact exceptional_actual_endpoints_ne w b c hcw hb Q hQ u d hu hd true false
      (by simpa only [F, ite_eq_left h0, ite_eq_right h1, Bool.false_eq_true,
        eq_self_iff_true, ite_true, ite_false] using hmark)
  · exact exceptional_actual_endpoints_ne w b c hcw hb Q hQ v a hv ha false true
      (by simpa only [F, ite_eq_right h0, ite_eq_left h1, Bool.false_eq_true,
        eq_self_iff_true, ite_true, ite_false] using hmark)
  · exact exceptional_actual_endpoints_ne w b c hcw hb Q hQ v d hv hd false false
      (by simpa only [F, ite_eq_right h0, ite_eq_right h1, Bool.false_eq_true,
        eq_self_iff_true, ite_true, ite_false] using hmark)

/-- The full ordered row word of a positive border, read from its actual beta lists. -/
theorem profile_border_row_lengths (P : Profile 3) (u v : ℤ)
    (hu : 0 < u) (hv : 0 < v) :
    (P.toBetaDiagram.positiveBorder u v hu hv).rowLength =
      ![(P.r 0 : ℤ) + u, (P.r 0 : ℤ) + P.r 1 - P.g 0,
        (P.r 1 : ℤ) + P.r 2 - P.g 1, (P.r 2 : ℤ) + P.r 3 - P.g 2,
        (P.r 3 : ℤ) + v] := by
  let B := P.toBetaDiagram.positiveBorder u v hu hv
  funext i
  fin_cases i
  · change B.row 0 - B.col (0 : Fin 4).castSucc = (P.r 0 : ℤ) + u
    rw [SkewJacobiNegative.BetaDiagram.positiveBorder_row_zero,
      SkewJacobiNegative.BetaDiagram.positiveBorder_col_castSucc]
    change P.xi 0 + u - P.zeta 0 = (P.r 0 : ℤ) + u
    have hi := P.xi_sub_zeta 0
    omega
  · change B.row (0 : Fin 4).succ - B.col (1 : Fin 4).castSucc =
      (P.r 0 : ℤ) + P.r 1 - P.g 0
    rw [SkewJacobiNegative.BetaDiagram.positiveBorder_row_succ,
      SkewJacobiNegative.BetaDiagram.positiveBorder_col_castSucc]
    have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M 0 1) P.indices_four
    simpa only [Profile.toBetaDiagram, fourIndices, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] using hi
  · change B.row (1 : Fin 4).succ - B.col (2 : Fin 4).castSucc =
      (P.r 1 : ℤ) + P.r 2 - P.g 1
    rw [SkewJacobiNegative.BetaDiagram.positiveBorder_row_succ,
      SkewJacobiNegative.BetaDiagram.positiveBorder_col_castSucc]
    have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M 1 2) P.indices_four
    simpa only [Profile.toBetaDiagram, fourIndices, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] using hi
  · change B.row (2 : Fin 4).succ - B.col (3 : Fin 4).castSucc =
      (P.r 2 : ℤ) + P.r 3 - P.g 2
    rw [SkewJacobiNegative.BetaDiagram.positiveBorder_row_succ,
      SkewJacobiNegative.BetaDiagram.positiveBorder_col_castSucc]
    have hi := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M 2 3) P.indices_four
    simpa only [Profile.toBetaDiagram, fourIndices, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] using hi
  · change B.row (Fin.last 3).succ - B.col (Fin.last 4) = (P.r 3 : ℤ) + v
    rw [SkewJacobiNegative.BetaDiagram.positiveBorder_row_succ,
      SkewJacobiNegative.BetaDiagram.positiveBorder_col_last]
    change P.xi 3 - (P.zeta 3 - v) = (P.r 3 : ℤ) + v
    have hi := P.xi_sub_zeta 3
    omega

/-- The displayed F border row word, valid at all positive margins. -/
theorem F_border_row_lengths (w b c : ℕ) (hcw : c < w) (hb : c + w < b)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    ((familyF w b c hcw hb).toBetaDiagram.positiveBorder u v hu hv).rowLength =
      ![(w : ℤ) + u, (b : ℤ) + (w - c), 2 * (b : ℤ) - c,
        2 * (b : ℤ) - c, (b : ℤ) + (w - c) + v] := by
  rw [profile_border_row_lengths]
  have hsub : ((b + w - c : ℕ) : ℤ) = (b : ℤ) + w - c := by omega
  funext i
  fin_cases i <;> simp [familyF, hsub] <;> omega

/-- The displayed H border row word. -/
theorem H_border_row_lengths (w b c : ℕ) (hcw : c < w) (hb : c + w < b)
    (u v : ℤ) (hu : 0 < u) (hv : 0 < v) :
    ((familyH w b c hcw hb).toBetaDiagram.positiveBorder u v hu hv).rowLength =
      ![(w : ℤ) + u, (b : ℤ) + (w - c), 2 * (b : ℤ) - c,
        2 * (b : ℤ) - c + (w - c), (b : ℤ) + v] := by
  rw [profile_border_row_lengths]
  have hsub : ((b + w - c : ℕ) : ℤ) = (b : ℤ) + w - c := by omega
  funext i
  fin_cases i <;> simp [familyH, hsub] <;> omega

/-- Evaluation of the actual five-row monomial is independent of profile proof fields. -/
theorem complete_five_word_product (a b c d e : ℤ) :
    (∏ i : Fin 5, complete (![a, b, c, d, e] i)) =
      complete a * complete b * complete c * complete d * complete e := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change complete a * (complete b * (complete c * (complete d * complete e))) =
    complete a * complete b * complete c * complete d * complete e
  ring

/-- At tied margins the actual row monomial forces precisely q=b-c.
This is a symbolic generator-pair reading, with no parameter census. -/
theorem exceptional_tied_margin_forced (w b c : ℕ) (hcw : c < w)
    (hb : c + w < b) (q : ℤ) (hq : 0 < q)
    (he : ((familyF w b c hcw hb).toBetaDiagram.positiveBorder q q hq hq).schur =
      ((familyH w b c hcw hb).toBetaDiagram.positiveBorder q q hq hq).schur) :
    q = (b : ℤ) - c := by
  let F := (familyF w b c hcw hb).toBetaDiagram.positiveBorder q q hq hq
  let H := (familyH w b c hcw hb).toBetaDiagram.positiveBorder q q hq hq
  have hrow := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [SkewJacobiNegative.BetaDiagram.square_initialForm,
    SkewJacobiNegative.BetaDiagram.square_initialForm] at hrow
  change (∏ i : Fin 5, complete (F.rowLength i)) =
    (∏ i : Fin 5, complete (H.rowLength i)) at hrow
  have hrf := F_border_row_lengths w b c hcw hb q q hq hq
  have hrh := H_border_row_lengths w b c hcw hb q q hq hq
  let K := complete ((w : ℤ) + q) * complete ((b : ℤ) + (w - c)) *
    complete (2 * (b : ℤ) - c)
  rw [hrf, hrh] at hrow
  rw [complete_five_word_product, complete_five_word_product] at hrow
  have hprod :
      K * (complete (2 * (b : ℤ) - c) * complete ((b : ℤ) + (w - c) + q)) =
      K * (complete (2 * (b : ℤ) - c + (w - c)) * complete ((b : ℤ) + q)) := by
    simpa only [K, mul_assoc] using hrow
  have hK : K ≠ 0 := by
    dsimp only [K]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact (complete_ne_zero_iff _).mpr (by omega)
      · exact (complete_ne_zero_iff _).mpr (by omega)
    · exact (complete_ne_zero_iff _).mpr (by omega)
  have hp := mul_left_cancel₀ hK hprod
  rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hp with
    ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega

/-- Every positive border of the displayed F differs from every positive border
of either orientation of H.  This proves the full all-margin cofactor-orbit exclusion. -/
theorem exceptional_F_all_borders_ne (w b c : ℕ) (hc : 1 ≤ c)
    (hcw : c < w) (hb : c + w < b) (Q : Profile 3)
    (hQ : Q = familyH w b c hcw hb ∨ Q = (familyH w b c hcw hb).rotate)
    (u v a d : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hd : 0 < d) :
    ((familyF w b c hcw hb).toBetaDiagram.positiveBorder u v hu hv).schur ≠
      (Q.toBetaDiagram.positiveBorder a d ha hd).schur := by
  by_cases huv : u = v
  · subst v
    intro he
    let F := (familyF w b c hcw hb).toBetaDiagram
    have hcF : F.Connected := Profile.toBetaDiagram_connected _
    have hcQ : Q.toBetaDiagram.Connected := Profile.toBetaDiagram_connected _
    have hspan : F.largestLabel = Q.toBetaDiagram.largestLabel := by
      apply F.largestLabel_eq_of_schur_eq _ hcF hcQ
      rcases hQ with rfl | rfl <;>
        simpa only [F, Profile.toBetaDiagram_schur, Profile.schur_rotate] using
          family_schur_eq w b c hcw hb
    have hm := different_child_margins_recovered F Q.toBetaDiagram hcF hcQ hspan
      u u a d hu hu ha hd he
    have hau : a = u := by rcases hm with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
    have hdu : d = u := by rcases hm with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
    subst a
    subst d
    have he' : ((familyF w b c hcw hb).toBetaDiagram.positiveBorder u u hu hu).schur =
        ((familyH w b c hcw hb).toBetaDiagram.positiveBorder u u hu hu).schur := by
      rcases hQ with rfl | rfl
      · exact he
      · rw [← equal_margin_border_rotate_schur] at he
        exact he
    have ht := exceptional_tied_margin_forced w b c hcw hb u hu he'
    subst u
    exact exceptional_equal_margin_borders_ne w b c hc hcw hb he'
  · exact exceptional_unequal_margin_borders_ne w b c hcw hb Q hQ
      u v a d hu hv ha hd huv

/-- `lem:four-border`: arbitrary positive margins and both orientations of
both exceptional cofactor orbits. -/
theorem four_border_exclusion (w b c : ℕ) (hc : 1 ≤ c)
    (hcw : c < w) (hb : c + w < b) (P Q : Profile 3)
    (hP : P = familyF w b c hcw hb ∨ P = (familyF w b c hcw hb).rotate)
    (hQ : Q = familyH w b c hcw hb ∨ Q = (familyH w b c hcw hb).rotate)
    (u v a d : ℤ) (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) (hd : 0 < d) :
    (P.toBetaDiagram.positiveBorder u v hu hv).schur ≠
      (Q.toBetaDiagram.positiveBorder a d ha hd).schur := by
  rcases hP with rfl | rfl
  · exact exceptional_F_all_borders_ne w b c hc hcw hb Q hQ u v a d hu hv ha hd
  · intro he
    let F := (familyF w b c hcw hb).toBetaDiagram.positiveBorder v u hv hu
    let G := (familyF w b c hcw hb).rotate.toBetaDiagram.positiveBorder u v hu hv
    have hR : F.RotationEquivalent G :=
      positiveBorder_rotation_transport _ _ (profile_rotation_equivalent _) v u hv hu
    have hT := (F.translation_rotate_iff_rotation G).mpr hR
    have hFG : F.schur = G.schur := hT.schur_eq.trans G.rotate_schur
    apply exceptional_F_all_borders_ne w b c hc hcw hb Q hQ v u a d hv hu ha hd
    exact hFG.trans he

end FourRowBorders
end SkewJacobiNegative

namespace SkewJacobiNegative.BetaDiagram
open Gluing FourRowHessenberg FourRowClasses FourRowBorders
variable {n : ℕ}

/-- Ordered natural gaps are the literal adjacent full-board beta differences. -/
theorem toProfile_gap (D : BetaDiagram (n + 1)) (hD : D.Connected) (j : Fin n) :
    ((D.toProfile hD).g j : ℤ) = D.row j.succ - D.col j.castSucc := by
  have hh := (D.toProfile hD).xi_succ_sub_zeta_castSucc j
  rw [D.toProfile_xi hD, D.toProfile_zeta hD] at hh
  change (D.row j.succ - D.col (Fin.last n)) -
    (D.col j.castSucc - D.col (Fin.last n)) = ((D.toProfile hD).g j : ℤ) at hh
  omega

/-- Actual endpoint extensions have identical ordered overlap words. -/
theorem endpoint_profiles_gap_eq (D : BetaDiagram (n + 1)) (hD : D.Connected)
    (t : ℤ) (ht : 0 < t) :
    ((D.extendTop t ht).toProfile (D.extendTop_connected hD t ht)).g =
      ((D.extendBottom t ht).toProfile (D.extendBottom_connected hD t ht)).g := by
  funext j
  apply Int.ofNat_inj.mp
  rw [toProfile_gap, toProfile_gap]
  simp [extendTop, extendBottom, Fin.succ_ne_zero, Fin.castSucc_ne_last]

/-- Literal profile motion produces motion of the original, unnormalized beta lists. -/
theorem motion_of_toProfile_motion (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected)
    (h : D.toProfile hD = E.toProfile hE ∨ D.toProfile hD = (E.toProfile hE).rotate) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  rcases h with h | h
  · left
    refine ⟨D.col (Fin.last n) - E.col (Fin.last n), ?_, ?_⟩
    · intro i
      have hh := congrArg (fun P : Profile n => P.xi i) h
      rw [D.toProfile_xi hD, E.toProfile_xi hE] at hh
      change D.row i - D.col (Fin.last n) = E.row i - E.col (Fin.last n) at hh
      omega
    · intro i
      have hh := congrArg (fun P : Profile n => P.zeta i) h
      rw [D.toProfile_zeta hD, E.toProfile_zeta hE] at hh
      change D.col i - D.col (Fin.last n) = E.col i - E.col (Fin.last n) at hh
      omega
  · right
    refine ⟨D.col (Fin.last n) + E.row 0, ?_, ?_⟩
    · intro i
      have hh := congrArg (fun P : Profile n => P.xi i) h
      rw [Profile.xi_rotate, D.toProfile_xi hD, E.toProfile_xi hE,
        E.toProfile_zeta hE] at hh
      change D.row i - D.col (Fin.last n) =
        (E.row 0 - E.col (Fin.last n)) - (E.col i.rev - E.col (Fin.last n)) at hh
      omega
    · intro i
      have hh := congrArg (fun P : Profile n => P.zeta i) h
      rw [Profile.zeta_rotate, D.toProfile_zeta hD, E.toProfile_xi hE] at hh
      change D.col i - D.col (Fin.last n) =
        (E.row 0 - E.col (Fin.last n)) - (E.row i.rev - E.col (Fin.last n)) at hh
      omega

/-- Equal ordered overlap words cannot connect the two distinct exceptional orbits. -/
theorem familyRelation_false_of_gap_eq (P Q : Profile 3) (hg : P.g = Q.g) :
    ¬ FamilyRelation P Q := by
  rintro ⟨w, b, c, hcw, hb, hcase⟩
  rcases hcase with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ <;>
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  all_goals
    have hh := congrFun hg 1
    simp [familyF, familyH, Profile.rotate] at hh
    omega

/-- Opposite endpoints of any connected four-row child compare only by rotation.
The full classification is applied to the actual endpoint profiles. -/
theorem four_endpoint_equality_symmetric (C : BetaDiagram 4) (hC : C.Connected)
    (t : ℤ) (ht : 0 < t)
    (he : (C.extendTop t ht).schur = (C.extendBottom t ht).schur) : C.Symmetric := by
  let hT := C.extendTop_connected hC t ht
  let hB := C.extendBottom_connected hC t ht
  let P := (C.extendTop t ht).toProfile hT
  let Q := (C.extendBottom t ht).toProfile hB
  have hh := (four_rows_schur_eq_iff P Q).mp
    (by simpa only [P, Q, toProfile_schur] using he)
  have hm : P = Q ∨ P = Q.rotate := by
    rcases hh with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
    · exact False.elim (familyRelation_false_of_gap_eq P Q
        (C.endpoint_profiles_gap_eq hC t ht) hh)
  rcases motion_of_toProfile_motion (C.extendTop t ht) (C.extendBottom t ht) hT hB hm with
    hh | hh
  · exact False.elim (C.extendTop_not_translation_extendBottom t ht hh)
  · exact C.symmetric_of_extendTop_rotation_extendBottom t ht hh

/-- Normalization of the actual child reconstructs the actual parent as its
positive border with the source's own strict margins. -/
theorem parent_profile_border_translation (D : BetaDiagram (n + 2))
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected) :
    D.TranslationEquivalent
      (((D.cornerDiagram hP).toProfile hC).toBetaDiagram.positiveBorder
        D.topMargin D.bottomMargin D.topMargin_pos D.bottomMargin_pos) := by
  let C := D.cornerDiagram hP
  refine ⟨C.col (Fin.last n), ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
      change D.row 0 = (C.toProfile hC).xi 0 + D.topMargin + C.col (Fin.last n)
      rw [C.toProfile_xi hC]
      simp only [C, cornerDiagram, topMargin]
      ring
    | succ i =>
      change D.row i.succ = (C.toProfile hC).xi i + C.col (Fin.last n)
      rw [C.toProfile_xi hC]
      simp only [C, cornerDiagram]
      ring
  · intro i
    cases i using Fin.lastCases with
    | last =>
      rw [positiveBorder_col_last]
      change D.col (Fin.last (n + 1)) =
        (C.toProfile hC).zeta (Fin.last n) - D.bottomMargin + C.col (Fin.last n)
      rw [Profile.zeta_last]
      simp only [C, cornerDiagram, bottomMargin]
      ring
    | cast i =>
      rw [positiveBorder_col_castSucc]
      change D.col i.castSucc = (C.toProfile hC).zeta i + C.col (Fin.last n)
      rw [C.toProfile_zeta hC]
      simp only [C, cornerDiagram]
      ring

/-- A connected child's normalized profile retains zero-freeness. -/
theorem toProfile_zeroFree (D : BetaDiagram (n + 1)) (hD : D.Connected)
    (hZ : D.ZeroFree) : (D.toProfile hD).toBetaDiagram.ZeroFree := by
  intro i j hh
  change (D.toProfile hD).xi i = (D.toProfile hD).zeta j at hh
  rw [D.toProfile_xi hD, D.toProfile_zeta hD] at hh
  change D.row i - D.col (Fin.last n) = D.col j - D.col (Fin.last n) at hh
  exact hZ i j (by omega)

/-- No five-row equal parents with connected zero-free four-row children cross
between the two exceptional child orbits.  The children need not be rigid. -/
theorem four_child_motion_of_parent_eq (D E : BetaDiagram 5)
    (hD : D.Connected) (hE : E.Connected) (hZ : D.ZeroFree)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hCD : (D.cornerDiagram hPD).Connected) (hCE : (E.cornerDiagram hPE).Connected)
    (he : D.schur = E.schur) :
    (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE) ∨
      (D.cornerDiagram hPD).RotationEquivalent (E.cornerDiagram hPE) := by
  let C := D.cornerDiagram hPD
  let T := E.cornerDiagram hPE
  let P := C.toProfile hCD
  let Q := T.toProfile hCE
  have hc : C.schur = T.schur := D.cornerPolynomial_eq_of_schur_eq E hD hE he
  have hclass := (four_rows_schur_eq_iff P Q).mp
    (by simpa only [P, Q, toProfile_schur] using hc)
  rcases hclass with hh | hh | ⟨w, b, c, hcw, hb, hcase⟩
  · exact motion_of_toProfile_motion C T hCD hCE (Or.inl hh)
  · exact motion_of_toProfile_motion C T hCD hCE (Or.inr hh)
  · have hCZ : C.ZeroFree := D.corner_zeroFree hZ hPD
    have hPZ : P.toBetaDiagram.ZeroFree := C.toProfile_zeroFree hCD hCZ
    have hquart : P ∈ exceptionalQuartet w b c hcw hb := by
      simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false]
      rcases hcase with ⟨hP, _⟩ | ⟨hP, _⟩
      · rcases hP with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases hP with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    have hcpos := exceptional_c_pos_of_zeroFree w b c hcw hb P hquart hPZ
    have hd := (D.parent_profile_border_translation hPD hCD).schur_eq
    have het := (E.parent_profile_border_translation hPE hCE).schur_eq
    have hp : (P.toBetaDiagram.positiveBorder D.topMargin D.bottomMargin
        D.topMargin_pos D.bottomMargin_pos).schur =
      (Q.toBetaDiagram.positiveBorder E.topMargin E.bottomMargin
        E.topMargin_pos E.bottomMargin_pos).schur := hd.symm.trans (he.trans het)
    rcases hcase with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · exact False.elim (four_border_exclusion w b c hcpos hcw hb P Q hP hQ
        D.topMargin D.bottomMargin E.topMargin E.bottomMargin
        D.topMargin_pos D.bottomMargin_pos E.topMargin_pos E.bottomMargin_pos hp)
    · exact False.elim (four_border_exclusion w b c hcpos hcw hb Q P hQ hP
        E.topMargin E.bottomMargin D.topMargin D.bottomMargin
        E.topMargin_pos E.bottomMargin_pos D.topMargin_pos D.bottomMargin_pos hp.symm)

/-- Every zero-free five-row parent with a connected actual four-row child
is rigid against arbitrary connected mates. -/
theorem five_connected_corner_zeroFree_rigidity (D : BetaDiagram 5)
    (hD : D.Connected) (hZ : D.ZeroFree)
    (hP : D.PositiveCorner) (hC : (D.cornerDiagram hP).Connected) : D.RotationRigid := by
  apply (rotationRigid_iff_same_order D).mpr
  intro E hE he
  let hPE := D.positiveCorner_of_cornerPolynomial_eq E hD hE hP
    (D.cornerPolynomial_eq_of_schur_eq E hD hE he.symm)
  have hCE := D.connected_corner_of_corner_eq E hD hE hP hC he.symm
  have hm := D.four_child_motion_of_parent_eq E hD hE hZ hP hPE hC hCE he.symm
  have hEnd : ∀ (t : ℤ) (ht : 0 < t),
      ((D.cornerDiagram hP).extendTop t ht).schur =
      ((D.cornerDiagram hP).extendBottom t ht).schur → (D.cornerDiagram hP).Symmetric :=
    (D.cornerDiagram hP).four_endpoint_equality_symmetric hC
  rcases hm with htr | hrot
  · exact D.connected_border_aligned_rigidity E hD hE hP hPE hC hCE htr hEnd he.symm
  · have hEr := E.rotate_connected hE
    have hPr := E.rotate_positiveCorner hPE
    have hCr : (E.rotate.cornerDiagram hPr).Connected := by
      apply connected_of_schur_irreducible _ (by omega)
      rw [← (D.corner_translation_of_rotation E hP hPE hrot).schur_eq]
      exact (D.cornerDiagram hP).schur_irreducible hC
    have hh := D.connected_border_aligned_rigidity E.rotate hD hEr hP hPr hC hCr
      (D.corner_translation_of_rotation E hP hPE hrot) hEnd (he.symm.trans E.rotate_schur.symm)
    rcases hh with hh | hh
    · exact Or.inr ((D.translation_rotate_iff_rotation E).mp hh)
    · exact Or.inl ((D.rotation_rotate_iff_translation E).mp hh)

/-- Zero-free three-corner rigidity, with its five-row exceptional-orbit
exclusion and every higher child/endpoint condition produced from the source. -/
theorem three_corners_zeroFree_rigidity (D : BetaDiagram (n + 5))
    (hD : D.Connected) (hZ : D.ZeroFree) (h : D.ThreeCorners) : D.RotationRigid := by
  induction n with
  | zero =>
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    exact D.five_connected_corner_zeroFree_rigidity hD hZ hP
      (D.three_corners_corner_connected hP h)
  | succ n ih =>
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    let C := D.cornerDiagram hP
    have hC : C.Connected := D.three_corners_corner_connected hP h
    have hCZ : C.ZeroFree := D.corner_zeroFree hZ hP
    have hCond : C.ThreeCorners := D.corner_three_corners hP h
    apply D.connected_border_rigidity hD hP hC
    · exact ih C hC hCZ hCond
    · intro t ht
      exact ih (C.extendTop t ht) (C.extendTop_connected hC t ht)
        (C.extendTop_zeroFree hCZ t ht) (C.extendTop_three_corners hCond t ht)

/-- `prop:three-corners`, for every source row count ≥5 and common betas. -/
theorem three_corners_rigidity (D : BetaDiagram (n + 5)) (hD : D.Connected)
    (h : D.ThreeCorners) : D.RotationRigid := by
  apply D.gamma_rigidity_descends hD
  exact D.gamma.three_corners_zeroFree_rigidity
    ((D.gamma_connected_iff).mpr hD) D.gamma_zeroFree ((D.gamma_three_corners_iff).mpr h)

/-- No connectedness, row-count or board-pattern premise is imposed on the mate. -/
theorem three_corners_full_class (D : BetaDiagram (n + 5)) (hD : D.Connected)
    (h : D.ThreeCorners) {m : ℕ} (E : BetaDiagram m) (he : E.schur = D.schur) :
    D.MotionEquivalent E := (D.three_corners_rigidity hD h).full_mate hD E he

/-- At three negatives the source patterns are exhausted by columns and
the three-corner inequalities; no five-row exceptional family remains. -/
theorem three_negative_rigidity (D : BetaDiagram (n + 5)) (hD : D.Connected)
    (hcount : negativeCount D ≤ 3) : D.RotationRigid := by
  rcases D.small_negative_shape_dichotomy (by omega) with
    h | h | h | h | h | h
  · exact D.column_negatives_rigidity hD h
  · exact D.rotationRigid_of_rotate (D.rotate.column_negatives_rigidity
      (D.rotate_connected hD) h)
  · exact D.three_corners_rigidity hD h
  · have hn := D.square_negative_count h
    omega
  · have hn := D.hook_negative_count h
    omega
  · have hn := D.rotate.hook_negative_count h
    have he := D.rotate.negativeCount_eq_of_schur_eq D D.rotate_schur
    omega

/-- The three-negative full-board class is a rotation orbit in all source orders ≥5. -/
theorem three_negative_full_class (D : BetaDiagram (n + 5)) (hD : D.Connected)
    (hcount : negativeCount D ≤ 3) {m : ℕ} (E : BetaDiagram m)
    (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.three_negative_rigidity hD hcount).full_mate hD E he

/-- All actual source masks with at most four negatives are exhausted by the
unbounded column, three-corner, square and hook producers. -/
theorem small_negative_rigidity (D : BetaDiagram (n + 5)) (hD : D.Connected)
    (hcount : negativeCount D ≤ 4) : D.RotationRigid := by
  rcases D.small_negative_shape_dichotomy hcount with h | h | h | h | h | h
  · exact D.column_negatives_rigidity hD h
  · exact D.rotationRigid_of_rotate (D.rotate.column_negatives_rigidity
      (D.rotate_connected hD) h)
  · exact D.three_corners_rigidity hD h
  · exact D.square_rigidity (by omega) hD h
  · exact D.hook_negatives_rigidity (by omega) hD h
  · exact D.rotationRigid_of_rotate (D.rotate.hook_negatives_rigidity
      (by omega) (D.rotate_connected hD) h)

/-- Every positive top endpoint retains the source's actual four-negative budget
and is settled by the full all-mask theorem. -/
theorem small_negative_endpoint_rigidity (D : BetaDiagram (n + 5))
    (hD : D.Connected) (hcount : negativeCount D ≤ 4)
    (t : ℤ) (ht : 0 < t) : (D.extendTop t ht).RotationRigid := by
  apply small_negative_rigidity _ (D.extendTop_connected hD t ht)
  rw [extendTop_negativeCount]
  exact hcount

/-- The higher-row four-negative class has no order, connectedness or mask
restriction on its mate, and includes all common-beta boundaries. -/
theorem small_negative_full_class (D : BetaDiagram (n + 5)) (hD : D.Connected)
    (hcount : negativeCount D ≤ 4) {m : ℕ} (E : BetaDiagram m)
    (he : E.schur = D.schur) : D.MotionEquivalent E :=
  (D.small_negative_rigidity hD hcount).full_mate hD E he

/-- Complete classification through four negatives at every source order.
The only nonmotion alternative has four source and mate rows, exactly three
negative sites, and the literal F/H family relation with its original parameters. -/
theorem low_negative_complete_class (D : BetaDiagram n) (hD : D.Connected)
    (hcount : negativeCount D ≤ 4) {m : ℕ} (E : BetaDiagram m)
    (he : E.schur = D.schur) :
    D.MotionEquivalent E ∨
      ∃ hrowD : n = 4, ∃ hrowE : m = 4,
        ∃ hDC : (D.castOrder hrowD).Connected,
        ∃ hEC : (E.castOrder hrowE).Connected,
          negativeCount D = 3 ∧
          FamilyRelation ((D.castOrder hrowD).toProfile hDC)
            ((E.castOrder hrowE).toProfile hEC) := by
  by_cases hn : n ≤ 3
  · left
    have hR : D.RotationRigid := by
      apply (rotationRigid_iff_same_order D).mpr
      intro F hF hp
      exact D.small_rows_rigidity_same_order F hD hF hn hp.symm
    exact hR.full_mate hD E he
  · by_cases hn4 : n = 4
    · subst n
      have hm4 : m = 4 := E.row_count_of_schur_eq D he
      subst m
      have hE := D.connected_full_mate_of_schur_eq E hD he.symm
      let P := D.toProfile hD
      let Q := E.toProfile hE
      have hclass := four_rows_complete_class_same_order D E hD hE he.symm
      rcases hclass with hp | hp | hp
      · left
        exact ⟨rfl, D.motion_of_toProfile_motion E hD hE (Or.inl hp)⟩
      · left
        exact ⟨rfl, D.motion_of_toProfile_motion E hD hE (Or.inr hp)⟩
      · right
        refine ⟨rfl, rfl, hD, hE, ?_, hp⟩
        have hpcount : negativeCount P.toBetaDiagram = 3 := by
          rcases hp with ⟨w, b, c, hcw, hb, hcase⟩
          have hquart : P ∈ exceptionalQuartet w b c hcw hb := by
            simp only [exceptionalQuartet, List.mem_cons, List.not_mem_nil, or_false]
            rcases hcase with ⟨hP, _⟩ | ⟨hP, _⟩
            · rcases hP with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
            · rcases hP with h | h
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr h))
          exact exceptionalQuartet_negative_count w b c hcw hb P hquart
        have hpoly : P.toBetaDiagram.schur = D.schur := by
          rw [Profile.toBetaDiagram_schur]
          exact D.toProfile_schur hD
        have hnc := P.toBetaDiagram.negativeCount_eq_of_schur_eq D hpoly
        omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      exact Or.inl ((D.small_negative_rigidity hD hcount).full_mate hD E he)

end SkewJacobiNegative.BetaDiagram
