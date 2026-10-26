/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseQuarticAlgebra

/-!
# Square-initial signs at single middle-row contacts

The deleted-diagonal step in `thm:staircase-residual-matching`.
Strict interval-merge costs keep every positive perturbation above a negative
first merge.  Tied negative minima retain both coefficients.
-/

namespace SkewJacobiNegative.Staircase
open MvPolynomial

private theorem strict_add {w : ℕ+ → ℝ} {p q : CompleteRing} {a : ℝ}
    (hp : Base.WeightStrictLowerBound w p a) (hq : Base.WeightStrictLowerBound w q a) :
    Base.WeightStrictLowerBound w (p+q) a := by
  intro d hd
  rw [MvPolynomial.coeff_add] at hd
  by_cases hz : p.coeff d = 0
  · exact hq d (by simpa only [hz,zero_add] using hd)
  · exact hp d hz

private theorem strict_neg {w : ℕ+ → ℝ} {p : CompleteRing} {a : ℝ}
    (hp : Base.WeightStrictLowerBound w p a) :
    Base.WeightStrictLowerBound w (-p) a := by
  intro d hd
  apply hp d
  simpa only [MvPolynomial.coeff_neg, neg_ne_zero] using hd

private theorem homogeneous_strict {w : ℕ+ → ℝ} {p : CompleteRing} {a b : ℝ}
    (hp : IsWeightedHomogeneous w p b) (hab : a < b) :
    Base.WeightStrictLowerBound w p a := by
  intro d hd
  exact hab.trans_eq (hp hd).symm

private theorem negative_unique_initial (w : ℕ+ → ℝ) (N M H : CompleteRing)
    (a b : ℝ) (hN : IsWeightedHomogeneous w N a)
    (hM : IsWeightedHomogeneous w M b) (hNz : N ≠ 0) (hab : a < b)
    (hH : Base.WeightStrictLowerBound w H a) :
    Base.initialForm w (-N-M+H) = -N := by
  have hHigher := strict_add (strict_neg (homogeneous_strict hM hab)) hH
  have hLeast : Base.leastWeight w (-N) = a :=
    Base.leastWeight_eq_of_homogeneous (neg_ne_zero.mpr hNz) hN.neg
  have hHigher' : Base.WeightStrictLowerBound w (-M+H) (Base.leastWeight w (-N)) := by
    rw [hLeast]
    exact hHigher
  rw [show -N-M+H = -N+(-M+H) by ring,
    Base.initialForm_add_eq_left (neg_ne_zero.mpr hNz) hHigher']
  exact Base.initialForm_eq_of_homogeneous (neg_ne_zero.mpr hNz) hN.neg

/-- Two negative homogeneous minima cannot be canceled by a strictly higher
perturbation; a tie retains both unit coefficients. -/
theorem negative_pair_initial_augmentation (w : ℕ+ → ℝ) (N M H : CompleteRing)
    (a b : ℝ) (hN : IsWeightedHomogeneous w N a)
    (hM : IsWeightedHomogeneous w M b)
    (hEN : residualAugmentation N = 1) (hEM : residualAugmentation M = 1)
    (hH : Base.WeightStrictLowerBound w H (min a b)) :
    residualAugmentation (Base.initialForm w (-N-M+H)) = -1 ∨
      residualAugmentation (Base.initialForm w (-N-M+H)) = -2 := by
  have hNz : N ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hEN
    norm_num at hEN
  have hMz : M ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hEM
    norm_num at hEM
  rcases lt_trichotomy a b with hab | hab | hba
  · left
    rw [negative_unique_initial w N M H a b hN hM hNz hab
      (by simpa only [min_eq_left hab.le] using hH), map_neg, hEN]
  · right
    have hHom : IsWeightedHomogeneous w (-N-M) a := by
      apply hN.neg.sub
      simpa only [hab] using hM
    have hEval : residualAugmentation (-N-M) = -2 := by
      rw [map_sub,map_neg,hEN,hEM]
      norm_num
    have hNe : -N-M ≠ 0 := by
      intro hz
      rw [hz,map_zero] at hEval
      norm_num at hEval
    have hLeast : Base.leastWeight w (-N-M) = a :=
      Base.leastWeight_eq_of_homogeneous hNe hHom
    have hHigher : Base.WeightStrictLowerBound w H (Base.leastWeight w (-N-M)) := by
      rw [hLeast]
      simpa only [hab,min_self] using hH
    rw [Base.initialForm_add_eq_left hNe hHigher,
      Base.initialForm_eq_of_homogeneous hNe hHom]
    exact hEval
  · left
    rw [show -N-M+H = -M-N+H by ring,
      negative_unique_initial w M N H b a hM hN hMz hba
        (by simpa only [min_eq_right hba.le] using hH), map_neg, hEM]

private theorem square_complete_homogeneous (k : ℤ) (hk : 0 < k) :
    IsWeightedHomogeneous Base.squareWeight.generatorWeight (complete k) ((k : ℝ)^2) := by
  rw [complete_of_pos hk]
  have h := MvPolynomial.isWeightedHomogeneous_X ℚ Base.squareWeight.generatorWeight
    (⟨k.toNat,by omega⟩ : ℕ+)
  have hc : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk.le
  change IsWeightedHomogeneous Base.squareWeight.generatorWeight _ ((k.toNat : ℝ)^2) at h
  rw [hc] at h
  exact h

private def squareWordWeight (T : Fin 4 → ℤ) : ℤ :=
  (T 0)^2 + (T 1)^2 + (T 2)^2 + (T 3)^2

private theorem quartet_square_homogeneous (T : Fin 4 → ℤ) (hT : ∀ i, 0 < T i) :
    IsWeightedHomogeneous Base.squareWeight.generatorWeight (quartetTerm T)
      (squareWordWeight T : ℝ) := by
  have h := ((square_complete_homogeneous (T 0) (hT 0)).mul
    (square_complete_homogeneous (T 1) (hT 1))).mul
      (square_complete_homogeneous (T 2) (hT 2))
  have hh := h.mul (square_complete_homogeneous (T 3) (hT 3))
  simpa only [quartetTerm, squareWordWeight, Int.cast_add, Int.cast_pow] using hh

private theorem quartet_augmentation_one (T : Fin 4 → ℤ) (hT : ∀ i, 0 < T i) :
    residualAugmentation (quartetTerm T) = 1 := by
  rw [quartetTerm_monomial T hT, residualAugmentation_monomial]

/-- A single erased second row leaves one or two negative first merges as
the square-initial layer; every further interval merge has higher weight. -/
theorem single_middleB_initial_negative (q : ℕ+) (a c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hb : r+s < q.val) (hc : s+t < c) (hd : t < d)
    (hane : a ≠ q.val) (hcne : c ≠ q.val) (htne : t ≠ q.val)
    (hdne : d ≠ q.val) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight
      (HessenbergExpansion.fourInterval (bar q) a q.val c d r s t)) = -1 ∨
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight
      (HessenbergExpansion.fourInterval (bar q) a q.val c d r s t)) = -2 := by
  let u : ℤ := a+q.val-r
  let v : ℤ := q.val+c-s
  let w : ℤ := c+d-t
  let x : ℤ := a+q.val+c-r-s
  let y : ℤ := q.val+c+d-s-t
  let f : ℤ := a+q.val+c+d-r-s-t
  let N : Fin 4 → ℤ := ![u,r,c,d]
  let M : Fin 4 → ℤ := ![a,v,s,d]
  let X : Fin 4 → ℤ := ![x,r,s,d]
  let Y : Fin 4 → ℤ := ![u,r,w,t]
  let Z : Fin 4 → ℤ := ![a,y,s,t]
  let F : Fin 4 → ℤ := ![f,r,s,t]
  let Yp : CompleteRing := if w = q.val then 0 else quartetTerm Y
  let H : CompleteRing := quartetTerm X+Yp+quartetTerm Z-quartetTerm F
  have hpN : ∀ i, 0 < N i := by
    intro i; fin_cases i <;> dsimp [N,u] <;> omega
  have hpM : ∀ i, 0 < M i := by
    intro i; fin_cases i <;> dsimp [M,v] <;> omega
  have hpX : ∀ i, 0 < X i := by
    intro i; fin_cases i <;> dsimp [X,x] <;> omega
  have hpY : ∀ i, 0 < Y i := by
    intro i; fin_cases i <;> dsimp [Y,u,w] <;> omega
  have hpZ : ∀ i, 0 < Z i := by
    intro i; fin_cases i <;> dsimp [Z,y] <;> omega
  have hpF : ∀ i, 0 < F i := by
    intro i; fin_cases i <;> dsimp [F,f] <;> omega
  have hX : squareWordWeight N < squareWordWeight X := by
    have h := CubicNecessity.join_weight_strict u c s (by dsimp [u]; omega) (by omega)
    dsimp [squareWordWeight,N,X,u,x] at *
    nlinarith
  have hY : squareWordWeight N < squareWordWeight Y := by
    have h := CubicNecessity.join_weight_strict c d t (by omega) (by omega)
    dsimp [squareWordWeight,N,Y,u,w] at *
    nlinarith
  have hZ : squareWordWeight M < squareWordWeight Z := by
    have h := CubicNecessity.join_weight_strict v d t (by dsimp [v]; omega) (by omega)
    dsimp [squareWordWeight,M,Z,v,y] at *
    nlinarith
  have hF : squareWordWeight X < squareWordWeight F := by
    have h := CubicNecessity.join_weight_strict x d t (by dsimp [x]; omega) (by omega)
    dsimp [squareWordWeight,X,F,x,f] at *
    nlinarith
  let lo : ℝ := min (squareWordWeight N : ℝ) (squareWordWeight M : ℝ)
  have hLX : lo < (squareWordWeight X : ℝ) :=
    (min_le_left _ _).trans_lt (by exact_mod_cast hX)
  have hLY : lo < (squareWordWeight Y : ℝ) :=
    (min_le_left _ _).trans_lt (by exact_mod_cast hY)
  have hLZ : lo < (squareWordWeight Z : ℝ) :=
    (min_le_right _ _).trans_lt (by exact_mod_cast hZ)
  have hLF : lo < (squareWordWeight F : ℝ) :=
    hLX.trans (by exact_mod_cast hF)
  have hYp : Base.WeightStrictLowerBound Base.squareWeight.generatorWeight Yp lo := by
    dsimp [Yp]
    split_ifs
    · intro e he
      exact (he rfl).elim
    · exact homogeneous_strict (quartet_square_homogeneous Y hpY) hLY
  have hHigher : Base.WeightStrictLowerBound Base.squareWeight.generatorWeight H lo := by
    have h := strict_add (strict_add
      (strict_add (homogeneous_strict (quartet_square_homogeneous X hpX) hLX)
        hYp)
      (homogeneous_strict (quartet_square_homogeneous Z hpZ) hLZ))
      (strict_neg (homogeneous_strict (quartet_square_homogeneous F hpF) hLF))
    simpa only [H,sub_eq_add_neg] using h
  have hbarA := bar_eq_complete_of_ne q a hane
  have hbarC := bar_eq_complete_of_ne q c hcne
  have hbarD := bar_eq_complete_of_ne q d hdne
  have hbarR := bar_eq_complete_of_ne q r (by omega)
  have hbarS := bar_eq_complete_of_ne q s (by omega)
  have hbarT := bar_eq_complete_of_ne q t htne
  have hbarU := bar_eq_complete_of_ne q u (by dsimp [u]; omega)
  have hbarV := bar_eq_complete_of_ne q v (by dsimp [v]; omega)
  have hbarW : bar q w = if w = q.val then 0 else complete w := by
    rw [bar,eraseGenerator_complete]
  have hbarX := bar_eq_complete_of_ne q x (by dsimp [x]; omega)
  have hbarY := bar_eq_complete_of_ne q y (by dsimp [y]; omega)
  have hbarF := bar_eq_complete_of_ne q f (by dsimp [f]; omega)
  dsimp [u,v,w,x,y,f] at hbarU hbarV hbarW hbarX hbarY hbarF
  have hpoly : HessenbergExpansion.fourInterval (bar q) a q.val c d r s t =
      -quartetTerm N-quartetTerm M+H := by
    simp only [HessenbergExpansion.fourInterval,bar_cut,hbarA,hbarC,hbarD,hbarR,hbarS,hbarT,
      hbarU,hbarV,hbarW,hbarX,hbarY,hbarF,zero_mul,mul_zero,zero_add,add_zero,zero_sub,sub_zero]
    dsimp [H,Yp,quartetTerm,N,M,X,Y,Z,F,u,v,w,x,y,f]
    split_ifs <;> ring
  rw [hpoly]
  exact negative_pair_initial_augmentation Base.squareWeight.generatorWeight
    (quartetTerm N) (quartetTerm M) H (squareWordWeight N) (squareWordWeight M)
    (quartet_square_homogeneous N hpN) (quartet_square_homogeneous M hpM)
    (quartet_augmentation_one N hpN) (quartet_augmentation_one M hpM) hHigher

/-- The single second-row contact has a strictly negative square-initial
augmentation on the actual specialized determinant. -/
theorem restriction_middleB_initial_negative {q : ℕ+} {P : Gluing.Profile 3}
    (hP : QComponent q P) (hb : P.r 1 = q.val)
    (ha : P.r 0 ≠ q.val) (hc : P.r 2 ≠ q.val) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight (restriction q P)) = -1 ∨
      residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight (restriction q P)) = -2 := by
  have h0 : (0 : ℤ) < P.g 0 := by exact_mod_cast hP.gap_pos 0
  have h1 : (0 : ℤ) < P.g 1 := by exact_mod_cast hP.gap_pos 1
  have h2 : (0 : ℤ) < P.g 2 := by exact_mod_cast hP.gap_pos 2
  have hbot : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap,Fin.sum_univ_succ] using hP.bottom
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨_,_,_,hA,hB,hC,hD⟩
  have hbi : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  rw [restriction_four_expansion q P hP.thick,hbi]
  exact single_middleB_initial_negative q (P.r 0) (P.r 2) (P.r 3)
    (P.g 0) (P.g 1) (P.g 2) h0 h1 h2 hA (by omega) hC hD
    (by exact_mod_cast ha) (by exact_mod_cast hc) (by exact_mod_cast hP.gap_ne 2)
    (by omega)

/-- The third-row contact uses the same interval-word argument after formal
reversal; no reversed component domain is asserted or assumed. -/
theorem restriction_middleC_initial_negative {q : ℕ+} {P : Gluing.Profile 3}
    (hP : QComponent q P) (hc : P.r 2 = q.val)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 ≠ q.val) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight (restriction q P)) = -1 ∨
      residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight (restriction q P)) = -2 := by
  have h0 : (0 : ℤ) < P.g 0 := by exact_mod_cast hP.gap_pos 0
  have h1 : (0 : ℤ) < P.g 1 := by exact_mod_cast hP.gap_pos 1
  have h2 : (0 : ℤ) < P.g 2 := by exact_mod_cast hP.gap_pos 2
  have hbot : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap,Fin.sum_univ_succ] using hP.bottom
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨_,_,_,hA,hB,hC,hD⟩
  have hci : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  rw [restriction_four_expansion q P hP.thick,hci]
  rw [← HessenbergExpansion.fourInterval_reverse (bar q) (P.r 0) (P.r 1)
    q.val (P.r 3) (P.g 0) (P.g 1) (P.g 2)]
  exact single_middleB_initial_negative q (P.r 3) (P.r 1) (P.r 0)
    (P.g 2) (P.g 1) (P.g 0) h2 h1 h0 hD (by omega) (by omega) hA
    (by omega) (by exact_mod_cast hb) (by exact_mod_cast hP.gap_ne 0)
    (by exact_mod_cast ha)

/-- Positive augmentation identifies the positive member of two competing
homogeneous minima; a nonzero equal-weight difference has augmentation zero. -/
theorem mixed_pair_positive_initial (w : ℕ+ → ℝ) (N Y H : CompleteRing)
    (a b : ℝ) (hN : IsWeightedHomogeneous w N a)
    (hY : IsWeightedHomogeneous w Y b)
    (hEN : residualAugmentation N = 1) (hEY : residualAugmentation Y = 1)
    (hne : N ≠ Y) (hH : Base.WeightStrictLowerBound w H a)
    (heps : residualAugmentation (Base.initialForm w (-N+Y+H)) = 1) :
    Base.initialForm w (-N+Y+H) = Y := by
  have hNz : N ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hEN
    norm_num at hEN
  have hYz : Y ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hEY
    norm_num at hEY
  rcases lt_trichotomy a b with hab | hab | hba
  · have hi : Base.initialForm w (-N+Y+H) = -N := by
      simpa only [sub_neg_eq_add] using
        negative_unique_initial w N (-Y) H a b hN hY.neg hNz hab hH
    rw [hi,map_neg,hEN] at heps
    norm_num at heps
  · have hHom : IsWeightedHomogeneous w (-N+Y) a :=
      hN.neg.add (by simpa only [hab] using hY)
    have hNe : -N+Y ≠ 0 := by
      intro hz
      apply hne
      linear_combination -hz
    have hLeast : Base.leastWeight w (-N+Y) = a :=
      Base.leastWeight_eq_of_homogeneous hNe hHom
    have hHigher : Base.WeightStrictLowerBound w H (Base.leastWeight w (-N+Y)) := by
      rw [hLeast]
      exact hH
    rw [Base.initialForm_add_eq_left hNe hHigher,
      Base.initialForm_eq_of_homogeneous hNe hHom,map_add,map_neg,hEN,hEY] at heps
    norm_num at heps
  · have hHigher : Base.WeightStrictLowerBound w (-N+H) b :=
      strict_add (strict_neg (homogeneous_strict hN hba))
        (fun d hd => hba.trans (hH d hd))
    have hLeast : Base.leastWeight w Y = b :=
      Base.leastWeight_eq_of_homogeneous hYz hY
    have hHigher' : Base.WeightStrictLowerBound w (-N+H) (Base.leastWeight w Y) := by
      rw [hLeast]
      exact hHigher
    rw [show -N+Y+H = Y+(-N+H) by ring,
      Base.initialForm_add_eq_left hYz hHigher']
    exact Base.initialForm_eq_of_homogeneous hYz hY

theorem double_middle_positive_initial (q : ℕ+) (a d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hb : r+s < q.val) (hc : s+t < q.val) (hd : q.val+t < d)
    (hane : a ≠ q.val) (hrs : r ≠ s) (hst : s ≠ t)
    (heps : residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight
      (HessenbergExpansion.fourInterval (bar q) a q.val q.val d r s t)) = 1) :
    Base.initialForm Base.squareWeight.generatorWeight
      (HessenbergExpansion.fourInterval (bar q) a q.val q.val d r s t) =
        complete r*complete t*complete (a+q.val-r)*complete (q.val+d-t) := by
  let u : ℤ := a+q.val-r
  let v : ℤ := (q.val : ℤ)+q.val-s
  let w : ℤ := q.val+d-t
  let x : ℤ := a+q.val+q.val-r-s
  let y : ℤ := (q.val : ℤ)+q.val+d-s-t
  let f : ℤ := a+q.val+q.val+d-r-s-t
  let N : Fin 4 → ℤ := ![s,a,v,d]
  let Y : Fin 4 → ℤ := ![r,t,u,w]
  let X : Fin 4 → ℤ := ![r,s,x,d]
  let Z : Fin 4 → ℤ := ![s,t,a,y]
  let F : Fin 4 → ℤ := ![r,s,t,f]
  let H : CompleteRing := quartetTerm X+quartetTerm Z-quartetTerm F
  have hpN : ∀ i, 0 < N i := by
    intro i; fin_cases i <;> dsimp [N,v] <;> omega
  have hpY : ∀ i, 0 < Y i := by
    intro i; fin_cases i <;> dsimp [Y,u,w] <;> omega
  have hpX : ∀ i, 0 < X i := by
    intro i; fin_cases i <;> dsimp [X,x] <;> omega
  have hpZ : ∀ i, 0 < Z i := by
    intro i; fin_cases i <;> dsimp [Z,y] <;> omega
  have hpF : ∀ i, 0 < F i := by
    intro i; fin_cases i <;> dsimp [F,f] <;> omega
  have hX : squareWordWeight N < squareWordWeight X := by
    have h := CubicNecessity.join_weight_strict a v r ha (by dsimp [v]; omega)
    dsimp [squareWordWeight,N,X,v,x] at *
    nlinarith
  have hZ : squareWordWeight N < squareWordWeight Z := by
    have h := CubicNecessity.join_weight_strict v d t (by dsimp [v]; omega) (by omega)
    dsimp [squareWordWeight,N,Z,v,y] at *
    nlinarith
  have hF : squareWordWeight X < squareWordWeight F := by
    have h := CubicNecessity.join_weight_strict x d t (by dsimp [x]; omega) (by omega)
    dsimp [squareWordWeight,X,F,x,f] at *
    nlinarith
  have hHigher : Base.WeightStrictLowerBound Base.squareWeight.generatorWeight H
      (squareWordWeight N : ℝ) := by
    have hNX : (squareWordWeight N : ℝ) < (squareWordWeight X : ℝ) := by exact_mod_cast hX
    have hNZ : (squareWordWeight N : ℝ) < (squareWordWeight Z : ℝ) := by exact_mod_cast hZ
    have hNF : (squareWordWeight N : ℝ) < (squareWordWeight F : ℝ) := by
      exact_mod_cast hX.trans hF
    have h := strict_add
      (strict_add (homogeneous_strict (quartet_square_homogeneous X hpX)
          hNX)
        (homogeneous_strict (quartet_square_homogeneous Z hpZ) hNZ))
      (strict_neg (homogeneous_strict (quartet_square_homogeneous F hpF) hNF))
    simpa only [H,sub_eq_add_neg] using h
  have hne : quartetTerm N ≠ quartetTerm Y := by
    intro he
    have hm : FourRowHessenberg.fourMatch (Y 0) (Y 1) (Y 2) (Y 3)
        (N 0) (N 1) (N 2) (N 3) := by
      apply FourRowHessenberg.four_product_reading
        (hpY 0) (hpY 1) (hpY 2) (hpY 3) (hpN 0) (hpN 1) (hpN 2) (hpN 3)
      change quartetTerm Y = quartetTerm N
      exact he.symm
    change FourRowHessenberg.fourMatch r t u w s a v d at hm
    have h := quartic_internal_middle_locus a q.val q.val d r s t
      hr hs ht ha hb hc (by omega) hm
    rcases h with ⟨hsr,_,_⟩ | ⟨hst',_,_⟩
    · exact hrs hsr.symm
    · exact hst hst'
  have hbarA := bar_eq_complete_of_ne q a hane
  have hbarD := bar_eq_complete_of_ne q d (by omega)
  have hbarR := bar_eq_complete_of_ne q r (by omega)
  have hbarS := bar_eq_complete_of_ne q s (by omega)
  have hbarT := bar_eq_complete_of_ne q t (by omega)
  have hbarU := bar_eq_complete_of_ne q u (by dsimp [u]; omega)
  have hbarV := bar_eq_complete_of_ne q v (by dsimp [v]; omega)
  have hbarW := bar_eq_complete_of_ne q w (by dsimp [w]; omega)
  have hbarX := bar_eq_complete_of_ne q x (by dsimp [x]; omega)
  have hbarZ := bar_eq_complete_of_ne q y (by dsimp [y]; omega)
  have hbarF := bar_eq_complete_of_ne q f (by dsimp [f]; omega)
  dsimp [u,v,w,x,y,f] at hbarU hbarV hbarW hbarX hbarZ hbarF
  have hpoly : HessenbergExpansion.fourInterval (bar q) a q.val q.val d r s t =
      -quartetTerm N+quartetTerm Y+H := by
    simp only [HessenbergExpansion.fourInterval,bar_cut,hbarA,hbarD,hbarR,hbarS,hbarT,
      hbarU,hbarV,hbarW,hbarX,hbarZ,hbarF,zero_mul,mul_zero,zero_add,add_zero,zero_sub,sub_zero]
    dsimp [H,quartetTerm,N,Y,X,Z,F,u,v,w,x,y,f]
    ring
  rw [hpoly] at heps ⊢
  rw [mixed_pair_positive_initial Base.squareWeight.generatorWeight
    (quartetTerm N) (quartetTerm Y) H (squareWordWeight N) (squareWordWeight Y)
    (quartet_square_homogeneous N hpN) (quartet_square_homogeneous Y hpY)
    (quartet_augmentation_one N hpN) (quartet_augmentation_one Y hpY) hne hHigher heps]
  rfl

/-- A quartic primitive with both middle rows erased can have positive
square-initial augmentation only through its incomparable positive cut pair. -/
theorem restriction_BC_positive_initial {q : ℕ+} {P : Gluing.Profile 3}
    (hP : QComponent q P) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val)
    (hdegree : (canonicalPrimitive hP).totalDegree = 4)
    (heps : residualAugmentation
      (Base.initialForm Base.squareWeight.generatorWeight (restriction q P)) = 1) :
    Base.initialForm Base.squareWeight.generatorWeight (restriction q P) =
      complete (P.g 0)*complete (P.g 2)*
        complete ((P.r 0 : ℤ)+q.val-P.g 0)*complete ((q.val : ℤ)+P.r 3-P.g 2) := by
  have h0 : (0 : ℤ) < P.g 0 := by exact_mod_cast hP.gap_pos 0
  have h1 : (0 : ℤ) < P.g 1 := by exact_mod_cast hP.gap_pos 1
  have h2 : (0 : ℤ) < P.g 2 := by exact_mod_cast hP.gap_pos 2
  have hbot : q.val+P.g 2 < P.r 3 := by
    simpa [lastGap,Fin.sum_univ_succ] using hP.bottom
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨_,_,_,hA,hB,hC,hD⟩
  obtain ⟨_,hane,hrs,hst,_⟩ := four_quartic_nonextraction hP hdegree
  have hbi : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  have hci : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  rw [restriction_four_expansion q P hP.thick,hbi,hci] at heps ⊢
  exact double_middle_positive_initial q (P.r 0) (P.r 3) (P.g 0) (P.g 1) (P.g 2)
    h0 h1 h2 hA (by omega) (by omega) (by omega)
    (by exact_mod_cast hane) (by exact_mod_cast hrs hb) (by exact_mod_cast hst hc) heps

open Gluing HessenbergExpansion

private theorem middle_augmentation_bar (q : ℕ+) (k : ℤ) (hk : 0 < k) :
    residualAugmentation (bar q k) = if k = q.val then 0 else 1 := by
  by_cases h : k = q.val
  · rw [h, bar_cut, map_zero, if_pos rfl]
  · rw [bar_eq_complete_of_ne q k h, residualAugmentation_complete hk, if_neg h]

/-- Augmentation separates the BC and UC strata from the two ordinary
single-middle-row contact strata on the actual component. -/
theorem middle_row_contact_augmentation (q : ℕ+) (P : Profile 3)
    (hP : QComponent q P) (haq : P.r 0 ≠ q.val)
    (hcontact : P.r 1 = q.val ∨ P.r 2 = q.val) :
    residualAugmentation (restriction q P) =
      if P.r 1 = q.val ∧ P.r 2 = q.val then 1 else
      if P.r 2 = q.val ∧ (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val then -1 else 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hVne : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := by
    rcases hcontact with hbq | hcq <;> omega
  have hXne : (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 ≠ q.val := by
    rcases hcontact with hbq | hcq <;> omega
  have hA := middle_augmentation_bar q (P.r 0) (by exact_mod_cast P.r_pos 0)
  have hB := middle_augmentation_bar q (P.r 1) (by exact_mod_cast P.r_pos 1)
  have hC := middle_augmentation_bar q (P.r 2) (by exact_mod_cast P.r_pos 2)
  have hD := middle_augmentation_bar q (P.r 3) (by exact_mod_cast P.r_pos 3)
  rw [if_neg (by exact_mod_cast haq)] at hA
  rw [if_neg (by omega)] at hD
  have hgap (i : Fin 3) : residualAugmentation (bar q (P.g i)) = 1 := by
    rw [middle_augmentation_bar q _ (by exact_mod_cast hP.gap_pos i),
      if_neg (by exact_mod_cast hP.gap_ne i)]
  have hU := middle_augmentation_bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0) (by omega)
  have hV := middle_augmentation_bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1) (by omega)
  have hW := middle_augmentation_bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2) (by omega)
  have hX := middle_augmentation_bar q
    ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) (by omega)
  have hY := middle_augmentation_bar q
    ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) (by omega)
  have hF := middle_augmentation_bar q
    ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2) (by omega)
  rw [if_neg hVne] at hV
  rw [if_neg hXne] at hX
  rw [if_neg (by omega)] at hW hY hF
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval, map_add, map_sub, map_mul, hA, hB, hC, hD,
    hgap, hU, hV, hW, hX, hY, hF]
  split_ifs <;> norm_num <;> omega

/-- Actual equality transports the exceptional BC and UC contact predicates. -/
theorem middle_row_contact_status_eq (q : ℕ+) (P Q : Profile 3)
    (hP : QComponent q P) (hQ : QComponent q Q)
    (haP : P.r 0 ≠ q.val) (haQ : Q.r 0 ≠ q.val)
    (hcP : P.r 1 = q.val ∨ P.r 2 = q.val)
    (hcQ : Q.r 1 = q.val ∨ Q.r 2 = q.val)
    (he : restriction q P = restriction q Q) :
    ((P.r 1 = q.val ∧ P.r 2 = q.val) ↔ (Q.r 1 = q.val ∧ Q.r 2 = q.val)) ∧
    ((P.r 2 = q.val ∧ (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) ↔
      (Q.r 2 = q.val ∧ (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val)) := by
  have hp := P.g_lt_castSucc 0
  have hq := Q.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hp
  change Q.g 0 < Q.r 0 at hq
  have haug := congrArg residualAugmentation he
  rw [middle_row_contact_augmentation q P hP haP hcP,
    middle_row_contact_augmentation q Q hQ haQ hcQ] at haug
  split_ifs at haug <;> norm_num at haug <;> constructor <;> omega

end SkewJacobiNegative.Staircase
