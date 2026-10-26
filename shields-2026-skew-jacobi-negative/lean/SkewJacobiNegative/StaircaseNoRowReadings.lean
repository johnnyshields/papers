/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseSquareInitial
import SkewJacobiNegative.StaircaseQuadraticSwap

/-!
# Four-row readings with a surviving diagonal

The no-row-contact cases of `thm:staircase-residual-matching`.
Square initial forms recover the actual row multiset.  Endpoint and interval
data then determine the word up to rotation; augmentation separates the two
longer interval-contact strata.
-/

namespace SkewJacobiNegative.Staircase
open Gluing HessenbergExpansion

private theorem middle_swap_defect {R : Type*} [CommRing R] (h : ℤ → R)
    (a b c d r s t : ℤ) :
    fourInterval h a b c d r s t-fourInterval h a c b d r s t =
      (h r*h (a+b-r)-h a*h b)*(h t*h (c+d-t)-h c*h d)-
      (h r*h (a+c-r)-h a*h c)*(h t*h (b+d-t)-h b*h d) := by
  unfold fourInterval
  rw [show c+b-s=b+c-s by ring,
    show a+c+b-r-s=a+b+c-r-s by ring,
    show c+b+d-s-t=b+c+d-s-t by ring,
    show a+c+b+d-r-s-t=a+b+c+d-r-s-t by ring]
  ring

private theorem erased_B_bar (q : ℕ+) (r a b : ℤ) :
    eraseGenerator q (quadraticB r a b) =
      bar q r*bar q (a+b-r)-bar q a*bar q b := by
  simp only [quadraticB,map_sub,map_mul,bar]

/-- Equality with the same endpoints and gaps leaves only the allowed
whole-word rotation when the two middle rows are exchanged. -/
theorem actual_middle_swap_reading (q : ℕ+) (a b c d r s t : ℤ)
    (hr : 0<r) (ht : 0<t) (ha : r<a) (hbr : r<b) (hcr : r<c)
    (hbt : t<b) (hct : t<c) (hd : q.val+t<d)
    (ho : a-r≤d-t) (hrq : r≠q.val) (haq : a≠q.val)
    (hbq : b≠q.val) (hcq : c≠q.val) (htq : t≠q.val)
    (he : fourInterval (bar q) a b c d r s t=fourInterval (bar q) a c b d r s t) :
    b=c ∨ (r=t ∧ a=d) := by
  have hz := sub_eq_zero.mpr he
  rw [middle_swap_defect] at hz
  have hCD : bar q t*bar q (c+d-t)-bar q c*bar q d=quadraticB t c d := by
    rw [bar_eq_complete_of_ne q _ htq,bar_eq_complete_of_ne q _ (by omega),
      bar_eq_complete_of_ne q _ hcq,bar_eq_complete_of_ne q _ (by omega)]
    rfl
  have hBD : bar q t*bar q (b+d-t)-bar q b*bar q d=quadraticB t b d := by
    rw [bar_eq_complete_of_ne q _ htq,bar_eq_complete_of_ne q _ (by omega),
      bar_eq_complete_of_ne q _ hbq,bar_eq_complete_of_ne q _ (by omega)]
    rfl
  rw [hCD,hBD,←erased_B_bar q r a b,←erased_B_bar q r a c] at hz
  exact barred_quadratic_swap_key q a b c d r t hr ht ha hbr hcr hbt hct hd ho
    hrq haq hbq hcq (sub_eq_zero.mp hz)

/-- At a common middle or three-row interval contact, actual equality and
the recovered first endpoint determine the full word up to rotation. -/
theorem no_row_aligned_interval_reading (q : ℕ+) (P Q : Profile 3)
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hrowsP : ∀ i, P.r i≠q.val) (hrowsQ : ∀ i, Q.r i≠q.val)
    (long : Bool)
    (hContactP : (if long then (P.r 0:ℤ)+P.r 1+P.r 2-P.g 0-P.g 1
      else (P.r 1:ℤ)+P.r 2-P.g 1)=q.val)
    (hContactQ : (if long then (Q.r 0:ℤ)+Q.r 1+Q.r 2-Q.g 0-Q.g 1
      else (Q.r 1:ℤ)+Q.r 2-Q.g 1)=q.val)
    (hRow : (P.r 0:ℤ)=Q.r 0) (hFirst : (P.g 0:ℤ)=Q.g 0)
    (hOrient : (P.r 0:ℤ)-P.g 0≤(P.r 3:ℤ)-P.g 2)
    (he : restriction q P=restriction q Q) : P=Q ∨ P=Q.rotate := by
  have hA : P.r 0=Q.r 0 := Int.ofNat_inj.mp hRow
  have hR : P.g 0=Q.g 0 := Int.ofNat_inj.mp hFirst
  have hdomP := P.four_domain hP.thick.hessenberg
  have hdomQ := Q.four_domain hQ.thick.hessenberg
  rcases hdomP with ⟨hr,hs,ht,ha,hb,hc,hd⟩
  rcases hdomQ with ⟨hR',hS',hT',hA',hB',hC',hD'⟩
  have hbotP : q.val+P.g 2<P.r 3 := by
    simpa [lastGap,Fin.sum_univ_succ] using hP.bottom
  have hbotQ : q.val+Q.g 2<Q.r 3 := by
    simpa [lastGap,Fin.sum_univ_succ] using hQ.bottom
  have hsmallP : (P.r 1:ℤ)<q.val ∧ (P.r 2:ℤ)<q.val := by
    cases long <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hContactP <;> omega
  have hsmallQ : (Q.r 1:ℤ)<q.val ∧ (Q.r 2:ℤ)<q.val := by
    cases long <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hContactQ <;> omega
  have hDiag := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [restriction_square_initial_no_row_contact q P hrowsP,
    restriction_square_initial_no_row_contact q Q hrowsQ] at hDiag
  have hFour : complete (P.r 0)*complete (P.r 1)*complete (P.r 2)*complete (P.r 3)=
      complete (Q.r 0)*complete (Q.r 1)*complete (Q.r 2)*complete (Q.r 3) := by
    simpa [Fin.prod_univ_succ,mul_assoc] using hDiag
  simp only [←hA] at hFour
  have haNe : complete (P.r 0)≠0 :=
    (complete_ne_zero_iff _).mpr (by have h:=P.r_pos 0; omega)
  have hTriplePoly : complete (P.r 1)*complete (P.r 2)*complete (P.r 3)=
      complete (Q.r 1)*complete (Q.r 2)*complete (Q.r 3) := by
    apply mul_left_cancel₀ haNe
    simpa only [mul_assoc] using hFour
  have hTriple := residual_triple_product_reading
    (show (0:ℤ)<P.r 1 by exact_mod_cast P.r_pos 1)
    (show (0:ℤ)<P.r 2 by exact_mod_cast P.r_pos 2)
    (show (0:ℤ)<P.r 3 by exact_mod_cast P.r_pos 3)
    (show (0:ℤ)<Q.r 1 by exact_mod_cast Q.r_pos 1)
    (show (0:ℤ)<Q.r 2 by exact_mod_cast Q.r_pos 2)
    (show (0:ℤ)<Q.r 3 by exact_mod_cast Q.r_pos 3) hTriplePoly
  have hEnd : P.r 3=Q.r 3 ∧ (P.r 1:ℤ)+P.r 2=(Q.r 1:ℤ)+Q.r 2 := by
    unfold FourRowHessenberg.tripleMatch at hTriple
    rcases hTriple with ⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|
      ⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩ <;> constructor <;> omega
  obtain ⟨hD,hMiddleSum⟩ := hEnd
  have hS : P.g 1=Q.g 1 := by
    cases long <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hContactP hContactQ <;> omega
  obtain ⟨hFull,_⟩ := restriction_full_and_gap_eq hP hQ he
  rw [fullIndex_four,fullIndex_four] at hFull
  have hT : P.g 2=Q.g 2 := by omega
  have hdNe : complete (P.r 3)≠0 :=
    (complete_ne_zero_iff _).mpr (by have h:=P.r_pos 3; omega)
  have hPairPoly : complete (P.r 1)*complete (P.r 2)=
      complete (Q.r 1)*complete (Q.r 2) := by
    apply mul_right_cancel₀ hdNe
    simpa only [←hD] using hTriplePoly
  have hPair := complete_two_product_reading
    (show (0:ℤ)<P.r 1 by exact_mod_cast P.r_pos 1)
    (show (0:ℤ)<P.r 2 by exact_mod_cast P.r_pos 2)
    (show (0:ℤ)<Q.r 1 by exact_mod_cast Q.r_pos 1)
    (show (0:ℤ)<Q.r 2 by exact_mod_cast Q.r_pos 2) hPairPoly
  rcases hPair with ⟨hB,hC⟩|⟨hB,hC⟩
  · left
    apply Profile.ext
    · funext i; fin_cases i
      · exact hA
      · exact Int.ofNat_inj.mp hB
      · exact Int.ofNat_inj.mp hC
      · exact hD
    · funext i; fin_cases i
      · exact hR
      · exact hS
      · exact hT
  · have hqb : Q.r 1=P.r 2 := Int.ofNat_inj.mp hC.symm
    have hqc : Q.r 2=P.r 1 := Int.ofNat_inj.mp hB.symm
    have heFour := he
    rw [restriction_four_expansion q P hP.thick,restriction_four_expansion q Q hQ.thick] at heFour
    have hSwap : fourInterval (bar q) (P.r 0) (P.r 1) (P.r 2) (P.r 3)
        (P.g 0) (P.g 1) (P.g 2)=
        fourInterval (bar q) (P.r 0) (P.r 2) (P.r 1) (P.r 3)
        (P.g 0) (P.g 1) (P.g 2) := by
      simpa only [←hA,←hD,←hR,←hS,←hT,hqb,hqc] using heFour
    have hread := actual_middle_swap_reading q (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2)
      (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 2) ha (by omega) (by omega)
      (by omega) (by omega) (by omega) hOrient
      (by exact_mod_cast hP.gap_ne 0) (by exact_mod_cast hrowsP 0)
      (by exact_mod_cast hrowsP 1) (by exact_mod_cast hrowsP 2)
      (by exact_mod_cast hP.gap_ne 2) hSwap
    rcases hread with hbc|⟨hrt,had⟩
    · left
      have hbcN : P.r 1=P.r 2 := Int.ofNat_inj.mp hbc
      apply Profile.ext
      · funext i; fin_cases i
        · exact hA
        · exact hbcN.trans hqb.symm
        · exact hbcN.symm.trans hqc.symm
        · exact hD
      · funext i; fin_cases i
        · exact hR
        · exact hS
        · exact hT
    · right
      have hrtN : P.g 0=P.g 2 := Int.ofNat_inj.mp hrt
      have hadN : P.r 0=P.r 3 := Int.ofNat_inj.mp had
      apply Profile.ext
      · funext i; fin_cases i <;> simp only [Profile.rotate,Fin.rev,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
        · exact hadN.trans hD
        · exact hqc.symm
        · exact hqb.symm
        · exact hadN.symm.trans hA
      · funext i; fin_cases i <;> simp only [Profile.rotate,Fin.rev,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
        · exact hrtN.trans hT
        · exact hS
        · exact hrtN.symm.trans hR


private theorem augmentation_bar (q : ℕ+) (k : ℤ) (hk : 0<k) :
    residualAugmentation (bar q k) = if k=q.val then 0 else 1 := by
  by_cases h : k=q.val
  · rw [h,bar_cut,map_zero,if_pos rfl]
  · rw [bar_eq_complete_of_ne q k h,residualAugmentation_complete hk,if_neg h]

/-- On the surviving-diagonal stratum augmentation distinguishes middle from
three-row interval contacts, including simultaneous first-interval contact. -/
theorem no_row_contact_augmentation (q : ℕ+) (P : Profile 3)
    (hP : QComponent q P) (hrows : ∀ i, P.r i≠q.val) :
    residualAugmentation (restriction q P) =
      (if (P.r 1:ℤ)+P.r 2-P.g 1=q.val then 1 else 0)-
      (if (P.r 0:ℤ)+P.r 1+P.r 2-P.g 0-P.g 1=q.val then 1 else 0) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr,hs,ht,ha,hb,hc,hd⟩
  have hbottom : q.val+P.g 2<P.r 3 := by
    simpa [lastGap,Fin.sum_univ_succ] using hP.bottom
  have hrow (i : Fin 4) : residualAugmentation (bar q (P.r i))=1 := by
    rw [augmentation_bar q _ (by exact_mod_cast P.r_pos i),if_neg (by exact_mod_cast hrows i)]
  have hgap (i : Fin 3) : residualAugmentation (bar q (P.g i))=1 := by
    rw [augmentation_bar q _ (by exact_mod_cast hP.gap_pos i),if_neg (by exact_mod_cast hP.gap_ne i)]
  have hU := augmentation_bar q ((P.r 0:ℤ)+P.r 1-P.g 0) (by omega)
  have hV := augmentation_bar q ((P.r 1:ℤ)+P.r 2-P.g 1) (by omega)
  have hW := augmentation_bar q ((P.r 2:ℤ)+P.r 3-P.g 2) (by omega)
  have hX := augmentation_bar q ((P.r 0:ℤ)+P.r 1+P.r 2-P.g 0-P.g 1) (by omega)
  have hY := augmentation_bar q ((P.r 1:ℤ)+P.r 2+P.r 3-P.g 1-P.g 2) (by omega)
  have hF := augmentation_bar q ((P.r 0:ℤ)+P.r 1+P.r 2+P.r 3-P.g 0-P.g 1-P.g 2) (by omega)
  rw [if_neg (by omega)] at hW hY hF
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval,map_add,map_sub,map_mul,hrow,hgap,hU,hV,hW,hX,hY,hF]
  split_ifs <;> norm_num


/-- Equality transports both noninitial interval-contact predicates internally. -/
theorem no_row_contact_status_eq (q : ℕ+) (P Q : Profile 3)
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hrowsP : ∀ i, P.r i ≠ q.val) (hrowsQ : ∀ i, Q.r i ≠ q.val)
    (he : restriction q P = restriction q Q) :
    (((P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val) ↔
      ((Q.r 1 : ℤ) + Q.r 2 - Q.g 1 = q.val)) ∧
    (((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 = q.val) ↔
      ((Q.r 0 : ℤ) + Q.r 1 + Q.r 2 - Q.g 0 - Q.g 1 = q.val)) := by
  have hp := P.g_lt_castSucc 0
  have hq := Q.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hp
  change Q.g 0 < Q.r 0 at hq
  have haug := congrArg residualAugmentation he
  rw [no_row_contact_augmentation q P hP hrowsP,
    no_row_contact_augmentation q Q hQ hrowsQ] at haug
  split_ifs at haug <;> norm_num at haug <;> constructor <;> omega

end SkewJacobiNegative.Staircase
