/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseQuarticAlgebra

/-!
# Middle-row exchange for an erased quadratic product

The two-factor swap step in `thm:staircase-residual-matching`.
Private largest-index differentiation separates strict endpoint comparisons;
the tied comparison recovers both endpoint pairs.
-/

namespace SkewJacobiNegative.Staircase

private theorem pderiv_erase_commute (q j : ℕ+) (hjq : j ≠ q) (p : CompleteRing) :
    MvPolynomial.pderiv j (eraseGenerator q p) =
      eraseGenerator q (MvPolynomial.pderiv j p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [eraseGenerator]
  | add p r hp hr => simp only [map_add,hp,hr]
  | mul_X p i hp =>
    rw [map_mul,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,
      map_add,map_mul,map_mul,hp]
    have hX : MvPolynomial.pderiv j (eraseGenerator q (MvPolynomial.X i : CompleteRing)) =
        eraseGenerator q (MvPolynomial.pderiv j (MvPolynomial.X i : CompleteRing)) := by
      by_cases hi : i = q
      · subst i
        simp [eraseGenerator,MvPolynomial.pderiv_X,hjq,Ne.symm hjq]
      · by_cases hij : i = j
        · subst i
          simp [eraseGenerator,MvPolynomial.pderiv_X,hi]
        · simp [eraseGenerator,MvPolynomial.pderiv_X,hi,hij,Ne.symm hij]
    rw [hX]

private theorem erased_B_eq (q : ℕ+) (r a b : ℤ)
    (hrq : r ≠ q.val) (haq : a ≠ q.val) (hbq : b ≠ q.val) :
    eraseGenerator q (quadraticB r a b) =
      complete r*bar q (a+b-r)-complete a*complete b := by
  simp only [quadraticB,map_sub,map_mul]
  rw [eraseGenerator_complete q r,if_neg hrq,
    eraseGenerator_complete q a,if_neg haq,eraseGenerator_complete q b,if_neg hbq]
  rfl

private theorem erased_B_ne_zero (q : ℕ+) (r a b : ℤ)
    (hr : 0 < r) (ha : r < a) (hb : r < b)
    (hrq : r ≠ q.val) (haq : a ≠ q.val) (hbq : b ≠ q.val) :
    eraseGenerator q (quadraticB r a b) ≠ 0 := by
  by_cases hu : a+b-r = q.val
  · rw [erased_B_eq q r a b hrq haq hbq,hu,bar_cut,mul_zero,zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero
      ((complete_ne_zero_iff a).mpr (by omega)) ((complete_ne_zero_iff b).mpr (by omega)))
  · have he : eraseGenerator q (quadraticB r a b) = quadraticB r a b := by
      rw [erased_B_eq q r a b hrq haq hbq,bar_eq_complete_of_ne q _ hu]
      rfl
    rw [he]
    exact (quadraticB_irreducible r a b hr ha hb).ne_zero

private theorem erased_B_augmentation (q : ℕ+) (r a b : ℤ)
    (hr : 0 < r) (ha : r < a) (hb : r < b)
    (hrq : r ≠ q.val) (haq : a ≠ q.val) (hbq : b ≠ q.val) :
    residualAugmentation (eraseGenerator q (quadraticB r a b)) =
      if a+b-r = q.val then -1 else 0 := by
  rw [erased_B_eq q r a b hrq haq hbq,map_sub,map_mul,map_mul,
    residualAugmentation_complete hr,residualAugmentation_bar q (by omega),
    residualAugmentation_complete (show 0 < a by omega),
    residualAugmentation_complete (show 0 < b by omega)]
  split_ifs <;> norm_num

private theorem erased_B_above (q j : ℕ+) (hjq : j ≠ q) (r a b : ℤ)
    (hr : 0 < r) (ha : r < a) (hb : r < b) (hv : a+b-r < (j.val : ℤ)) :
    MvPolynomial.pderiv j (eraseGenerator q (quadraticB r a b)) = 0 := by
  rw [pderiv_erase_commute q j hjq,quadraticB_above r a b hr ha hb j hv,map_zero]

private theorem erased_B_top (q j : ℕ+) (hjq : j ≠ q) (r a b : ℤ)
    (hr : 0 < r) (ha : r < a) (hb : r < b) (hrq : r ≠ q.val)
    (hv : (j.val : ℤ) = a+b-r) :
    MvPolynomial.pderiv j (eraseGenerator q (quadraticB r a b)) = complete r := by
  rw [pderiv_erase_commute q j hjq,quadraticB_top r a b hr ha hb j hv,
    eraseGenerator_complete q r,if_neg hrq]

private theorem barred_swap_of_lt (q : ℕ+) (a b c d r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hbr : r < b) (hcr : r < c)
    (hbt : t < b) (hct : t < c) (hd : q.val+t < d)
    (ho : a-r ≤ d-t) (hrq : r ≠ q.val) (haq : a ≠ q.val)
    (hcq : c ≠ q.val)
    (he : eraseGenerator q (quadraticB r a b)*quadraticB t c d =
      eraseGenerator q (quadraticB r a c)*quadraticB t b d) (hcb : c < b) :
    r = t ∧ a = d := by
  have htd : t < d := by omega
  let j : ℕ+ := ⟨(b+d-t).toNat,by omega⟩
  have hj : (j.val : ℤ) = b+d-t := by dsimp [j]; omega
  have hjq : j ≠ q := by
    intro h
    have hv : (j.val : ℤ) = q.val := by rw [h]
    omega
  have hAB : a+b-r ≤ b+d-t := by omega
  have hAC : a+c-r < (j.val : ℤ) := by omega
  have hCD : c+d-t < (j.val : ℤ) := by omega
  have he' := congrArg (fun p : CompleteRing => MvPolynomial.pderiv j p) he
  by_cases hlt : a+b-r < b+d-t
  · rw [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,
      erased_B_above q j hjq r a b hr ha hbr (by omega),
      quadraticB_above t c d ht hct htd j hCD,
      erased_B_above q j hjq r a c hr ha hcr hAC,
      quadraticB_top t b d ht hbt htd j hj] at he'
    simp only [zero_mul,mul_zero,zero_add,add_zero] at he'
    exact ((mul_ne_zero (erased_B_ne_zero q r a c hr ha hcr hrq haq hcq)
      ((complete_ne_zero_iff t).mpr ht.le)) he'.symm).elim
  · have hEq : a+b-r = b+d-t := by omega
    rw [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul,
      erased_B_top q j hjq r a b hr ha hbr hrq (hj.trans hEq.symm),
      quadraticB_above t c d ht hct htd j hCD,
      erased_B_above q j hjq r a c hr ha hcr hAC,
      quadraticB_top t b d ht hbt htd j hj] at he'
    simp only [zero_mul,mul_zero,zero_add,add_zero] at he'
    have hDeriv : complete r*quadraticB t c d =
        complete t*eraseGenerator q (quadraticB r a c) := he'.trans (mul_comm _ _)
    have hu : a+c-r ≠ q.val := by
      intro h
      have hAug := congrArg residualAugmentation hDeriv
      rw [map_mul,map_mul,residualAugmentation_complete hr,residualAugmentation_complete ht,
        quadraticB_augmentation t c d ht hct htd,
        erased_B_augmentation q r a c hr ha hcr hrq haq hcq,if_pos h] at hAug
      norm_num at hAug
    have hErase : eraseGenerator q (quadraticB r a c) = quadraticB r a c := by
      rw [erased_B_eq q r a c hrq haq hcq,bar_eq_complete_of_ne q _ hu]
      rfl
    rw [hErase] at hDeriv
    have hRead := variable_times_B_reading r t c d t r a c hr ht ht hct htd hr ha hcr hDeriv
    exact ⟨hRead.1,by omega⟩

/-- The erased first quadratic and uncut second quadratic can exchange their
middle rows only by identity or the whole-word rotation.

**Differs from the paper's route.** Largest-index differentiation and the
coordinate-times-binomial classification recover the rows; the paper compares
the degrees of the specialized factors. -/
theorem barred_quadratic_swap_key (q : ℕ+) (a b c d r t : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hbr : r < b) (hcr : r < c)
    (hbt : t < b) (hct : t < c) (hd : q.val+t < d)
    (ho : a-r ≤ d-t) (hrq : r ≠ q.val) (haq : a ≠ q.val)
    (hbq : b ≠ q.val) (hcq : c ≠ q.val)
    (he : eraseGenerator q (quadraticB r a b)*quadraticB t c d =
      eraseGenerator q (quadraticB r a c)*quadraticB t b d) :
    b = c ∨ (r = t ∧ a = d) := by
  by_cases hbc : b = c
  · exact Or.inl hbc
  · right
    rcases lt_or_gt_of_ne hbc with hlt | hgt
    · exact barred_swap_of_lt q a c b d r t hr ht ha hcr hbr hct hbt hd ho
        hrq haq hbq he.symm hlt
    · exact barred_swap_of_lt q a b c d r t hr ht ha hbr hcr hbt hct hd ho
        hrq haq hcq he hgt

end SkewJacobiNegative.Staircase
