/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseQuarticAlgebra
import SkewJacobiNegative.StaircaseSquareInitial
import SkewJacobiNegative.StaircaseDeletedRowInitial
import SkewJacobiNegative.StaircaseIntervalSwap
import SkewJacobiNegative.StaircaseNoRowReadings

/-!
# Size-preserving staircase residual matching

Exact matching of actual normalized primitive factors on the four-row component domain.
-/

namespace SkewJacobiNegative.Staircase

open Gluing HessenbergExpansion

/-- Literal row/gap data equality, expressed as seven arithmetic equations. -/
def inventoryData (P : Profile 3) (R : Fin 4 → ℕ) (G : Fin 3 → ℕ) : Prop :=
  P.r 0 = R 0 ∧ P.r 1 = R 1 ∧ P.r 2 = R 2 ∧ P.r 3 = R 3 ∧
    P.g 0 = G 0 ∧ P.g 1 = G 1 ∧ P.g 2 = G 2

theorem inventoryData_eq_iff (P Q : Profile 3) :
    inventoryData P Q.r Q.g ↔ P = Q := by
  constructor
  · rintro ⟨h0, h1, h2, h3, g0, g1, g2⟩
    apply Profile.ext
    · funext i
      fin_cases i <;> assumption
    · funext i
      fin_cases i <;> assumption
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem inventoryData_rotate_iff (P : Profile 3)
    (R : Fin 4 → ℕ) (G : Fin 3 → ℕ) :
    inventoryData P.rotate R G ↔
      inventoryData P ![R 3, R 2, R 1, R 0] ![G 2, G 1, G 0] := by
  change
    (P.r 3 = R 0 ∧ P.r 2 = R 1 ∧ P.r 1 = R 2 ∧ P.r 0 = R 3 ∧
      P.g 2 = G 0 ∧ P.g 1 = G 1 ∧ P.g 0 = G 2) ↔
    (P.r 0 = R 3 ∧ P.r 1 = R 2 ∧ P.r 2 = R 1 ∧ P.r 3 = R 0 ∧
      P.g 0 = G 2 ∧ P.g 1 = G 1 ∧ P.g 2 = G 0)
  constructor <;> rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
  all_goals exact ⟨h3, h2, h1, h0, h6, h5, h4⟩


def inventoryOrbit (P : Profile 3) (R : Fin 4 → ℕ) (G : Fin 3 → ℕ) : Prop :=
  inventoryData P R G ∨ inventoryData P ![R 3, R 2, R 1, R 0] ![G 2, G 1, G 0]

theorem inventoryOrbit_iff (P A : Profile 3) :
    inventoryOrbit P A.r A.g ↔ inRotationOrbit P A := by
  have hrot : inventoryData P ![A.r 3, A.r 2, A.r 1, A.r 0]
      ![A.g 2, A.g 1, A.g 0] ↔ P = A.rotate := by
    simpa [inventoryData, Profile.rotate] using inventoryData_eq_iff P A.rotate
  exact or_congr (inventoryData_eq_iff P A) hrot

private theorem inventoryOrbit_rotate_iff (P : Profile 3)
    (R : Fin 4 → ℕ) (G : Fin 3 → ℕ) :
    inventoryOrbit P.rotate R G ↔ inventoryOrbit P R G := by
  simp only [inventoryOrbit, inventoryData_rotate_iff]
  change
    (inventoryData P ![R 3, R 2, R 1, R 0] ![G 2, G 1, G 0] ∨ inventoryData P R G) ↔
      (inventoryData P R G ∨ inventoryData P ![R 3, R 2, R 1, R 0] ![G 2, G 1, G 0])
  exact or_comm


def inventoryResidualData (q : ℕ+) (P Q : Profile 3) (a r s : ℕ) : Prop :=
  r + s < a ∧ r + s < q.val ∧ 0 < r ∧ 0 < s ∧ r ≠ s ∧ a ≠ q.val ∧
    ((inventoryOrbit P ![a, q.val, a, a + 2 * q.val - r - s] ![r, s, r] ∧
      inventoryOrbit Q ![a, a + q.val - s, q.val, a + q.val - r] ![r, r, s]) ∨
     (inventoryOrbit P ![a, a + q.val - s, q.val, a + q.val - r] ![r, r, s] ∧
      inventoryOrbit Q ![a, q.val, a, a + 2 * q.val - r - s] ![r, s, r]))

private theorem inventoryResidualData_rotate_left_iff
    (q : ℕ+) (P Q : Profile 3) (a r s : ℕ) :
    inventoryResidualData q P.rotate Q a r s ↔ inventoryResidualData q P Q a r s := by
  simp only [inventoryResidualData, inventoryOrbit_rotate_iff]

private theorem inventoryResidualData_rotate_right_iff
    (q : ℕ+) (P Q : Profile 3) (a r s : ℕ) :
    inventoryResidualData q P Q.rotate a r s ↔ inventoryResidualData q P Q a r s := by
  simp only [inventoryResidualData, inventoryOrbit_rotate_iff]

theorem inventoryResidualData_quartet {q : ℕ+} {P Q : Profile 3} {a r s : ℕ}
    (h : inventoryResidualData q P Q a r s) : quarticResidualQuartet q P Q := by
  rcases h with ⟨ha, hq, hr, hs, hrs, haq, hrel⟩
  refine ⟨a, r, s, ha, hq, hr, hs, hrs, haq, ?_⟩
  let A := residualFamilyA a q.val r s ha hq
  let B := residualFamilyB a q.val r s ha hq
  change ((inventoryOrbit P A.r A.g ∧ inventoryOrbit Q B.r B.g) ∨
    (inventoryOrbit P B.r B.g ∧ inventoryOrbit Q A.r A.g)) at hrel
  change ((inRotationOrbit P A ∧ inRotationOrbit Q B) ∨
    (inRotationOrbit P B ∧ inRotationOrbit Q A))
  simpa only [inventoryOrbit_iff] using hrel

/-- The four witness choices correspond to A, rotated A, B, and rotated B.
They are actual row/gap coordinates, not a bounded parameter census. -/
def inventoryCoordinateAlternatives (q : ℕ+) (P Q : Profile 3) : Prop :=
  inventoryData P Q.r Q.g ∨ inventoryData P Q.rotate.r Q.rotate.g ∨
    inventoryResidualData q P Q (P.r 0) (P.g 0) (P.g 1) ∨
    inventoryResidualData q P Q (P.r 3) (P.g 2) (P.g 1) ∨
    inventoryResidualData q P Q (P.r 0) (P.g 0) (P.g 2) ∨
    inventoryResidualData q P Q (P.r 3) (P.g 2) (P.g 0)

private theorem inventoryResidualData_to_alternatives
    {q : ℕ+} {P Q : Profile 3} {a r s : ℕ}
    (h : inventoryResidualData q P Q a r s) :
    inventoryCoordinateAlternatives q P Q := by
  have hp := h.2.2.2.2.2.2
  rcases hp with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rcases hp with hp | hp
    · have h0 : P.r 0 = a := hp.1
      have g0 : P.g 0 = r := hp.2.2.2.2.1
      have g1 : P.g 1 = s := hp.2.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inl (by simpa only [h0, g0, g1] using h)))
    · have h3 : P.r 3 = a := hp.2.2.2.1
      have g2 : P.g 2 = r := hp.2.2.2.2.2.2
      have g1 : P.g 1 = s := hp.2.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [h3, g2, g1] using h))))
  · rcases hp with hp | hp
    · have h0 : P.r 0 = a := hp.1
      have g0 : P.g 0 = r := hp.2.2.2.2.1
      have g2 : P.g 2 = s := hp.2.2.2.2.2.2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [h0, g0, g2] using h)))))
    · have h3 : P.r 3 = a := hp.2.2.2.1
      have g2 : P.g 2 = r := hp.2.2.2.2.2.2
      have g0 : P.g 0 = s := hp.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [h3, g2, g0] using h)))))

private theorem inventoryResidualData_reverse
    {q : ℕ+} {P Q : Profile 3} {a r s : ℕ}
    (h : inventoryResidualData q P Q a r s) : inventoryResidualData q Q P a r s := by
  rcases h with ⟨ha, hq, hr, hs, hne, haq, hrel⟩
  refine ⟨ha, hq, hr, hs, hne, haq, ?_⟩
  rcases hrel with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact Or.inr ⟨hq, hp⟩
  · exact Or.inl ⟨hq, hp⟩

private theorem inventoryCoordinateAlternatives_reverse
    {q : ℕ+} {P Q : Profile 3}
    (h : inventoryCoordinateAlternatives q P Q) :
    inventoryCoordinateAlternatives q Q P := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl ((inventoryData_eq_iff Q P).mpr ((inventoryData_eq_iff P Q).mp h).symm)
  · have hh := congrArg Profile.rotate ((inventoryData_eq_iff P Q.rotate).mp h)
    have hq : Q = P.rotate := by simpa only [Profile.rotate_rotate] using hh.symm
    exact Or.inr (Or.inl ((inventoryData_eq_iff Q P.rotate).mpr hq))
  all_goals exact inventoryResidualData_to_alternatives (inventoryResidualData_reverse h)

theorem inventoryCoordinateAlternatives_residual {q : ℕ+} {P Q : Profile 3}
    (h : inventoryCoordinateAlternatives q P Q) : quarticResidualAlternatives q P Q := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl ((inventoryData_eq_iff P Q).mp h)
  · exact Or.inr (Or.inl ((inventoryData_eq_iff P Q.rotate).mp h))
  all_goals exact Or.inr (Or.inr (Or.inr (inventoryResidualData_quartet h)))

private theorem inventoryCoordinateAlternatives_unrotate_left
    {q : ℕ+} {P Q : Profile 3}
    (h : inventoryCoordinateAlternatives q P.rotate Q) :
    inventoryCoordinateAlternatives q P Q := by
  rcases h with h | h | h | h | h | h
  · have hh := congrArg Profile.rotate ((inventoryData_eq_iff P.rotate Q).mp h)
    have hp : P = Q.rotate := by simpa only [Profile.rotate_rotate] using hh
    exact Or.inr (Or.inl ((inventoryData_eq_iff P Q.rotate).mpr hp))
  · have hh := congrArg Profile.rotate ((inventoryData_eq_iff P.rotate Q.rotate).mp h)
    have hp : P = Q := by simpa only [Profile.rotate_rotate] using hh
    exact Or.inl ((inventoryData_eq_iff P Q).mpr hp)
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    simpa [Profile.rotate, Fin.rev] using
      (inventoryResidualData_rotate_left_iff q P Q _ _ _).mp h
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    simpa [Profile.rotate, Fin.rev] using
      (inventoryResidualData_rotate_left_iff q P Q _ _ _).mp h
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    simpa [Profile.rotate, Fin.rev] using
      (inventoryResidualData_rotate_left_iff q P Q _ _ _).mp h
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    simpa [Profile.rotate, Fin.rev] using
      (inventoryResidualData_rotate_left_iff q P Q _ _ _).mp h

private theorem inventoryCoordinateAlternatives_unrotate_right
    {q : ℕ+} {P Q : Profile 3}
    (h : inventoryCoordinateAlternatives q P Q.rotate) :
    inventoryCoordinateAlternatives q P Q := by
  rcases h with h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · have hp := (inventoryData_eq_iff P Q.rotate.rotate).mp h
    apply Or.inl
    apply (inventoryData_eq_iff P Q).mpr
    simpa only [Profile.rotate_rotate] using hp
  · exact Or.inr (Or.inr (Or.inl
      ((inventoryResidualData_rotate_right_iff q P Q _ _ _).mp h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ((inventoryResidualData_rotate_right_iff q P Q _ _ _).mp h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((inventoryResidualData_rotate_right_iff q P Q _ _ _).mp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((inventoryResidualData_rotate_right_iff q P Q _ _ _).mp h)))))

private theorem rows_off_cut_of_middle_off {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val)
    (hb : P.r 1 ≠ q.val) (hc : P.r 2 ≠ q.val) : ∀ i, P.r i ≠ q.val := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · have hbottom : q.val + P.g 2 < P.r 3 := by
      simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
    change P.r 3 ≠ q.val
    omega

/-- A surviving diagonal has square-initial augmentation one in every order. -/
theorem restriction_initial_augmentation_one {n : ℕ} (q : ℕ+) (P : Profile n)
    (hrows : ∀ i, P.r i ≠ q.val) :
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight (restriction q P)) =
      1 := by
  rw [restriction_square_initial_no_row_contact q P hrows, map_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact residualAugmentation_complete (by exact_mod_cast P.r_pos i)

/-- A surviving square-initial diagonal cannot match a deleted middle row. -/
theorem restriction_no_row_middleB_ne {n : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile 3}
    (hrows : ∀ i, P.r i ≠ q.val) (hQ : QComponent q Q)
    (hb : Q.r 1 = q.val) (ha : Q.r 0 ≠ q.val) (hc : Q.r 2 ≠ q.val) :
    restriction q P ≠ restriction q Q := by
  intro he
  have hh := congrArg (fun p : CompleteRing =>
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight p)) he
  rw [restriction_initial_augmentation_one q P hrows] at hh
  rcases restriction_middleB_initial_negative hQ hb ha hc with hn | hn
  · rw [hn] at hh
    norm_num at hh
  · rw [hn] at hh
    norm_num at hh

/-- The same sign separation includes every single third-row contact, including UC. -/
theorem restriction_no_row_middleC_ne {n : ℕ} {q : ℕ+}
    {P : Profile n} {Q : Profile 3}
    (hrows : ∀ i, P.r i ≠ q.val) (hQ : QComponent q Q)
    (hc : Q.r 2 = q.val) (ha : Q.r 0 ≠ q.val) (hb : Q.r 1 ≠ q.val) :
    restriction q P ≠ restriction q Q := by
  intro he
  have hh := congrArg (fun p : CompleteRing =>
    residualAugmentation (Base.initialForm Base.squareWeight.generatorWeight p)) he
  rw [restriction_initial_augmentation_one q P hrows] at hh
  rcases restriction_middleC_initial_negative hQ hc ha hb with hn | hn
  · rw [hn] at hh
    norm_num at hh
  · rw [hn] at hh
    norm_num at hh

/-- Equality of actual restrictions with surviving diagonals supplies the
four-row monomial reading before any placement of the gaps is assumed. -/
theorem restriction_four_rows_match {q : ℕ+} {P Q : Profile 3}
    (hP : ∀ i, P.r i ≠ q.val) (hQ : ∀ i, Q.r i ≠ q.val)
    (he : restriction q P = restriction q Q) :
    FourRowHessenberg.fourMatch (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (Q.r 0) (Q.r 1) (Q.r 2) (Q.r 3) := by
  have hh := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [restriction_square_initial_no_row_contact q P hP,
    restriction_square_initial_no_row_contact q Q hQ] at hh
  apply FourRowHessenberg.four_product_reading
    (by exact_mod_cast P.r_pos 0) (by exact_mod_cast P.r_pos 1)
    (by exact_mod_cast P.r_pos 2) (by exact_mod_cast P.r_pos 3)
    (by exact_mod_cast Q.r_pos 0) (by exact_mod_cast Q.r_pos 1)
    (by exact_mod_cast Q.r_pos 2) (by exact_mod_cast Q.r_pos 3)
  simpa [Fin.prod_univ_succ, mul_assoc] using hh

/-- Augmented derivative of one erased generator: the indicator of its index, off the cut. -/
theorem quarticLow_aug_deriv_bar (q j : ℕ+) (k : ℤ) :
    residualAugmentation (MvPolynomial.pderiv j (bar q k)) =
      if j ≠ q ∧ k = (j.val : ℤ) then 1 else 0 := by
  by_cases hjq : j = q
  · have hz : MvPolynomial.pderiv j (bar q k) = 0 := by
      rw [bar, eraseGenerator_complete]
      split_ifs with hk
      · simp
      · rw [residual_pderiv_complete, if_neg]
        intro he
        exact hk (he.trans (by rw [hjq]))
    rw [hz, map_zero,
      if_neg (show ¬ (j ≠ q ∧ k = (j.val : ℤ)) from fun hh => hh.1 hjq)]
  · rw [residual_pderiv_bar q j hjq k]
    by_cases hk : k = (j.val : ℤ)
    · rw [if_pos hk, if_pos (And.intro hjq hk), map_one]
    · rw [if_neg hk,
        if_neg (show ¬ (j ≠ q ∧ k = (j.val : ℤ)) from fun hh => hk hh.2), map_zero]

/-- A positive generator other than the cut has augmentation one. -/
theorem quarticLow_aug_bar_one (q : ℕ+) {k : ℤ} (hk : 0 < k) (hne : k ≠ (q.val : ℤ)) :
    residualAugmentation (bar q k) = 1 := by
  rw [residualAugmentation_bar q hk, if_neg hne]

/-- The cut generator has augmentation zero. -/
theorem quarticLow_aug_bar_zero (q : ℕ+) {k : ℤ} (hk : 0 < k) (he : k = (q.val : ℤ)) :
    residualAugmentation (bar q k) = 0 := by
  rw [residualAugmentation_bar q hk, if_pos he]

/-- Quartic low-derivative interval: the augmented derivative of the actual restriction at
`j ≤ g₂` is `-[g₂ = j]`, under the isolated `u`-contact `u = q`, `r₂ ≠ q`, and `v ≠ q`.
The rows `r₁ ≠ q` and `x ≠ q` are derived from `u = q` and thickness. -/
theorem quarticLow_interval (q : ℕ+) (P : Profile 3) (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = (q.val : ℤ))
    (hc : P.r 2 ≠ q.val) (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ (q.val : ℤ))
    (j : ℕ+) (hj : (j.val : ℤ) ≤ P.g 2) :
    residualAugmentation (MvPolynomial.pderiv j (restriction q P)) =
      -(if (P.g 2 : ℤ) = (j.val : ℤ) then 1 else 0) := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have h12 := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at h12
  have e0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hb : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hq : 0 < q.val := q.pos
  have hr0 := P.r_pos 0
  have hr1 := P.r_pos 1
  have hr2 := P.r_pos 2
  have hr3 := P.r_pos 3
  have hg0 := hP.gap_pos 0
  have hg1 := hP.gap_pos 1
  have hg2 := hP.gap_pos 2
  have hn0 := hP.gap_ne 0
  have hn1 := hP.gap_ne 1
  have hn2 := hP.gap_ne 2
  -- Augmentation of every factor index occurring in the eight terms.
  -- Only `u` equals `q`; `r₁ ≠ q` since `u = q` and `r₀ > g₀`.
  have hFA : residualAugmentation (bar q (P.r 0 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFB : residualAugmentation (bar q (P.r 1 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFC : residualAugmentation (bar q (P.r 2 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFD : residualAugmentation (bar q (P.r 3 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFR : residualAugmentation (bar q (P.g 0 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFS : residualAugmentation (bar q (P.g 1 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFTt : residualAugmentation (bar q (P.g 2 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFu : residualAugmentation (bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0)) = 0 :=
    quarticLow_aug_bar_zero q (by omega) hu
  have hFv : residualAugmentation (bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1)) = 1 :=
    quarticLow_aug_bar_one q (by omega) hv
  have hFw : residualAugmentation (bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFx : residualAugmentation
      (bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFy : residualAugmentation
      (bar q ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFT : residualAugmentation
      (bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  -- The remaining high-index indicators vanish below the last gap; the other
  -- indicators cancel in the collected derivative.
  have nU : ¬ (j ≠ q ∧ (P.r 0 : ℤ) + P.r 1 - P.g 0 = (j.val : ℤ)) :=
    fun hh => hh.1 (PNat.coe_injective (by omega))
  have nC : ¬ (j ≠ q ∧ (P.r 2 : ℤ) = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nD : ¬ (j ≠ q ∧ (P.r 3 : ℤ) = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nv : ¬ (j ≠ q ∧ (P.r 1 : ℤ) + P.r 2 - P.g 1 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nw : ¬ (j ≠ q ∧ (P.r 2 : ℤ) + P.r 3 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nx : ¬ (j ≠ q ∧
      (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have ny : ¬ (j ≠ q ∧
      (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nT : ¬ (j ≠ q ∧
      (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  -- The last-gap indicator: `j ≠ q` is automatic once `g₂ = j`, since `g₂ ≠ q`.
  have hTt : (if j ≠ q ∧ (P.g 2 : ℤ) = (j.val : ℤ) then (1 : ℚ) else 0) =
      if (P.g 2 : ℤ) = (j.val : ℤ) then 1 else 0 := by
    by_cases h : (P.g 2 : ℤ) = (j.val : ℤ)
    · have hjq : j ≠ q := by
        intro he
        apply hn2
        have h' : (j.val : ℤ) = (q.val : ℤ) := by rw [he]
        omega
      rw [if_pos (And.intro hjq h), if_pos h]
    · rw [if_neg (show ¬ (j ≠ q ∧ (P.g 2 : ℤ) = (j.val : ℤ)) from fun hh => h hh.2),
        if_neg h]
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval, map_add, map_sub, MvPolynomial.pderiv_mul, map_mul,
    quarticLow_aug_deriv_bar, hFA, hFB, hFC, hFD, hFR, hFS, hFTt, hFu, hFv, hFw, hFx, hFy, hFT,
    if_neg nU, if_neg nC, if_neg nD, if_neg nv, if_neg nw, if_neg nx, if_neg ny, if_neg nT, hTt]
  ring

/-- Single-middle contact at the second row: `P.r 1 = q`, with `P.r 0` and `P.r 2` not `q`.
For every `j ≤ P.g 2`, the augmented derivative of the actual restriction is `[P.g 2 = j]`. -/
theorem quarticMid_middleB (q : ℕ+) {P : Profile 3} (hP : QComponent q P)
    (hb : P.r 1 = q.val) (ha : P.r 0 ≠ q.val) (hc : P.r 2 ≠ q.val)
    (j : ℕ+) (hj : (j.val : ℤ) ≤ (P.g 2 : ℤ)) :
    residualAugmentation (MvPolynomial.pderiv j (restriction q P)) =
      if (P.g 2 : ℤ) = (j.val : ℤ) then 1 else 0 := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have h12 := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at h12
  have e0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hbot : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hq : 0 < q.val := q.pos
  have hg0 := hP.gap_pos 0
  have hg1 := hP.gap_pos 1
  have hg2 := hP.gap_pos 2
  have hr0 := P.r_pos 0
  have hr2 := P.r_pos 2
  have hr3 := P.r_pos 3
  have hn0 := hP.gap_ne 0
  have hn1 := hP.gap_ne 1
  have hn2 := hP.gap_ne 2
  have hb' : (P.r 1 : ℤ) = (q.val : ℤ) := by exact_mod_cast hb
  have hR1 : bar q (P.r 1 : ℤ) = 0 := by rw [hb', bar_cut]
  -- Augmentations of every factor index occurring in the eight terms.
  have hFA : residualAugmentation (bar q (P.r 0 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFC : residualAugmentation (bar q (P.r 2 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFD : residualAugmentation (bar q (P.r 3 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFR : residualAugmentation (bar q (P.g 0 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFS : residualAugmentation (bar q (P.g 1 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFT2 : residualAugmentation (bar q (P.g 2 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFu : residualAugmentation (bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFv : residualAugmentation (bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFw : residualAugmentation (bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFx : residualAugmentation
      (bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFy : residualAugmentation
      (bar q ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFT : residualAugmentation
      (bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  -- Derivative indicators of the high atoms vanish for `j ≤ g₂`: each exceeds `g₂`.
  have nC : ¬ (j ≠ q ∧ (P.r 2 : ℤ) = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nD : ¬ (j ≠ q ∧ (P.r 3 : ℤ) = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nw : ¬ (j ≠ q ∧ (P.r 1 : ℤ) + P.r 2 - P.g 1 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nx : ¬ (j ≠ q ∧ (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have ny : ¬ (j ≠ q ∧ (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nW : ¬ (j ≠ q ∧ (P.r 2 : ℤ) + P.r 3 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nT : ¬ (j ≠ q ∧
      (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  -- The last-gap indicator: `j ≠ q` is automatic once `g₂ = j`, since `g₂ ≠ q`.
  have hTt : (if j ≠ q ∧ (P.g 2 : ℤ) = (j.val : ℤ) then (1 : ℚ) else 0) =
      if (P.g 2 : ℤ) = (j.val : ℤ) then 1 else 0 := by
    by_cases h : (P.g 2 : ℤ) = (j.val : ℤ)
    · have hjq : j ≠ q := by
        intro he
        apply hn2
        have h' : (j.val : ℤ) = (q.val : ℤ) := by rw [he]
        omega
      rw [if_pos (And.intro hjq h), if_pos h]
    · rw [if_neg (show ¬ (j ≠ q ∧ (P.g 2 : ℤ) = (j.val : ℤ)) from fun hh => h hh.2),
        if_neg h]
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul, map_mul, hR1,
    map_zero, zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero,
    quarticLow_aug_deriv_bar, hFA, hFC, hFD, hFR, hFS, hFT2, hFu, hFv, hFw, hFx, hFy, hFT,
    if_neg nC, if_neg nD, if_neg nw, if_neg nx, if_neg ny, if_neg nW, if_neg nT, hTt]
  ring

/-- Single-middle contact at the third row: `P.r 2 = q`, with `P.r 1`, `P.r 0` and
`P.r 0 + P.r 1 - P.g 0` not `q`.  For every `j ≤ P.g 0`, the augmented derivative of the actual
restriction is `[P.g 0 = j]`. -/
theorem quarticMid_middleC (q : ℕ+) {P : Profile 3} (hP : QComponent q P)
    (hc : P.r 2 = q.val) (hb : P.r 1 ≠ q.val) (ha : P.r 0 ≠ q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ (q.val : ℤ))
    (j : ℕ+) (hj : (j.val : ℤ) ≤ (P.g 0 : ℤ)) :
    residualAugmentation (MvPolynomial.pderiv j (restriction q P)) =
      if (P.g 0 : ℤ) = (j.val : ℤ) then 1 else 0 := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have h12 := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at h12
  have e0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hbot : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hq : 0 < q.val := q.pos
  have hg0 := hP.gap_pos 0
  have hg1 := hP.gap_pos 1
  have hg2 := hP.gap_pos 2
  have hr0 := P.r_pos 0
  have hr1 := P.r_pos 1
  have hr3 := P.r_pos 3
  have hn0 := hP.gap_ne 0
  have hn1 := hP.gap_ne 1
  have hn2 := hP.gap_ne 2
  have hc' : (P.r 2 : ℤ) = (q.val : ℤ) := by exact_mod_cast hc
  have hR2 : bar q (P.r 2 : ℤ) = 0 := by rw [hc', bar_cut]
  -- Augmentations of every factor index occurring in the eight terms.
  have hFA : residualAugmentation (bar q (P.r 0 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFB : residualAugmentation (bar q (P.r 1 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFD : residualAugmentation (bar q (P.r 3 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFR : residualAugmentation (bar q (P.g 0 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFS : residualAugmentation (bar q (P.g 1 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFT2 : residualAugmentation (bar q (P.g 2 : ℤ)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFu : residualAugmentation (bar q ((P.r 0 : ℤ) + P.r 1 - P.g 0)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFv : residualAugmentation (bar q ((P.r 1 : ℤ) + P.r 2 - P.g 1)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFw : residualAugmentation (bar q ((P.r 2 : ℤ) + P.r 3 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFx : residualAugmentation
      (bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFy : residualAugmentation
      (bar q ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  have hFT : residualAugmentation
      (bar q ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2)) = 1 :=
    quarticLow_aug_bar_one q (by omega) (by omega)
  -- Derivative indicators of the atoms that do not cancel formally vanish for `j ≤ g₀`.
  have nr0 : ¬ (j ≠ q ∧ (P.r 0 : ℤ) = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nr1 : ¬ (j ≠ q ∧ (P.r 1 : ℤ) = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nw : ¬ (j ≠ q ∧ (P.r 1 : ℤ) + P.r 2 - P.g 1 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nu : ¬ (j ≠ q ∧ (P.r 0 : ℤ) + P.r 1 - P.g 0 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nx : ¬ (j ≠ q ∧ (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have ny : ¬ (j ≠ q ∧ (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  have nT : ¬ (j ≠ q ∧
      (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 = (j.val : ℤ)) :=
    fun hh => by have h2 := hh.2; clear hh; omega
  -- The first-gap indicator: `j ≠ q` is automatic once `g₀ = j`, since `g₀ ≠ q`.
  have hTt : (if j ≠ q ∧ (P.g 0 : ℤ) = (j.val : ℤ) then (1 : ℚ) else 0) =
      if (P.g 0 : ℤ) = (j.val : ℤ) then 1 else 0 := by
    by_cases h : (P.g 0 : ℤ) = (j.val : ℤ)
    · have hjq : j ≠ q := by
        intro he
        apply hn0
        have h' : (j.val : ℤ) = (q.val : ℤ) := by rw [he]
        omega
      rw [if_pos (And.intro hjq h), if_pos h]
    · rw [if_neg (show ¬ (j ≠ q ∧ (P.g 0 : ℤ) = (j.val : ℤ)) from fun hh => h hh.2),
        if_neg h]
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval, map_add, map_sub, map_neg, MvPolynomial.pderiv_mul, map_mul, hR2,
    map_zero, zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero,
    quarticLow_aug_deriv_bar, hFA, hFB, hFD, hFR, hFS, hFT2, hFu, hFv, hFw, hFx, hFy, hFT,
    if_neg nr0, if_neg nr1, if_neg nw, if_neg nu, if_neg nx, if_neg ny, if_neg nT, hTt]
  ring


/-- The indicator `δ_j(k) = [k = j]` of a generator label, as an augmentation coefficient. -/
abbrev quarticDelta (j : ℕ+) (k : ℤ) : ℚ := if k = (j.val : ℤ) then 1 else 0

/-- Augmented derivative of one erased generator, with the `j ≠ q` conjunct removed for an
index different from the cut. -/
theorem quarticFull_ind (q j : ℕ+) {k : ℤ} (hk : k ≠ (q.val : ℤ)) :
    (if j ≠ q ∧ k = (j.val : ℤ) then (1 : ℚ) else 0) = quarticDelta j k := by
  by_cases h : k = (j.val : ℤ)
  · have hjq : j ≠ q := fun he => hk (h.trans (by rw [he]))
    rw [if_pos ⟨hjq, h⟩, quarticDelta, if_pos h]
  · rw [if_neg (fun hh => h hh.2), quarticDelta, if_neg h]

/-- Augmented derivative of a product of four non-cut barred generators: the sum of the
indicators of its four labels, with multiplicity. -/
theorem quarticFull_aug_four (q j : ℕ+) {k1 k2 k3 k4 : ℤ}
    (p1 : 0 < k1) (p2 : 0 < k2) (p3 : 0 < k3) (p4 : 0 < k4)
    (n1 : k1 ≠ (q.val : ℤ)) (n2 : k2 ≠ (q.val : ℤ))
    (n3 : k3 ≠ (q.val : ℤ)) (n4 : k4 ≠ (q.val : ℤ)) :
    residualAugmentation (MvPolynomial.pderiv j (bar q k1 * bar q k2 * bar q k3 * bar q k4)) =
      quarticDelta j k1 + quarticDelta j k2 + quarticDelta j k3 + quarticDelta j k4 := by
  have a1 := quarticLow_aug_bar_one q p1 n1
  have a2 := quarticLow_aug_bar_one q p2 n2
  have a3 := quarticLow_aug_bar_one q p3 n3
  have a4 := quarticLow_aug_bar_one q p4 n4
  simp only [MvPolynomial.pderiv_mul, map_add, map_mul, quarticLow_aug_deriv_bar,
    a1, a2, a3, a4, quarticFull_ind q j n1, quarticFull_ind q j n2,
    quarticFull_ind q j n3, quarticFull_ind q j n4]
  ring

/-- Full right-contact histogram.  Under `P.r 2 = q`, with `P.r 0`, `P.r 1` and
`u = P.r 0 + P.r 1 - P.g 0` not equal to `q`, every positive label `j` has augmented
derivative of the actual restriction equal to the signed histogram of the rows and gaps. -/
theorem quarticFull_right_derivative (q : ℕ+) (P : Profile 3) (hP : QComponent q P)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 ≠ q.val) (hc : P.r 2 = q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ (q.val : ℤ)) (j : ℕ+) :
    residualAugmentation (MvPolynomial.pderiv j (restriction q P)) =
      quarticDelta j ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) +
      quarticDelta j ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) -
      quarticDelta j ((P.r 1 : ℤ) + P.r 2 - P.g 1) -
      quarticDelta j ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2) +
      quarticDelta j (P.g 0 : ℤ) +
      quarticDelta j ((P.r 0 : ℤ) + P.r 1 - P.g 0) -
      quarticDelta j (P.r 0 : ℤ) -
      quarticDelta j (P.r 1 : ℤ) := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have h12 := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at h12
  have e0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hbot : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hq : 0 < q.val := q.pos
  have hr0 := P.r_pos 0
  have hr1 := P.r_pos 1
  have hr2 := P.r_pos 2
  have hr3 := P.r_pos 3
  have hg0 := hP.gap_pos 0
  have hg1 := hP.gap_pos 1
  have hg2 := hP.gap_pos 2
  have hn0 := hP.gap_ne 0
  have hn1 := hP.gap_ne 1
  have hn2 := hP.gap_ne 2
  have hc' : (P.r 2 : ℤ) = (q.val : ℤ) := by exact_mod_cast hc
  have hR2 : bar q (P.r 2 : ℤ) = 0 := by rw [hc', bar_cut]
  -- The six surviving four-factor products.  Each factor is positive and not the cut.
  have T3 := quarticFull_aug_four q j (k1 := (P.r 0 : ℤ))
    (k2 := (P.r 1 : ℤ) + P.r 2 - P.g 1) (k3 := (P.g 1 : ℤ)) (k4 := (P.r 3 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T4 := quarticFull_aug_four q j (k1 := (P.r 0 : ℤ)) (k2 := (P.r 1 : ℤ))
    (k3 := (P.r 2 : ℤ) + P.r 3 - P.g 2) (k4 := (P.g 2 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T5 := quarticFull_aug_four q j
    (k1 := (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) (k2 := (P.g 0 : ℤ))
    (k3 := (P.g 1 : ℤ)) (k4 := (P.r 3 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T6 := quarticFull_aug_four q j (k1 := (P.r 0 : ℤ) + P.r 1 - P.g 0)
    (k2 := (P.g 0 : ℤ)) (k3 := (P.r 2 : ℤ) + P.r 3 - P.g 2) (k4 := (P.g 2 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T7 := quarticFull_aug_four q j (k1 := (P.r 0 : ℤ))
    (k2 := (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) (k3 := (P.g 1 : ℤ))
    (k4 := (P.g 2 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T8 := quarticFull_aug_four q j
    (k1 := (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2)
    (k2 := (P.g 0 : ℤ)) (k3 := (P.g 1 : ℤ)) (k4 := (P.g 2 : ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval, hR2, map_add, map_sub, map_neg, map_zero, mul_zero, zero_mul, zero_add,
    add_zero, zero_sub, sub_zero, T3, T4, T5, T6, T7, T8]
  ring

/-- The augmented derivative of a complete generator is its indicator, for every `j`. -/
private theorem quarticFull_aug_complete (j : ℕ+) (k : ℤ) :
    residualAugmentation (MvPolynomial.pderiv j (complete k)) = quarticDelta j k := by
  rw [residual_pderiv_complete]
  unfold quarticDelta
  split_ifs <;> simp

/-- Universal augmented derivative of the actual four-row restriction. -/
theorem quarticFull_interval (q : ℕ+) (P : Profile 3) (hP : QComponent q P)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = (q.val : ℤ))
    (hc : P.r 2 ≠ q.val) (hv : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ (q.val : ℤ)) (j : ℕ+) :
    residualAugmentation (MvPolynomial.pderiv j (restriction q P)) =
      quarticDelta j ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) +
      quarticDelta j ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) -
      quarticDelta j ((P.r 1 : ℤ) + P.r 2 - P.g 1) -
      quarticDelta j ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2) +
      quarticDelta j (P.r 2 : ℤ) + quarticDelta j (P.r 3 : ℤ) -
      quarticDelta j (P.g 2 : ℤ) -
      quarticDelta j ((P.r 2 : ℤ) + P.r 3 - P.g 2) := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have h12 := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at h12
  have e0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hb : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hq : 0 < q.val := q.pos
  have hr0 := P.r_pos 0
  have hr1 := P.r_pos 1
  have hr2 := P.r_pos 2
  have hr3 := P.r_pos 3
  have hg0 := hP.gap_pos 0
  have hg1 := hP.gap_pos 1
  have hg2 := hP.gap_pos 2
  have hn0 := hP.gap_ne 0
  have hn1 := hP.gap_ne 1
  have hn2 := hP.gap_ne 2
  -- Every other interval label is off the cut under the actual contact and thickness bounds.
  have n_r0 : (P.r 0 : ℤ) ≠ q.val := by omega
  have n_r1 : (P.r 1 : ℤ) ≠ q.val := by omega
  have n_r2 : (P.r 2 : ℤ) ≠ q.val := by exact_mod_cast hc
  have n_r3 : (P.r 3 : ℤ) ≠ q.val := by omega
  have n_g0 : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hn0
  have n_g1 : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hn1
  have n_g2 : (P.g 2 : ℤ) ≠ q.val := by exact_mod_cast hn2
  have n_v : (P.r 1 : ℤ) + P.r 2 - P.g 1 ≠ q.val := hv
  have n_w : (P.r 2 : ℤ) + P.r 3 - P.g 2 ≠ q.val := by omega
  have n_x : (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 ≠ q.val := by omega
  have n_y : (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 ≠ q.val := by omega
  have n_T : (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 ≠ q.val := by omega
  -- Positivity of every index that the augmentation of a complete generator needs.
  have p_r0 : (0 : ℤ) < P.r 0 := by exact_mod_cast hr0
  have p_r1 : (0 : ℤ) < P.r 1 := by exact_mod_cast hr1
  have p_r2 : (0 : ℤ) < P.r 2 := by exact_mod_cast hr2
  have p_r3 : (0 : ℤ) < P.r 3 := by exact_mod_cast hr3
  have p_g0 : (0 : ℤ) < P.g 0 := by exact_mod_cast hg0
  have p_g1 : (0 : ℤ) < P.g 1 := by exact_mod_cast hg1
  have p_g2 : (0 : ℤ) < P.g 2 := by exact_mod_cast hg2
  have p_v : (0 : ℤ) < (P.r 1 : ℤ) + P.r 2 - P.g 1 := by omega
  have p_w : (0 : ℤ) < (P.r 2 : ℤ) + P.r 3 - P.g 2 := by omega
  have p_x : (0 : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by omega
  have p_y : (0 : ℤ) < (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 := by omega
  have p_T : (0 : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 := by omega
  -- Augmentation of each complete generator occurring in the six surviving terms is one.
  have A_r0 := residualAugmentation_complete p_r0
  have A_r1 := residualAugmentation_complete p_r1
  have A_r2 := residualAugmentation_complete p_r2
  have A_r3 := residualAugmentation_complete p_r3
  have A_g0 := residualAugmentation_complete p_g0
  have A_g1 := residualAugmentation_complete p_g1
  have A_g2 := residualAugmentation_complete p_g2
  have A_v := residualAugmentation_complete p_v
  have A_w := residualAugmentation_complete p_w
  have A_x := residualAugmentation_complete p_x
  have A_y := residualAugmentation_complete p_y
  have A_T := residualAugmentation_complete p_T
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval]
  -- The two terms containing `bar q u` are the zero polynomial.
  rw [hu, bar_cut]
  simp only [zero_mul, mul_zero, sub_zero, zero_sub, add_zero, zero_add]
  -- Every surviving erased generator is an ordinary complete generator.
  rw [bar_eq_complete_of_ne q _ n_r0, bar_eq_complete_of_ne q _ n_r1,
    bar_eq_complete_of_ne q _ n_r2, bar_eq_complete_of_ne q _ n_r3,
    bar_eq_complete_of_ne q _ n_g0, bar_eq_complete_of_ne q _ n_g1,
    bar_eq_complete_of_ne q _ n_g2, bar_eq_complete_of_ne q _ n_v,
    bar_eq_complete_of_ne q _ n_w, bar_eq_complete_of_ne q _ n_x,
    bar_eq_complete_of_ne q _ n_y, bar_eq_complete_of_ne q _ n_T]
  simp only [map_add, map_sub, map_mul, MvPolynomial.pderiv_mul, quarticFull_aug_complete,
    A_r0, A_r1, A_r2, A_r3, A_g0, A_g1, A_g2, A_v, A_w, A_x, A_y, A_T,
    mul_one, one_mul]
  ring

/-- Untouched four-row augmented derivative: `δx + δy - δv - δF` at every `j`. -/
theorem quarticUntouched_interval (q : ℕ+) (P : Profile 3) (hP : QComponent q P)
    (hNo : NoEntryContact q P) (j : ℕ+) :
    residualAugmentation (MvPolynomial.pderiv j (restriction q P)) =
      quarticDelta j ((P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1) +
      quarticDelta j ((P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2) -
      quarticDelta j ((P.r 1 : ℤ) + P.r 2 - P.g 1) -
      quarticDelta j ((P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2) := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have h12 := hP.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at h12
  have e0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hb : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hq : 0 < q.val := q.pos
  have hr0 := P.r_pos 0
  have hr1 := P.r_pos 1
  have hr2 := P.r_pos 2
  have hr3 := P.r_pos 3
  have hg0 := hP.gap_pos 0
  have hg1 := hP.gap_pos 1
  have hg2 := hP.gap_pos 2
  -- Every index in the eight terms is positive; `omega` uses thickness and the bottom bound.
  have p_r0 : (0 : ℤ) < P.r 0 := by exact_mod_cast hr0
  have p_r1 : (0 : ℤ) < P.r 1 := by exact_mod_cast hr1
  have p_r2 : (0 : ℤ) < P.r 2 := by exact_mod_cast hr2
  have p_r3 : (0 : ℤ) < P.r 3 := by exact_mod_cast hr3
  have p_g0 : (0 : ℤ) < P.g 0 := by exact_mod_cast hg0
  have p_g1 : (0 : ℤ) < P.g 1 := by exact_mod_cast hg1
  have p_g2 : (0 : ℤ) < P.g 2 := by exact_mod_cast hg2
  have p_u : (0 : ℤ) < (P.r 0 : ℤ) + P.r 1 - P.g 0 := by omega
  have p_v : (0 : ℤ) < (P.r 1 : ℤ) + P.r 2 - P.g 1 := by omega
  have p_w : (0 : ℤ) < (P.r 2 : ℤ) + P.r 3 - P.g 2 := by omega
  have p_x : (0 : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by omega
  have p_y : (0 : ℤ) < (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 := by omega
  have p_T : (0 : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 := by
    omega
  -- Augmentation of every complete factor is one.
  have A_r0 := residualAugmentation_complete p_r0
  have A_r1 := residualAugmentation_complete p_r1
  have A_r2 := residualAugmentation_complete p_r2
  have A_r3 := residualAugmentation_complete p_r3
  have A_g0 := residualAugmentation_complete p_g0
  have A_g1 := residualAugmentation_complete p_g1
  have A_g2 := residualAugmentation_complete p_g2
  have A_u := residualAugmentation_complete p_u
  have A_v := residualAugmentation_complete p_v
  have A_w := residualAugmentation_complete p_w
  have A_x := residualAugmentation_complete p_x
  have A_y := residualAugmentation_complete p_y
  have A_T := residualAugmentation_complete p_T
  rw [restriction_eq_full_of_no_entry_contact hNo, Gluing.Profile.toBetaDiagram_schur,
    Gluing.Profile.schur_four_complete P hP.thick.hessenberg]
  simp only [fourInterval, map_add, map_sub, map_mul, MvPolynomial.pderiv_mul,
    quarticFull_aug_complete, A_r0, A_r1, A_r2, A_r3, A_g0, A_g1, A_g2, A_u, A_v, A_w, A_x,
    A_y, A_T, mul_one, one_mul, map_one]
  ring


/-- Every actual gap is below the surviving untouched derivative indices. -/
theorem untouched_gap_aug_zero (q : ℕ+) (P : Profile 3) (hP : QComponent q P)
    (hNo : NoEntryContact q P) (j : ℕ+)
    (hj : j.val = P.g 0 ∨ j.val = P.g 1 ∨ j.val = P.g 2) :
    residualAugmentation (MvPolynomial.pderiv j (restriction q P)) = 0 := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hv : (j.val : ℤ) < (P.r 1 : ℤ) + P.r 2 - P.g 1 := by
    rcases hj with h | h | h <;> omega
  have hx : (j.val : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 := by omega
  have hy : (j.val : ℤ) < (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 := by omega
  have hf : (j.val : ℤ) < (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 := by omega
  rw [quarticUntouched_interval q P hP hNo j]
  simp only [quarticDelta, if_neg (ne_of_gt hx), if_neg (ne_of_gt hy),
    if_neg (ne_of_gt hv), if_neg (ne_of_gt hf), zero_add, sub_zero]

/-- Actual equality cannot mix an untouched component with an isolated
merged-interval contact, including last gaps above the cut. -/
theorem untouched_interval_restrictions_ne (q : ℕ+) (P Q : Profile 3)
    (hP : QComponent q P) (hQ : QComponent q Q) (hNo : NoEntryContact q P)
    (hu : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val) (hc : Q.r 2 ≠ q.val)
    (hv : (Q.r 1 : ℤ) + Q.r 2 - Q.g 1 ≠ q.val) :
    restriction q P ≠ restriction q Q := by
  intro he
  let j : ℕ+ := ⟨Q.g 2, hQ.gap_pos 2⟩
  obtain ⟨_, hG⟩ := restriction_full_and_gap_eq hP hQ he
  have hprod : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using hG
  have hread := residual_triple_product_reading
    (show (0 : ℤ) < P.g 0 by exact_mod_cast hP.gap_pos 0)
    (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1)
    (show (0 : ℤ) < P.g 2 by exact_mod_cast hP.gap_pos 2)
    (show (0 : ℤ) < Q.g 0 by exact_mod_cast hQ.gap_pos 0)
    (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1)
    (show (0 : ℤ) < Q.g 2 by exact_mod_cast hQ.gap_pos 2) hprod
  have hmatch : j.val = P.g 0 ∨ j.val = P.g 1 ∨ j.val = P.g 2 := by
    unfold FourRowHessenberg.tripleMatch at hread
    rcases hread with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    all_goals dsimp [j]; omega
  have hzero := untouched_gap_aug_zero q P hP hNo j hmatch
  have hlow := quarticLow_interval q Q hQ hu hc hv j (by dsimp [j]; exact le_rfl)
  have hj : (Q.g 2 : ℤ) = (j.val : ℤ) := rfl
  rw [if_pos hj] at hlow
  have h := congrArg (fun p : CompleteRing => residualAugmentation (MvPolynomial.pderiv j p)) he
  rw [hzero, hlow] at h
  norm_num at h

/-- Equality recovers both the least nonzero augmented-derivative index
and its coefficient.  No distinctness of any other generator labels is needed. -/
theorem low_augmented_derivative_reading (p f : CompleteRing) (t T : ℤ) (c d : ℚ)
    (ht : 0 < t) (hT : 0 < T) (hc : c ≠ 0) (hd : d ≠ 0)
    (hp : ∀ v : ℕ+, (v.val : ℤ) ≤ t →
      residualAugmentation (MvPolynomial.pderiv v p) =
        c * (if t = (v.val : ℤ) then 1 else 0))
    (hf : ∀ v : ℕ+, (v.val : ℤ) ≤ T →
      residualAugmentation (MvPolynomial.pderiv v f) =
        d * (if T = (v.val : ℤ) then 1 else 0))
    (he : p = f) : t = T ∧ c = d := by
  rcases lt_trichotomy t T with hlt | heq | hgt
  · let v : ℕ+ := ⟨t.toNat, by omega⟩
    have hv : (v.val : ℤ) = t := by dsimp [v]; omega
    have hh := congrArg (fun z : CompleteRing =>
      residualAugmentation (MvPolynomial.pderiv v z)) he
    rw [hp v (by omega), hf v (by omega)] at hh
    simp only [hv, if_pos rfl, if_neg (ne_of_gt hlt), ite_true, mul_one, mul_zero] at hh
    exact (hc hh).elim
  · subst T
    let v : ℕ+ := ⟨t.toNat, by omega⟩
    have hv : (v.val : ℤ) = t := by dsimp [v]; omega
    have hh := congrArg (fun z : CompleteRing =>
      residualAugmentation (MvPolynomial.pderiv v z)) he
    rw [hp v (by omega), hf v (by omega)] at hh
    simp only [hv, if_pos rfl, ite_true, mul_one] at hh
    exact ⟨rfl, hh⟩
  · let v : ℕ+ := ⟨T.toNat, by omega⟩
    have hv : (v.val : ℤ) = T := by dsimp [v]; omega
    have hh := congrArg (fun z : CompleteRing =>
      residualAugmentation (MvPolynomial.pderiv v z)) he
    rw [hp v (by omega), hf v (by omega)] at hh
    simp only [hv, if_neg (ne_of_gt hgt), if_pos rfl, ite_true, mul_zero, mul_one] at hh
    exact (hd hh.symm).elim

private theorem shift_atom_not_lt (e x y : ℤ) (he : 0 < e) (hx : 0 < x)
    (h : ∀ j : ℕ+, quarticDelta j (x + e) - quarticDelta j x =
      quarticDelta j (y + e) - quarticDelta j y) (hlt : x < y) : False := by
  let j : ℕ+ := ⟨x.toNat, by omega⟩
  have hj : (j.val : ℤ) = x := by dsimp [j]; omega
  have hz (k : ℤ) (hk : x < k) : quarticDelta j k = 0 := by
    simp only [quarticDelta, if_neg (show k ≠ (j.val : ℤ) by omega)]
  have hone : quarticDelta j x = 1 := by simp only [quarticDelta, hj, if_pos rfl, ite_true]
  have hh := h j
  rw [hz (x + e) (by omega), hone, hz (y + e) (by omega), hz y hlt] at hh
  norm_num at hh

private theorem shift_atom_reading (e x y : ℤ) (he : 0 < e) (hx : 0 < x) (hy : 0 < y)
    (h : ∀ j : ℕ+, quarticDelta j (x + e) - quarticDelta j x =
      quarticDelta j (y + e) - quarticDelta j y) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact (shift_atom_not_lt e x y he hx h hlt).elim
  · exact heq
  · exact (shift_atom_not_lt e y x he hy (fun j => (h j).symm) hgt).elim

private theorem shift_pair_not_lt (e b v B V : ℤ)
    (he : 0 < e) (hb : 0 < b) (hbv : b < v) (hBV : B < V)
    (h : ∀ j : ℕ+,
      quarticDelta j (b + e) + quarticDelta j (v + e) - quarticDelta j b - quarticDelta j v =
        quarticDelta j (B + e) + quarticDelta j (V + e) - quarticDelta j B - quarticDelta j V)
    (hlt : b < B) : False := by
  let j : ℕ+ := ⟨b.toNat, by omega⟩
  have hj : (j.val : ℤ) = b := by dsimp [j]; omega
  have hz (k : ℤ) (hk : b < k) : quarticDelta j k = 0 := by
    simp only [quarticDelta, if_neg (show k ≠ (j.val : ℤ) by omega)]
  have hone : quarticDelta j b = 1 := by simp only [quarticDelta, hj, if_pos rfl, ite_true]
  have hh := h j
  rw [hz (b + e) (by omega), hz (v + e) (by omega), hone, hz v hbv,
    hz (B + e) (by omega), hz (V + e) (by omega), hz B hlt, hz V (by omega)] at hh
  norm_num at hh

/-- A positive shift recovers the two ordered positive origins from their
finite two-atom difference histogram.  The labels need not be distinct across sides. -/
theorem shift_pair_reading (e b v B V : ℤ)
    (he : 0 < e) (hb : 0 < b) (hbv : b < v) (hB : 0 < B) (hBV : B < V)
    (h : ∀ j : ℕ+,
      quarticDelta j (b + e) + quarticDelta j (v + e) - quarticDelta j b - quarticDelta j v =
        quarticDelta j (B + e) + quarticDelta j (V + e) - quarticDelta j B - quarticDelta j V) :
    b = B ∧ v = V := by
  have hbB : b = B := by
    rcases lt_trichotomy b B with hlt | heq | hgt
    · exact (shift_pair_not_lt e b v B V he hb hbv hBV h hlt).elim
    · exact heq
    · exact (shift_pair_not_lt e B V b v he hB hBV hbv (fun j => (h j).symm) hgt).elim
  subst B
  refine ⟨rfl, shift_atom_reading e v V he (by omega) (by omega) ?_⟩
  intro j
  linear_combination h j

private theorem interval_rows_avoid_cut (q : ℕ+) (P : Profile 3) (hP : QComponent q P)
    (hu : (P.r 0:ℤ)+P.r 1-P.g 0=q.val) (hc : P.r 2≠q.val) : ∀i,P.r i≠q.val := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr,hs,ht,ha,hb,hc',hd⟩
  have hbottom : q.val+P.g 2<P.r 3 := by simpa [lastGap,Fin.sum_univ_succ] using hP.bottom
  intro i
  fin_cases i
  · change P.r 0≠q.val; omega
  · change P.r 1≠q.val; omega
  · change P.r 2≠q.val; exact hc
  · change P.r 3≠q.val; omega

/-- Actual isolated-u equality recovers every row and gap once the first
ordered endpoint has been read; no mate word or gap certificate is supplied. -/
theorem interval_aligned_profile_eq (q : ℕ+) (P Q : Profile 3)
    (hP : QComponent q P) (hQ : QComponent q Q)
    (huP : (P.r 0:ℤ)+P.r 1-P.g 0=q.val) (huQ : (Q.r 0:ℤ)+Q.r 1-Q.g 0=q.val)
    (hcP : P.r 2≠q.val) (hcQ : Q.r 2≠q.val)
    (hvP : (P.r 1:ℤ)+P.r 2-P.g 1≠q.val) (hvQ : (Q.r 1:ℤ)+Q.r 2-Q.g 1≠q.val)
    (hRow : (P.r 0:ℤ)=Q.r 0) (hFirst : (P.g 0:ℤ)=Q.g 0)
    (he : restriction q P=restriction q Q) : P=Q := by
  have hA : P.r 0=Q.r 0 := Int.ofNat_inj.mp hRow
  have hR : P.g 0=Q.g 0 := Int.ofNat_inj.mp hFirst
  have hB : P.r 1=Q.r 1 := by omega
  have hrowsP := interval_rows_avoid_cut q P hP huP hcP
  have hrowsQ := interval_rows_avoid_cut q Q hQ huQ hcQ
  have hT : P.g 2 = Q.g 2 := by
    have hh := low_augmented_derivative_reading (restriction q P) (restriction q Q)
      (P.g 2) (Q.g 2) (-1) (-1)
      (by exact_mod_cast hP.gap_pos 2) (by exact_mod_cast hQ.gap_pos 2)
      (by norm_num) (by norm_num)
      (fun j hj => by simpa only [neg_one_mul] using quarticLow_interval q P hP huP hcP hvP j hj)
      (fun j hj => by simpa only [neg_one_mul] using quarticLow_interval q Q hQ huQ hcQ hvQ j hj) he
    exact Int.ofNat_inj.mp hh.1
  obtain ⟨_,hGap⟩ := restriction_full_and_gap_eq hP hQ he
  have hGp : complete (P.g 0)*complete (P.g 1)*complete (P.g 2)=
      complete (Q.g 0)*complete (Q.g 1)*complete (Q.g 2) := by
    simpa only [gapMonomial,Fin.prod_univ_three,mul_assoc] using hGap
  simp only [←hR,←hT] at hGp
  have hrne : complete (P.g 0)≠0 := (complete_ne_zero_iff _).mpr (by omega)
  have htne : complete (P.g 2)≠0 := (complete_ne_zero_iff _).mpr (by omega)
  have hmiddle := mul_left_cancel₀ hrne (mul_right_cancel₀ htne hGp)
  have hS : P.g 1=Q.g 1 := Int.ofNat_inj.mp
    (complete_injective_nonnegative (by omega) (by omega) hmiddle)
  have hDiag := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [restriction_square_initial_no_row_contact q P hrowsP,
    restriction_square_initial_no_row_contact q Q hrowsQ] at hDiag
  have hFour : complete (P.r 0)*complete (P.r 1)*complete (P.r 2)*complete (P.r 3)=
      complete (Q.r 0)*complete (Q.r 1)*complete (Q.r 2)*complete (Q.r 3) := by
    simpa [Fin.prod_univ_succ,mul_assoc] using hDiag
  simp only [←hA,←hB] at hFour
  have habne : complete (P.r 0)*complete (P.r 1)≠0 := mul_ne_zero
    ((complete_ne_zero_iff _).mpr (by have h:=P.r_pos 0; omega))
    ((complete_ne_zero_iff _).mpr (by have h:=P.r_pos 1; omega))
  have hPairPoly : complete (P.r 2)*complete (P.r 3)=complete (Q.r 2)*complete (Q.r 3) := by
    apply mul_left_cancel₀ habne
    simpa only [mul_assoc] using hFour
  have hPair := complete_two_product_reading
    (show (0:ℤ)<P.r 2 by exact_mod_cast P.r_pos 2)
    (show (0:ℤ)<P.r 3 by exact_mod_cast P.r_pos 3)
    (show (0:ℤ)<Q.r 2 by exact_mod_cast Q.r_pos 2)
    (show (0:ℤ)<Q.r 3 by exact_mod_cast Q.r_pos 3) hPairPoly
  have finish (hc : P.r 2=Q.r 2) (hd : P.r 3=Q.r 3) : P=Q := by
    apply Profile.ext
    · funext i; fin_cases i
      · exact hA
      · exact hB
      · exact hc
      · exact hd
    · funext i; fin_cases i
      · exact hR
      · exact hS
      · exact hT
  rcases hPair with ⟨hc,hd⟩|⟨hc,hd⟩
  · exact finish (Int.ofNat_inj.mp hc) (Int.ofNat_inj.mp hd)
  · have hq2 : Q.r 2=P.r 3 := Int.ofNat_inj.mp hd.symm
    have hq3 : Q.r 3=P.r 2 := Int.ofNat_inj.mp hc.symm
    have hbotP : q.val+P.g 2<P.r 3 := by simpa [lastGap,Fin.sum_univ_succ] using hP.bottom
    have hbotQ : q.val+Q.g 2<Q.r 3 := by simpa [lastGap,Fin.sum_univ_succ] using hQ.bottom
    have heFour := he
    rw [restriction_four_expansion q P hP.thick,restriction_four_expansion q Q hQ.thick] at heFour
    have hSwap : fourInterval (bar q) (P.r 0) (P.r 1) (P.r 2) (P.r 3) (P.g 0) (P.g 1) (P.g 2)=
        fourInterval (bar q) (P.r 0) (P.r 1) (P.r 3) (P.r 2) (P.g 0) (P.g 1) (P.g 2) := by
      simpa only [←hA,←hB,←hR,←hS,←hT,hq2,hq3] using heFour
    have hdom := P.four_domain hP.thick.hessenberg
    rcases hdom with ⟨_,_,_,ha,hb,hc',hd'⟩
    have hcd := interval_last_swap_key q (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2)
      (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
      (by exact_mod_cast hP.gap_pos 2) ha hb (by omega) (by omega) huP hSwap
    have hcdN : P.r 2=P.r 3 := Int.ofNat_inj.mp hcd
    exact finish (hcdN.trans hq2.symm) (hcdN.symm.trans hq3.symm)


private theorem no_rows_aligned_reading {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hrowsP : ∀ i, P.r i ≠ q.val) (hrowsQ : ∀ i, Q.r i ≠ q.val)
    (htouch : ¬ (NoEntryContact q P ∧ NoEntryContact q Q))
    (hOrient : prefixIndex P ≤ suffixIndex P)
    (hRow : (P.r 0 : ℤ) = Q.r 0) (hFirst : (P.g 0 : ℤ) = Q.g 0)
    (he : restriction q P = restriction q Q) : P = Q ∨ P = Q.rotate := by
  have hstatus := no_row_contact_status_eq q P Q hP hQ hrowsP hrowsQ he
  have ho : (P.r 0 : ℤ) - P.g 0 ≤ (P.r 3 : ℤ) - P.g 2 := by
    dsimp [prefixIndex, suffixIndex] at hOrient
    omega
  by_cases hvP : (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val
  · have hvQ := hstatus.1.mp hvP
    exact no_row_aligned_interval_reading q P Q hP hQ hrowsP hrowsQ
      false hvP hvQ hRow hFirst ho he
  · have hvQ : (Q.r 1 : ℤ) + Q.r 2 - Q.g 1 ≠ q.val :=
      fun h => hvP (hstatus.1.mpr h)
    by_cases hxP : (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 = q.val
    · have hxQ := hstatus.2.mp hxP
      exact no_row_aligned_interval_reading q P Q hP hQ hrowsP hrowsQ
        true hxP hxQ hRow hFirst ho he
    · have hxQ : (Q.r 0 : ℤ) + Q.r 1 + Q.r 2 - Q.g 0 - Q.g 1 ≠ q.val :=
        fun h => hxP (hstatus.2.mpr h)
      by_cases huP : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val
      · by_cases huQ : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val
        · exact Or.inl (interval_aligned_profile_eq q P Q hP hQ
            huP huQ (hrowsP 2) (hrowsQ 2) hvP hvQ hRow hFirst he)
        · have hNoQ := four_no_contact_of_first_indices hQ
            (hrowsQ 0) (hrowsQ 1) (hrowsQ 2) huQ hvQ hxQ
          exact (untouched_interval_restrictions_ne q Q P hQ hP hNoQ
            huP (hrowsP 2) hvP he.symm).elim
      · have hNoP := four_no_contact_of_first_indices hP
          (hrowsP 0) (hrowsP 1) (hrowsP 2) huP hvP hxP
        by_cases huQ : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val
        · exact (untouched_interval_restrictions_ne q P Q hP hQ hNoP
            huQ (hrowsQ 2) hvQ he).elim
        · have hNoQ := four_no_contact_of_first_indices hQ
            (hrowsQ 0) (hrowsQ 1) (hrowsQ 2) huQ hvQ hxQ
          exact (htouch ⟨hNoP, hNoQ⟩).elim

private theorem quartet_aug_complete (j : ℕ+) (a b c d : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    residualAugmentation (MvPolynomial.pderiv j (quartetTerm ![a, b, c, d])) =
      quarticDelta j a + quarticDelta j b + quarticDelta j c + quarticDelta j d := by
  simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    MvPolynomial.pderiv_mul, map_add, map_mul, quarticFull_aug_complete,
    residualAugmentation_complete ha, residualAugmentation_complete hb,
    residualAugmentation_complete hc, residualAugmentation_complete hd, one_mul, mul_one]
  all_goals ring

private theorem middleB_cross_not_lt (q a c d C D r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hq : r + s < q) (hc : s + t < c) (hd : q + t < d)
    (hC : s + t < C) (hD : q + t < D)
    (hcross : d = a + q + C - r - s ∧ D = a + q + c - r - s) (hlt : C < c)
    (he : quartetTerm ![r, a + q - r, c, d] + quartetTerm ![s, a, q + c - s, d] =
      quartetTerm ![r, a + q - r, C, D] + quartetTerm ![s, a, q + C - s, D]) :
    False := by
  let j : ℕ+ := ⟨D.toNat, by omega⟩
  have hj : (j.val : ℤ) = D := by dsimp [j]; omega
  have hz (k : ℤ) (hk : k < D) : quarticDelta j k = 0 := by
    simp only [quarticDelta, if_neg (show k ≠ (j.val : ℤ) by omega)]
  have hone : quarticDelta j D = 1 := by simp only [quarticDelta, hj, if_pos rfl, ite_true]
  have hh := congrArg (fun z : CompleteRing =>
    residualAugmentation (MvPolynomial.pderiv j z)) he
  simp only [map_add,
    quartet_aug_complete j r (a + q - r) c d hr (by omega) (by omega) (by omega),
    quartet_aug_complete j s a (q + c - s) d hs (by omega) (by omega) (by omega),
    quartet_aug_complete j r (a + q - r) C D hr (by omega) (by omega) (by omega),
    quartet_aug_complete j s a (q + C - s) D hs (by omega) (by omega) (by omega)] at hh
  rw [hz r (by omega), hz (a + q - r) (by omega), hz c (by omega), hz d (by omega),
    hz s (by omega), hz a (by omega), hz (q + c - s) (by omega),
    hz C (by omega), hz (q + C - s) (by omega), hone] at hh
  norm_num at hh

/-- Once the first endpoint and all gaps are recovered at a second-row
contact, the positive word and negative sum recover the remaining rows. -/
private theorem middleB_fixed_gaps_reading (q a c d C D r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hq : r + s < q) (hc : s + t < c) (hd : q + t < d)
    (hC : s + t < C) (hD : q + t < D)
    (hpos : complete (a + q + c - r - s) * complete d =
      complete (a + q + C - r - s) * complete D)
    (hneg : quartetTerm ![r, a + q - r, c, d] + quartetTerm ![s, a, q + c - s, d] =
      quartetTerm ![r, a + q - r, C, D] + quartetTerm ![s, a, q + C - s, D]) :
    c = C ∧ d = D := by
  rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hpos with
      ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨by omega, h1⟩
  · have hcross : d = a + q + C - r - s ∧ D = a + q + c - r - s :=
      ⟨h1, h0.symm⟩
    have hcC : c = C := by
      rcases lt_trichotomy c C with hlt | heq | hgt
      · exact (middleB_cross_not_lt q a C D c d r s t hr hs ht ha hq hC hD
          hc hd ⟨hcross.2, hcross.1⟩ hlt hneg.symm).elim
      · exact heq
      · exact (middleB_cross_not_lt q a c d C D r s t hr hs ht ha hq hc hd
          hC hD hcross hgt hneg).elim
    exact ⟨hcC, by omega⟩

private theorem separate_gap_coefficients (r s x d u w X D U W : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (hxr : r < x) (hdr : r < d) (hUr : r < U) (hWr : r < W)
    (hus : s < u) (hws : s < w) (hXs : s < X) (hDs : s < D)
    (he : complete s * complete x * complete d + complete r * complete u * complete w =
      complete r * complete X * complete D + complete s * complete U * complete W) :
    complete x * complete d = complete U * complete W ∧
      complete u * complete w = complete X * complete D := by
  let Rtag : ℕ+ := ⟨r.toNat, by omega⟩
  let Stag : ℕ+ := ⟨s.toNat, by omega⟩
  have hR : (Rtag.val : ℤ) = r := by dsimp [Rtag]; omega
  have hS : (Stag.val : ℤ) = s := by dsimp [Stag]; omega
  have hcutR := congrArg (eraseGenerator Rtag) he
  have hcutS := congrArg (eraseGenerator Stag) he
  simp only [map_add, map_mul, eraseGenerator_complete, hR, if_pos rfl,
    if_neg (Ne.symm hne), if_neg (show x ≠ r by omega), if_neg (show d ≠ r by omega),
    if_neg (show U ≠ r by omega), if_neg (show W ≠ r by omega),
    ite_true, ite_false, zero_mul, mul_zero, zero_add, add_zero] at hcutR
  simp only [map_add, map_mul, eraseGenerator_complete, hS, if_pos rfl,
    if_neg hne, if_neg (show u ≠ s by omega), if_neg (show w ≠ s by omega),
    if_neg (show X ≠ s by omega), if_neg (show D ≠ s by omega),
    ite_true, ite_false, zero_mul, mul_zero, zero_add, add_zero] at hcutS
  constructor
  · apply mul_left_cancel₀ ((complete_ne_zero_iff s).mpr hs.le)
    simpa only [mul_assoc] using hcutR
  · apply mul_left_cancel₀ ((complete_ne_zero_iff r).mpr hr.le)
    simpa only [mul_assoc] using hcutS

private theorem mixed_middle_same_gap_order (q a c d b e r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (ha : r < a) (hq : r + s < q) (hc : s + r < c)
    (hd : q + r < d) (hb : r + s < b) (he : q + r < e) (hbq : b ≠ q)
    (hpos :
      complete s * complete (a + q + c - r - s) * complete d +
          complete r * complete (a + q - r) * complete (c + d - r) =
        complete s * complete (a + b + q - r - s) * complete e +
          complete r * complete (a + b - r) * complete (q + e - r)) :
    c = b ∧ d = a ∧ e = a := by
  have hparts := separate_gap_coefficients r s
    (a + q + c - r - s) d (a + q - r) (c + d - r)
    (a + b - r) (q + e - r) (a + b + q - r - s) e hr hs hne
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by linear_combination hpos)
  have heA : e = a := by
    rcases complete_two_product_reading (by omega) (by omega)
        (by omega) (by omega) hparts.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact (hbq (by omega)).elim
    · omega
  rcases complete_two_product_reading (by omega) (by omega)
      (by omega) (by omega) hparts.1 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega

private theorem mixed_middle_exchanged_gap_order (q a c d b e r s : ℤ)
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (ha : r < a) (hq : r + s < q) (hc : s + r < c)
    (hd : q + r < d) (hb : 2 * r < b) (he : q + s < e) (hcq : c ≠ q)
    (hpos :
      complete s * complete (a + q + c - r - s) * complete d +
          complete r * complete (a + q - r) * complete (c + d - r) =
        complete r * complete (a + b + q - 2 * r) * complete e +
          complete s * complete (a + b - r) * complete (q + e - s))
    (hneg :
      quartetTerm ![r, a + q - r, c, d] + quartetTerm ![s, a, q + c - s, d] =
        quartetTerm ![r, a, b + q - r, e] + quartetTerm ![s, a, b, q + e - s]) :
    c = a ∧ b = a + q - s ∧ d = a + 2 * q - r - s ∧ e = a + q - r := by
  have hparts := separate_gap_coefficients r s
    (a + q + c - r - s) d (a + q - r) (c + d - r)
    (a + b + q - 2 * r) e (a + b - r) (q + e - s) hr hs hne
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hpos
  have heU : e = a + q - r := by
    rcases complete_two_product_reading (by omega) (by omega)
        (by omega) (by omega) hparts.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
  have hmiddle : b = q + c - s ∧ d = q + e - s := by
    rcases complete_two_product_reading (by omega) (by omega)
        (by omega) (by omega) hparts.1 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨by omega, h1⟩
    · exact (hcq (by omega)).elim
  have hN2 : quartetTerm ![s, a, b, q + e - s] = quartetTerm ![s, a, q + c - s, d] := by
    rw [hmiddle.1, ← hmiddle.2]
  rw [hN2] at hneg
  have hword := add_right_cancel hneg
  have hpair : complete c * complete d = complete a * complete (b + q - r) := by
    apply mul_left_cancel₀ (mul_ne_zero ((complete_ne_zero_iff r).mpr hr.le)
      ((complete_ne_zero_iff (a + q - r)).mpr (by omega)))
    simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hword
    rw [heU] at hword
    linear_combination hword
  have hcA : c = a := by
    rcases complete_two_product_reading (by omega) (by omega) (by omega) (by omega) hpair with
      ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
  exact ⟨hcA, by omega, by omega, heU⟩

private theorem middleB_reduced_eq {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hb : P.r 1 = q.val) :
    fourReducedPositive P = fourPositiveInventory P ∧
      fourReducedNegative P = fourNegativeInventory P := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hnL : ¬ fourCancellationLeft P := by
    rintro ⟨h0, h1, h2⟩
    omega
  have hnM : ¬ fourCancellationMiddle P := by
    rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) <;> omega
  have hnR : ¬ fourCancellationRight P := by
    rintro ⟨h0, h1, h2⟩
    omega
  constructor <;> simp only [fourReducedPositive, fourReducedNegative,
    if_neg hnL, if_neg hnM, if_neg hnR]

private theorem survivingQuartets_cons_prop (q : ℕ+) (T : Fin 4 → ℤ)
    (L : List (Fin 4 → ℤ)) :
    survivingQuartets q (T :: L) =
      if quartetSurvives q T then T :: survivingQuartets q L else survivingQuartets q L := by
  classical
  by_cases h : quartetSurvives q T <;> simp [survivingQuartets, h]

private theorem survivingQuartets_nil_prop (q : ℕ+) :
    survivingQuartets q ([] : List (Fin 4 → ℤ)) = [] := rfl

private theorem middleB_inventory_lists {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hb : P.r 1 = q.val)
    (ha : P.r 0 ≠ q.val) (hc : P.r 2 ≠ q.val) :
    survivingQuartets q (fourPositiveInventory P) =
      [![(P.g 0 : ℤ), P.g 1, (P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1, P.r 3],
       ![(P.g 0 : ℤ), P.g 2, (P.r 0 : ℤ) + q.val - P.g 0,
         (P.r 2 : ℤ) + P.r 3 - P.g 2],
       ![(P.g 1 : ℤ), P.g 2, P.r 0, (q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2]] ∧
    survivingQuartets q (fourNegativeInventory P) =
      [![(P.g 0 : ℤ), (P.r 0 : ℤ) + q.val - P.g 0, P.r 2, P.r 3],
       ![(P.g 1 : ℤ), P.r 0, (q.val : ℤ) + P.r 2 - P.g 1, P.r 3]] := by
  have h01 := hP.thick 0 1 (by decide)
  have h12 := hP.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  change P.g 1 + P.g 2 < P.r 2 at h12
  have h0 : P.g 0 < P.r 0 := by exact P.g_lt_castSucc 0
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hbz : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  have haz : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hcz : (P.r 2 : ℤ) ≠ q.val := by exact_mod_cast hc
  have hdz : (P.r 3 : ℤ) ≠ q.val := by omega
  have hgz (i : Fin 3) : (P.g i : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne i
  have hun : (P.r 0 : ℤ) + q.val - P.g 0 ≠ q.val := by omega
  have hvn : (q.val : ℤ) + P.r 2 - P.g 1 ≠ q.val := by omega
  have hwn : (P.r 2 : ℤ) + P.r 3 - P.g 2 ≠ q.val := by omega
  have hxn : (P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1 ≠ q.val := by omega
  have hyn : (q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 ≠ q.val := by omega
  simp only [fourPositiveInventory, fourNegativeInventory,
    survivingQuartets_cons_prop, survivingQuartets_nil_prop, prefixIndex, suffixIndex, quartetSurvives,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk,
    hbz, haz, hcz, hdz, hgz 0, hgz 1, hgz 2, hun, hvn, hwn, hxn, hyn,
    not_true_eq_false, not_false_eq_true, and_true, true_and, and_false, false_and,
    eq_self_iff_true, decide_true, decide_false, ite_true, ite_false] <;> simp_all

private theorem middleC_inventory_lists {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hc : P.r 2 = q.val)
    (ha : P.r 0 ≠ q.val) (hb : P.r 1 ≠ q.val) :
    survivingQuartets q (fourPositiveInventory P) =
      [![(P.g 0 : ℤ), P.g 1, (P.r 0 : ℤ) + P.r 1 + q.val - P.g 0 - P.g 1, P.r 3]] ++
      (if (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val then [] else
        [![(P.g 0 : ℤ), P.g 2, (P.r 0 : ℤ) + P.r 1 - P.g 0,
          (q.val : ℤ) + P.r 3 - P.g 2]]) ++
      [![(P.g 1 : ℤ), P.g 2, P.r 0, (P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 2]] ∧
    survivingQuartets q (fourNegativeInventory P) =
      [![(P.g 1 : ℤ), P.r 0, (P.r 1 : ℤ) + q.val - P.g 1, P.r 3],
       ![(P.g 2 : ℤ), P.r 0, P.r 1, (q.val : ℤ) + P.r 3 - P.g 2]] := by
  have h01 := hP.thick 0 1 (by decide)
  have h12 := hP.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  change P.g 1 + P.g 2 < P.r 2 at h12
  have h0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hcz : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  have haz : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hbz : (P.r 1 : ℤ) ≠ q.val := by exact_mod_cast hb
  have hdz : (P.r 3 : ℤ) ≠ q.val := by omega
  have hgz (i : Fin 3) : (P.g i : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne i
  have hvn : (P.r 1 : ℤ) + q.val - P.g 1 ≠ q.val := by omega
  have hwn : (q.val : ℤ) + P.r 3 - P.g 2 ≠ q.val := by omega
  have hxn : (P.r 0 : ℤ) + P.r 1 + q.val - P.g 0 - P.g 1 ≠ q.val := by omega
  have hyn : (P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 2 ≠ q.val := by omega
  by_cases hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val
  all_goals simp only [fourPositiveInventory, fourNegativeInventory,
    survivingQuartets_cons_prop, survivingQuartets_nil_prop, prefixIndex, suffixIndex, quartetSurvives,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk,
    hcz, haz, hbz, hdz, hgz 0, hgz 1, hgz 2, hvn, hwn, hxn, hyn, hu,
    not_true_eq_false, not_false_eq_true, and_true, true_and, and_false, false_and,
    eq_self_iff_true, decide_true, decide_false, ite_true, ite_false,
    List.cons_append, List.nil_append] <;> simp_all

private theorem middleC_reduced_eq_of_length_three {q : ℕ+} {P : Profile 3}
    (hc : P.r 2 = q.val)
    (hlen : (survivingQuartets q (fourReducedPositive P)).length = 3) :
    fourReducedPositive P = fourPositiveInventory P ∧
      fourReducedNegative P = fourNegativeInventory P := by
  let diag : Fin 4 → ℤ := ![(P.r 0 : ℤ), P.r 1, P.r 2, P.r 3]
  have hdiag : ¬ quartetSurvives q diag := by
    rintro ⟨h0, h1, h2, h3⟩
    apply h2
    change (P.r 2 : ℤ) = (q.val : ℤ)
    exact_mod_cast hc
  have hskip (L : List (Fin 4 → ℤ)) :
      survivingQuartets q (diag :: L) = survivingQuartets q L := by
    rw [survivingQuartets_cons_prop, if_neg hdiag]
  have hbound (k : Fin 3) :
      (survivingQuartets q ((fourPositiveInventory P).eraseIdx (k.val + 1))).length ≤ 2 := by
    fin_cases k <;>
      change (survivingQuartets q (diag :: _)).length ≤ 2
    all_goals rw [hskip]
    all_goals unfold survivingQuartets
    all_goals apply List.length_filter_le
  have hnL : ¬ fourCancellationLeft P := by
    intro hL
    have hh := hlen
    rw [fourReducedPositive, if_pos hL] at hh
    have hb : (survivingQuartets q ((fourPositiveInventory P).eraseIdx 1)).length ≤ 2 := hbound 0
    omega
  have hnM : ¬ fourCancellationMiddle P := by
    intro hM
    have hh := hlen
    rw [fourReducedPositive, if_neg hnL, if_pos hM] at hh
    have hb : (survivingQuartets q ((fourPositiveInventory P).eraseIdx 2)).length ≤ 2 := hbound 1
    omega
  have hnR : ¬ fourCancellationRight P := by
    intro hR
    have hh := hlen
    rw [fourReducedPositive, if_neg hnL, if_neg hnM, if_pos hR] at hh
    have hb : (survivingQuartets q ((fourPositiveInventory P).eraseIdx 3)).length ≤ 2 := hbound 2
    omega
  constructor <;> simp only [fourReducedPositive, fourReducedNegative,
    if_neg hnL, if_neg hnM, if_neg hnR]

private theorem middleBC_aligned_reading {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (haP : P.r 0 ≠ q.val) (hbP : P.r 1 = q.val) (hcP : P.r 2 ≠ q.val)
    (haQ : Q.r 0 ≠ q.val) (hbQ : Q.r 1 ≠ q.val) (hcQ : Q.r 2 = q.val)
    (hRow : (P.r 0 : ℤ) = Q.r 0) (hFirstGap : (P.g 0 : ℤ) = Q.g 0) :
    inventoryCoordinateAlternatives q P Q := by
  have hzero := four_quartic_restriction_eq hP hQ hd he
  obtain ⟨hpos, hneg⟩ := four_quartic_signed_parts hP hQ hd he
  have hredP := middleB_reduced_eq hP hbP
  have hlistsP := middleB_inventory_lists hP hbP haP hcP
  have hlenQ : (survivingQuartets q (fourReducedPositive Q)).length = 3 := by
    have hh := quartetSum_lengths (fourReduced_surviving_positive hP).1
      (fourReduced_surviving_positive hQ).1 hpos
    rw [hredP.1, hlistsP.1] at hh
    exact hh.symm
  have hredQ := middleC_reduced_eq_of_length_three hcQ hlenQ
  have hlistsQ := middleC_inventory_lists hQ hcQ haQ hbQ
  have huQ : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 ≠ q.val := by
    intro hu
    have hh := hlenQ
    rw [hredQ.1, hlistsQ.1] at hh
    simp only [if_pos hu, ite_true, List.length_append, List.length_cons, List.length_nil] at hh
    omega
  have hlow := low_augmented_derivative_reading
    (restriction q P) (restriction q Q) (P.g 2) (Q.g 0) 1 1
    (by exact_mod_cast hP.gap_pos 2) (by exact_mod_cast hQ.gap_pos 0)
    (by norm_num) (by norm_num)
    (fun j hj => by simpa only [one_mul] using quarticMid_middleB q hP hbP haP hcP j hj)
    (fun j hj => by simpa only [one_mul] using quarticMid_middleC q hQ hcQ hbQ haQ huQ j hj) hzero
  have ht : P.g 2 = P.g 0 := Int.ofNat_inj.mp (hlow.1.trans hFirstGap.symm)
  have hg0 : P.g 0 = Q.g 0 := Int.ofNat_inj.mp hFirstGap
  have hRowNat : P.r 0 = Q.r 0 := Int.ofNat_inj.mp hRow
  obtain ⟨hF, hG⟩ := restriction_full_and_gap_eq hP hQ hzero
  have hFraw := hF
  rw [fullIndex_four, fullIndex_four] at hFraw
  have hYraw : (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 =
      (Q.r 1 : ℤ) + Q.r 2 + Q.r 3 - Q.g 1 - Q.g 2 := by omega
  rw [hbP, hcQ, ht] at hYraw
  have hprod : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using hG
  rw [ht, ← hg0] at hprod
  have htail : complete (P.g 1) * complete (P.g 0) =
      complete (Q.g 1) * complete (Q.g 2) := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ P.g 0 by omega))
    simpa only [mul_assoc] using hprod
  rw [hredP.1, hredQ.1, hlistsP.1, hlistsQ.1] at hpos
  rw [hredP.2, hredQ.2, hlistsP.2, hlistsQ.2] at hneg
  simp only [if_neg huQ, List.cons_append, List.nil_append,
    quartetSum_cons, quartetSum_nil, add_zero] at hpos hneg
  simp only [← hRowNat, ← hg0, ht] at hpos hneg
  have hp0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hp01 := hP.thick 0 1 (by decide)
  have hp12 := hP.thick 1 2 (by decide)
  have hq01 := hQ.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hp01
  change P.g 1 + P.g 2 < P.r 2 at hp12
  change Q.g 0 + Q.g 1 < Q.r 1 at hq01
  have hpBottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hqBottom : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hneNat : P.g 0 ≠ P.g 1 := (four_quartic_nonextraction hP hd).2.2.1 hbP
  have hrNon : complete (P.g 0) ≠ 0 :=
    (complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ P.g 0 by omega)
  rcases complete_two_product_reading
      (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1)
      (show (0 : ℤ) < P.g 0 by exact_mod_cast hP.gap_pos 0)
      (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1)
      (show (0 : ℤ) < Q.g 2 by exact_mod_cast hQ.gap_pos 2) htail with
      ⟨hS, hT⟩ | ⟨hS, hT⟩
  · have hg1 : P.g 1 = Q.g 1 := Int.ofNat_inj.mp hS
    have hg2 : P.g 0 = Q.g 2 := Int.ofNat_inj.mp hT
    have hp := hpos
    have hy := hYraw
    simp only [← hg1, ← hg2] at hp hy
    rw [hy] at hp
    have hpPair :
        complete (P.g 1) * complete ((P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1) *
            complete (P.r 3) +
          complete (P.g 0) * complete ((P.r 0 : ℤ) + q.val - P.g 0) *
            complete ((P.r 2 : ℤ) + P.r 3 - P.g 0) =
        complete (P.g 1) * complete ((P.r 0 : ℤ) + Q.r 1 + q.val - P.g 0 - P.g 1) *
            complete (Q.r 3) +
          complete (P.g 0) * complete ((P.r 0 : ℤ) + Q.r 1 - P.g 0) *
            complete ((q.val : ℤ) + Q.r 3 - P.g 0) := by
      apply mul_left_cancel₀ hrNon
      simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hp
      linear_combination hp
    obtain ⟨hcEq, hdEq, heEq⟩ := mixed_middle_same_gap_order (q.val : ℤ)
      (P.r 0) (P.r 2) (P.r 3) (Q.r 1) (Q.r 3) (P.g 0) (P.g 1)
      (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
      (by exact_mod_cast hneNat) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by exact_mod_cast hbQ) hpPair
    apply Or.inr
    apply Or.inl
    change P.r 0 = Q.r 3 ∧ P.r 1 = Q.r 2 ∧ P.r 2 = Q.r 1 ∧ P.r 3 = Q.r 0 ∧
      P.g 0 = Q.g 2 ∧ P.g 1 = Q.g 1 ∧ P.g 2 = Q.g 0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · have hg1 : P.g 1 = Q.g 2 := Int.ofNat_inj.mp hS
    have hg2 : P.g 0 = Q.g 1 := Int.ofNat_inj.mp hT
    have hp := hpos
    have hn := hneg
    have hy := hYraw
    simp only [← hg1, ← hg2] at hp hn hy
    rw [hy] at hp
    have hpPair :
        complete (P.g 1) * complete ((P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1) *
            complete (P.r 3) +
          complete (P.g 0) * complete ((P.r 0 : ℤ) + q.val - P.g 0) *
            complete ((P.r 2 : ℤ) + P.r 3 - P.g 0) =
        complete (P.g 0) * complete ((P.r 0 : ℤ) + Q.r 1 + q.val - 2 * P.g 0) *
            complete (Q.r 3) +
          complete (P.g 1) * complete ((P.r 0 : ℤ) + Q.r 1 - P.g 0) *
            complete ((q.val : ℤ) + Q.r 3 - P.g 1) := by
      apply mul_left_cancel₀ hrNon
      simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hp
      have hX : (P.r 0 : ℤ) + Q.r 1 + q.val - P.g 0 - P.g 0 =
          (P.r 0 : ℤ) + Q.r 1 + q.val - 2 * P.g 0 := by omega
      rw [hX] at hp
      linear_combination hp
    obtain ⟨hcEq, hbEq, hdEq, heEq⟩ := mixed_middle_exchanged_gap_order (q.val : ℤ)
      (P.r 0) (P.r 2) (P.r 3) (Q.r 1) (Q.r 3) (P.g 0) (P.g 1)
      (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
      (by exact_mod_cast hneNat) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by exact_mod_cast hcP) hpPair hn
    have haBound : P.g 0 + P.g 1 < P.r 0 := by omega
    have hqBound : P.g 0 + P.g 1 < q.val := by omega
    apply Or.inr
    apply Or.inr
    apply Or.inl
    refine ⟨haBound, hqBound, hP.gap_pos 0, hP.gap_pos 1, hneNat, haP, ?_⟩
    apply Or.inl
    constructor
    · apply Or.inl
      change P.r 0 = P.r 0 ∧ P.r 1 = q.val ∧ P.r 2 = P.r 0 ∧
        P.r 3 = P.r 0 + 2 * q.val - P.g 0 - P.g 1 ∧
        P.g 0 = P.g 0 ∧ P.g 1 = P.g 1 ∧ P.g 2 = P.g 0
      refine ⟨rfl, hbP, ?_, ?_, rfl, rfl, ht⟩ <;> omega
    · apply Or.inl
      change Q.r 0 = P.r 0 ∧ Q.r 1 = P.r 0 + q.val - P.g 1 ∧ Q.r 2 = q.val ∧
        Q.r 3 = P.r 0 + q.val - P.g 0 ∧ Q.g 0 = P.g 0 ∧
        Q.g 1 = P.g 0 ∧ Q.g 2 = P.g 1
      refine ⟨hRowNat.symm, ?_, hcQ, ?_, hg0.symm, hg2.symm, hg1.symm⟩ <;> omega

private theorem middleUC_reduced_eq {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hc : P.r 2 = q.val)
    (hu : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val) :
    fourReducedPositive P = fourPositiveInventory P ∧
      fourReducedNegative P = fourNegativeInventory P := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hnL : ¬ fourCancellationLeft P := by
    rintro ⟨h0, h1, h2⟩
    omega
  have hnM : ¬ fourCancellationMiddle P := by
    rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) <;> omega
  have hnR : ¬ fourCancellationRight P := by
    rintro ⟨h0, h1, h2⟩
    omega
  constructor <;> simp only [fourReducedPositive, fourReducedNegative,
    if_neg hnL, if_neg hnM, if_neg hnR]

private theorem middleUC_both_aligned_reading {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (hcP : P.r 2 = q.val) (huP : (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val)
    (hcQ : Q.r 2 = q.val) (huQ : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val)
    (hRow : (P.r 0 : ℤ) = Q.r 0) (hFirstGap : (P.g 0 : ℤ) = Q.g 0) : P = Q := by
  have hzero := four_quartic_restriction_eq hP hQ hd he
  have hp0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hq0 : Q.g 0 < Q.r 0 := Q.g_lt_castSucc 0
  have hp01 := hP.thick 0 1 (by decide)
  have hq01 := hQ.thick 0 1 (by decide)
  have hp12 := hP.thick 1 2 (by decide)
  have hq12 := hQ.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hp01
  change Q.g 0 + Q.g 1 < Q.r 1 at hq01
  change P.g 1 + P.g 2 < P.r 2 at hp12
  change Q.g 1 + Q.g 2 < Q.r 2 at hq12
  have haP : P.r 0 ≠ q.val := by omega
  have hbP : P.r 1 ≠ q.val := by omega
  have haQ : Q.r 0 ≠ q.val := by omega
  have hbQ : Q.r 1 ≠ q.val := by omega
  have hbEq : (P.r 1 : ℤ) = Q.r 1 := by omega
  have hRowNat : P.r 0 = Q.r 0 := Int.ofNat_inj.mp hRow
  have hbNat : P.r 1 = Q.r 1 := Int.ofNat_inj.mp hbEq
  have hg0 : P.g 0 = Q.g 0 := Int.ofNat_inj.mp hFirstGap
  obtain ⟨hF, hG⟩ := restriction_full_and_gap_eq hP hQ hzero
  have hprod : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using hG
  have hgapread := residual_triple_product_reading
    (show (0 : ℤ) < P.g 0 by exact_mod_cast hP.gap_pos 0)
    (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1)
    (show (0 : ℤ) < P.g 2 by exact_mod_cast hP.gap_pos 2)
    (show (0 : ℤ) < Q.g 0 by exact_mod_cast hQ.gap_pos 0)
    (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1)
    (show (0 : ℤ) < Q.g 2 by exact_mod_cast hQ.gap_pos 2) hprod
  have hsum : (P.g 0 : ℤ) + P.g 1 + P.g 2 = (Q.g 0 : ℤ) + Q.g 1 + Q.g 2 := by
    unfold FourRowHessenberg.tripleMatch at hgapread
    rcases hgapread with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega
  rw [fullIndex_four, fullIndex_four] at hF
  have hdEq : (P.r 3 : ℤ) = Q.r 3 := by omega
  have hdNat : P.r 3 = Q.r 3 := Int.ofNat_inj.mp hdEq
  have hY : (P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 2 =
      (Q.r 1 : ℤ) + q.val + Q.r 3 - Q.g 1 - Q.g 2 := by omega
  have htail : complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 1) * complete (Q.g 2) := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ Q.g 0 by omega))
    rw [hg0] at hprod
    simpa only [mul_assoc] using hprod
  have hP3 : quartetTerm ![(P.g 1 : ℤ), P.g 2, P.r 0,
      (P.r 1 : ℤ) + q.val + P.r 3 - P.g 1 - P.g 2] =
      quartetTerm ![(Q.g 1 : ℤ), Q.g 2, Q.r 0,
        (Q.r 1 : ℤ) + q.val + Q.r 3 - Q.g 1 - Q.g 2] := by
    simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [hRowNat, hY]
    exact congrArg (fun z : CompleteRing => z * complete (Q.r 0) *
      complete ((Q.r 1 : ℤ) + q.val + Q.r 3 - Q.g 1 - Q.g 2)) htail
  have hpos := (four_quartic_signed_parts hP hQ hd he).1
  rw [(middleUC_reduced_eq hP hcP huP).1, (middleUC_reduced_eq hQ hcQ huQ).1,
    (middleC_inventory_lists hP hcP haP hbP).1,
    (middleC_inventory_lists hQ hcQ haQ hbQ).1] at hpos
  simp only [if_pos huP, if_pos huQ, ite_true, List.cons_append, List.nil_append,
    quartetSum_cons, quartetSum_nil, add_zero] at hpos
  rw [hP3] at hpos
  have hword := add_right_cancel hpos
  have hXP : (P.r 0 : ℤ) + P.r 1 + q.val - P.g 0 - P.g 1 =
      (q.val : ℤ) + q.val - P.g 1 := by omega
  have hXQ : (Q.r 0 : ℤ) + Q.r 1 + q.val - Q.g 0 - Q.g 1 =
      (q.val : ℤ) + q.val - Q.g 1 := by omega
  simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hword
  rw [hXP, hXQ, hg0, hdNat] at hword
  have hpair : complete (P.g 1) * complete ((q.val : ℤ) + q.val - P.g 1) =
      complete (Q.g 1) * complete ((q.val : ℤ) + q.val - Q.g 1) := by
    apply mul_left_cancel₀ (mul_ne_zero
      ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ Q.g 0 by omega))
      ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ Q.r 3 by omega)))
    linear_combination hword
  have hsEq : (P.g 1 : ℤ) = Q.g 1 := by
    rcases complete_two_product_reading
        (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1) (by omega)
        (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1) (by omega) hpair with
      ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega
  have hg1 : P.g 1 = Q.g 1 := Int.ofNat_inj.mp hsEq
  have htEq : (P.g 2 : ℤ) = Q.g 2 := by omega
  have hg2 : P.g 2 = Q.g 2 := Int.ofNat_inj.mp htEq
  apply Profile.ext
  · funext i
    fin_cases i
    · exact hRowNat
    · exact hbNat
    · exact hcP.trans hcQ.symm
    · exact hdNat
  · funext i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2

private theorem middleBC_negative_list {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hb : P.r 1 = q.val) (hc : P.r 2 = q.val)
    (ha : P.r 0 ≠ q.val) :
    survivingQuartets q (fourNegativeInventory P) =
      [![(P.g 1 : ℤ), P.r 0, (q.val : ℤ) + q.val - P.g 1, P.r 3]] := by
  have h01 := hP.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at h01
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hbz : (P.r 1 : ℤ) = q.val := by exact_mod_cast hb
  have hcz : (P.r 2 : ℤ) = q.val := by exact_mod_cast hc
  have haz : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast ha
  have hdz : (P.r 3 : ℤ) ≠ q.val := by omega
  have hsz : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 1
  have hvn : (q.val : ℤ) + q.val - P.g 1 ≠ q.val := by omega
  simp only [fourNegativeInventory, survivingQuartets_cons_prop, survivingQuartets_nil_prop,
    quartetSurvives, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk,
    hbz, hcz, haz, hdz, hsz, hvn, not_true_eq_false, not_false_eq_true,
    and_true, true_and, and_false, false_and, eq_self_iff_true, ite_true, ite_false] <;> simp_all

private theorem middleBC_both_aligned_reading {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (hbP : P.r 1 = q.val) (hcP : P.r 2 = q.val)
    (hbQ : Q.r 1 = q.val) (hcQ : Q.r 2 = q.val)
    (hRow : (P.r 0 : ℤ) = Q.r 0) (hFirstGap : (P.g 0 : ℤ) = Q.g 0) : P = Q := by
  have hdQ : (canonicalPrimitive hQ).totalDegree = 4 := by rw [← he]; exact hd
  have haP := (four_quartic_nonextraction hP hd).2.1
  have haQ := (four_quartic_nonextraction hQ hdQ).2.1
  have hzero := four_quartic_restriction_eq hP hQ hd he
  have hneg := (four_quartic_signed_parts hP hQ hd he).2
  rw [(middleB_reduced_eq hP hbP).2, (middleB_reduced_eq hQ hbQ).2,
    middleBC_negative_list hP hbP hcP haP, middleBC_negative_list hQ hbQ hcQ haQ] at hneg
  simp only [quartetSum_cons, quartetSum_nil, add_zero] at hneg
  have hRowNat : P.r 0 = Q.r 0 := Int.ofNat_inj.mp hRow
  simp only [← hRowNat] at hneg
  have htail : complete (P.g 1) * complete ((q.val : ℤ) + q.val - P.g 1) * complete (P.r 3) =
      complete (Q.g 1) * complete ((q.val : ℤ) + q.val - Q.g 1) * complete (Q.r 3) := by
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ P.r 0 by omega))
    simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hneg
    linear_combination hneg
  have hp01 := hP.thick 0 1 (by decide)
  have hq01 := hQ.thick 0 1 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hp01
  change Q.g 0 + Q.g 1 < Q.r 1 at hq01
  have hpBottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hqBottom : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hread := residual_triple_product_reading
    (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1) (by omega) (by omega)
    (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1) (by omega) (by omega) htail
  have hsEq : (P.g 1 : ℤ) = Q.g 1 := by
    unfold FourRowHessenberg.tripleMatch at hread
    rcases hread with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega
  have hg0 : P.g 0 = Q.g 0 := Int.ofNat_inj.mp hFirstGap
  have hg1 : P.g 1 = Q.g 1 := Int.ofNat_inj.mp hsEq
  obtain ⟨hF, hG⟩ := restriction_full_and_gap_eq hP hQ hzero
  have hprod : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using hG
  rw [hg0, hg1] at hprod
  have hnon : complete (Q.g 0) * complete (Q.g 1) ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega)) ((complete_ne_zero_iff _).mpr (by omega))
  have htEq := complete_injective_nonnegative (by omega) (by omega) (mul_left_cancel₀ hnon hprod)
  have hg2 : P.g 2 = Q.g 2 := Int.ofNat_inj.mp htEq
  rw [fullIndex_four, fullIndex_four] at hF
  have hdEq : (P.r 3 : ℤ) = Q.r 3 := by omega
  apply Profile.ext
  · funext i
    fin_cases i
    · exact hRowNat
    · exact hbP.trans hbQ.symm
    · exact hcP.trans hcQ.symm
    · exact Int.ofNat_inj.mp hdEq
  · funext i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2

private theorem middleB_aligned_reading {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (haP : P.r 0 ≠ q.val) (hbP : P.r 1 = q.val) (hcP : P.r 2 ≠ q.val)
    (haQ : Q.r 0 ≠ q.val) (hbQ : Q.r 1 = q.val) (hcQ : Q.r 2 ≠ q.val)
    (hRow : (P.r 0 : ℤ) = Q.r 0) (hFirstGap : (P.g 0 : ℤ) = Q.g 0) : P = Q := by
  have hzero := four_quartic_restriction_eq hP hQ hd he
  have hlast := low_augmented_derivative_reading
    (restriction q P) (restriction q Q) (P.g 2) (Q.g 2) 1 1
    (by exact_mod_cast hP.gap_pos 2) (by exact_mod_cast hQ.gap_pos 2)
    (by norm_num) (by norm_num)
    (fun j hj => by simpa only [one_mul] using quarticMid_middleB q hP hbP haP hcP j hj)
    (fun j hj => by simpa only [one_mul] using quarticMid_middleB q hQ hbQ haQ hcQ j hj) hzero
  have hg0 : P.g 0 = Q.g 0 := Int.ofNat_inj.mp hFirstGap
  have hg2 : P.g 2 = Q.g 2 := Int.ofNat_inj.mp hlast.1
  obtain ⟨hF, hG⟩ := restriction_full_and_gap_eq hP hQ hzero
  have hprod : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using hG
  rw [hg0, hg2] at hprod
  have hg1poly : complete (P.g 1) = complete (Q.g 1) := by
    apply mul_right_cancel₀ ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ Q.g 2 by omega))
    apply mul_left_cancel₀ ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ Q.g 0 by omega))
    simpa only [mul_assoc] using hprod
  have hsEq := complete_injective_nonnegative
    (show (0 : ℤ) ≤ P.g 1 by omega) (show (0 : ℤ) ≤ Q.g 1 by omega) hg1poly
  have hg1 : P.g 1 = Q.g 1 := Int.ofNat_inj.mp hsEq
  have hRowNat : P.r 0 = Q.r 0 := Int.ofNat_inj.mp hRow
  rw [fullIndex_four, fullIndex_four] at hF
  have hsum : (P.r 2 : ℤ) + P.r 3 = (Q.r 2 : ℤ) + Q.r 3 := by omega
  obtain ⟨hpos, hneg⟩ := four_quartic_signed_parts hP hQ hd he
  have hredP := middleB_reduced_eq hP hbP
  have hredQ := middleB_reduced_eq hQ hbQ
  rw [hredP.1, hredQ.1] at hpos
  rw [hredP.2, hredQ.2] at hneg
  have hlistsP := middleB_inventory_lists hP hbP haP hcP
  have hlistsQ := middleB_inventory_lists hQ hbQ haQ hcQ
  rw [hlistsP.1, hlistsQ.1] at hpos
  rw [hlistsP.2, hlistsQ.2] at hneg
  simp only [quartetSum_cons, quartetSum_nil, add_zero] at hpos hneg
  simp only [← hRowNat, ← hg0, ← hg1, ← hg2] at hpos hneg
  have hW : (P.r 2 : ℤ) + P.r 3 - P.g 2 = (Q.r 2 : ℤ) + Q.r 3 - P.g 2 := by omega
  have hY : (q.val : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 =
      (q.val : ℤ) + Q.r 2 + Q.r 3 - P.g 1 - P.g 2 := by omega
  rw [hW, hY] at hpos
  have hword : quartetTerm ![(P.g 0 : ℤ), P.g 1,
      (P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1, P.r 3] =
      quartetTerm ![(P.g 0 : ℤ), P.g 1,
        (P.r 0 : ℤ) + q.val + Q.r 2 - P.g 0 - P.g 1, Q.r 3] :=
    add_right_cancel hpos
  have hpair : complete ((P.r 0 : ℤ) + q.val + P.r 2 - P.g 0 - P.g 1) * complete (P.r 3) =
      complete ((P.r 0 : ℤ) + q.val + Q.r 2 - P.g 0 - P.g 1) * complete (Q.r 3) := by
    apply mul_left_cancel₀ (mul_ne_zero
      ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ P.g 0 by omega))
      ((complete_ne_zero_iff _).mpr (show (0 : ℤ) ≤ P.g 1 by omega)))
    simpa only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      mul_assoc] using hword
  have hp0 : P.g 0 < P.r 0 := P.g_lt_castSucc 0
  have hp01 := hP.thick 0 1 (by decide)
  have hp12 := hP.thick 1 2 (by decide)
  have hq12 := hQ.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hp01
  change P.g 1 + P.g 2 < P.r 2 at hp12
  change Q.g 1 + Q.g 2 < Q.r 2 at hq12
  have hpBottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hqBottom : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  obtain ⟨hcEq, hdEq⟩ := middleB_fixed_gaps_reading (q.val : ℤ)
    (P.r 0) (P.r 2) (P.r 3) (Q.r 2) (Q.r 3) (P.g 0) (P.g 1) (P.g 2)
    (by exact_mod_cast hP.gap_pos 0) (by exact_mod_cast hP.gap_pos 1)
    (by exact_mod_cast hP.gap_pos 2) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hpair hneg
  apply Profile.ext
  · funext i
    fin_cases i
    · exact hRowNat
    · exact hbP.trans hbQ.symm
    · exact Int.ofNat_inj.mp hcEq
    · exact Int.ofNat_inj.mp hdEq
  · funext i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2

private theorem middleC_aligned_reading {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (haP : P.r 0 ≠ q.val) (hbP : P.r 1 ≠ q.val) (hcP : P.r 2 = q.val)
    (huP : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val)
    (haQ : Q.r 0 ≠ q.val) (hbQ : Q.r 1 ≠ q.val) (hcQ : Q.r 2 = q.val)
    (huQ : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 ≠ q.val)
    (he : restriction q P = restriction q Q)
    (hRow : (P.r 0 : ℤ) = Q.r 0) (hFirstGap : (P.g 0 : ℤ) = Q.g 0) : P = Q := by
  let e : ℤ := (P.r 0 : ℤ) - P.g 0
  let b : ℤ := P.r 1
  let v : ℤ := (P.r 1 : ℤ) + P.r 2 - P.g 1
  let B : ℤ := Q.r 1
  let V : ℤ := (Q.r 1 : ℤ) + Q.r 2 - Q.g 1
  obtain ⟨hF, hG⟩ := restriction_full_and_gap_eq hP hQ he
  have hFraw := hF
  rw [fullIndex_four, fullIndex_four] at hFraw
  have hY : (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 =
      (Q.r 1 : ℤ) + Q.r 2 + Q.r 3 - Q.g 1 - Q.g 2 := by omega
  have hXP : (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 = v + e := by
    dsimp [v, e]
    ring
  have hXQ : (Q.r 0 : ℤ) + Q.r 1 + Q.r 2 - Q.g 0 - Q.g 1 = V + e := by
    dsimp [V, e]
    omega
  have hUP : (P.r 0 : ℤ) + P.r 1 - P.g 0 = b + e := by
    dsimp [b, e]
    ring
  have hUQ : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = B + e := by
    dsimp [B, e]
    omega
  have hshift (j : ℕ+) :
      quarticDelta j (b + e) + quarticDelta j (v + e) - quarticDelta j b - quarticDelta j v =
        quarticDelta j (B + e) + quarticDelta j (V + e) - quarticDelta j B - quarticDelta j V := by
    have hh := congrArg (fun z : CompleteRing =>
      residualAugmentation (MvPolynomial.pderiv j z)) he
    rw [quarticFull_right_derivative q P hP haP hbP hcP huP j,
      quarticFull_right_derivative q Q hQ haQ hbQ hcQ huQ j] at hh
    rw [hXP, hXQ, hUP, hUQ, hY, hFraw, hRow, hFirstGap] at hh
    linear_combination hh
  have hp12 := hP.thick 1 2 (by decide)
  have hq12 := hQ.thick 1 2 (by decide)
  change P.g 1 + P.g 2 < P.r 2 at hp12
  change Q.g 1 + Q.g 2 < Q.r 2 at hq12
  have hpGap := hP.gap_pos 2
  have hqGap := hQ.gap_pos 2
  have hepos : 0 < e := by
    have hh := P.g_lt_castSucc 0
    change P.g 0 < P.r 0 at hh
    dsimp [e]
    omega
  obtain ⟨hbEq, hvEq⟩ := shift_pair_reading e b v B V hepos
    (by dsimp [b]; exact_mod_cast P.r_pos 1)
    (by dsimp [b, v]; omega)
    (by dsimp [B]; exact_mod_cast Q.r_pos 1)
    (by dsimp [B, V]; omega) hshift
  change (P.r 1 : ℤ) = Q.r 1 at hbEq
  have hcPz : (P.r 2 : ℤ) = q.val := by exact_mod_cast hcP
  have hcQz : (Q.r 2 : ℤ) = q.val := by exact_mod_cast hcQ
  have hsEq : (P.g 1 : ℤ) = Q.g 1 := by
    dsimp [v, V] at hvEq
    omega
  have hg0 : P.g 0 = Q.g 0 := Int.ofNat_inj.mp hFirstGap
  have hg1 : P.g 1 = Q.g 1 := Int.ofNat_inj.mp hsEq
  have hprod : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using hG
  rw [hg0, hg1] at hprod
  have hnon : complete (Q.g 0) * complete (Q.g 1) ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega))
      ((complete_ne_zero_iff _).mpr (by omega))
  have hlast := complete_injective_nonnegative (by omega) (by omega)
    (mul_left_cancel₀ hnon hprod)
  have hg2 : P.g 2 = Q.g 2 := Int.ofNat_inj.mp hlast
  have hdEq : (P.r 3 : ℤ) = Q.r 3 := by omega
  apply Profile.ext
  · funext i
    fin_cases i
    · exact Int.ofNat_inj.mp hRow
    · exact Int.ofNat_inj.mp hbEq
    · exact hcP.trans hcQ.symm
    · exact Int.ofNat_inj.mp hdEq
  · funext i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2

private theorem deleted_rows_aligned_reading {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (hSomeP : P.r 1 = q.val ∨ P.r 2 = q.val)
    (hSomeQ : Q.r 1 = q.val ∨ Q.r 2 = q.val)
    (hRow : (P.r 0 : ℤ) = Q.r 0) (hFirst : (P.g 0 : ℤ) = Q.g 0) :
    inventoryCoordinateAlternatives q P Q := by
  have hdQ : (canonicalPrimitive hQ).totalDegree = 4 := by rw [← he]; exact hd
  have haP := (four_quartic_nonextraction hP hd).2.1
  have haQ := (four_quartic_nonextraction hQ hdQ).2.1
  have hzero := four_quartic_restriction_eq hP hQ hd he
  have hstatus := middle_row_contact_status_eq q P Q hP hQ haP haQ hSomeP hSomeQ hzero
  have finish (hEq : P = Q) : inventoryCoordinateAlternatives q P Q :=
    Or.inl ((inventoryData_eq_iff P Q).mpr hEq)
  by_cases hBC : P.r 1 = q.val ∧ P.r 2 = q.val
  · have hBCQ := hstatus.1.mp hBC
    exact finish (middleBC_both_aligned_reading hP hQ hd he
      hBC.1 hBC.2 hBCQ.1 hBCQ.2 hRow hFirst)
  · have hnBCQ : ¬ (Q.r 1 = q.val ∧ Q.r 2 = q.val) :=
      fun h => hBC (hstatus.1.mpr h)
    by_cases hUC : P.r 2 = q.val ∧ (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val
    · have hUCQ := hstatus.2.mp hUC
      exact finish (middleUC_both_aligned_reading hP hQ hd he
        hUC.1 hUC.2 hUCQ.1 hUCQ.2 hRow hFirst)
    · have hnUCQ : ¬ (Q.r 2 = q.val ∧ (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 = q.val) :=
        fun h => hUC (hstatus.2.mpr h)
      by_cases hbP : P.r 1 = q.val
      · have hcP : P.r 2 ≠ q.val := fun h => hBC ⟨hbP, h⟩
        by_cases hbQ : Q.r 1 = q.val
        · have hcQ : Q.r 2 ≠ q.val := fun h => hnBCQ ⟨hbQ, h⟩
          exact finish (middleB_aligned_reading hP hQ hd he
            haP hbP hcP haQ hbQ hcQ hRow hFirst)
        · have hcQ := hSomeQ.resolve_left hbQ
          exact middleBC_aligned_reading hP hQ hd he
            haP hbP hcP haQ hbQ hcQ hRow hFirst
      · have hcP := hSomeP.resolve_left hbP
        have huP : (P.r 0 : ℤ) + P.r 1 - P.g 0 ≠ q.val := fun h => hUC ⟨hcP, h⟩
        by_cases hbQ : Q.r 1 = q.val
        · have hcQ : Q.r 2 ≠ q.val := fun h => hnBCQ ⟨hbQ, h⟩
          exact inventoryCoordinateAlternatives_reverse
            (middleBC_aligned_reading hQ hP hdQ he.symm
              haQ hbQ hcQ haP hbP hcP hRow.symm hFirst.symm)
        · have hcQ := hSomeQ.resolve_left hbQ
          have huQ : (Q.r 0 : ℤ) + Q.r 1 - Q.g 0 ≠ q.val := fun h => hnUCQ ⟨hcQ, h⟩
          exact finish (middleC_aligned_reading hP hQ
            haP hbP hcP huP haQ hbQ hcQ huQ hzero hRow hFirst)

private theorem restriction_second_coefficient_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hA : Q.r 0 ≠ q.val)
    (he : restriction q P = restriction q Q) :
    MvPolynomial.pderiv (secondGenerator hP) (restriction q P) =
      MvPolynomial.pderiv (secondGenerator hQ) (restriction q Q) := by
  have hindex := restriction_second_index_eq hP hQ ha hA he
  have hgen : secondGenerator hP = secondGenerator hQ := by
    apply Subtype.ext
    have hh : ((secondGenerator hP).val : ℤ) = (secondGenerator hQ).val := by
      rw [secondGenerator_val, secondGenerator_val, hindex]
    exact Int.ofNat_inj.mp hh
  simpa only [hgen] using congrArg (MvPolynomial.pderiv (secondGenerator hP)) he

private theorem second_coefficient_augmentation {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) :
    residualAugmentation (MvPolynomial.pderiv (secondGenerator hP) (restriction q P)) =
      (if prefixIndex P = secondIndex P then (1 : ℚ) else 0) +
        (if suffixIndex P = secondIndex P then 1 else 0) := by
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hlast : (P.r 3 : ℤ) ≠ q.val := by omega
  have hgap (i : Fin 3) : bar q (P.g i) = complete (P.g i) :=
    bar_eq_complete_of_ne q _ (by exact_mod_cast hP.gap_ne i)
  have hgp (i : Fin 3) : (0 : ℤ) < P.g i := by exact_mod_cast hP.gap_pos i
  have hr0 : (0 : ℤ) < P.r 0 := by exact_mod_cast P.r_pos 0
  have hr3 : (0 : ℤ) < P.r 3 := by exact_mod_cast P.r_pos 3
  rw [four_second_coefficient hP]
  simp only [hgap 0, hgap 1, hgap 2,
    bar_eq_complete_of_ne q (P.r 0 : ℤ) (by exact_mod_cast ha),
    bar_eq_complete_of_ne q (P.r 3 : ℤ) hlast,
    map_add, apply_ite, map_mul, map_zero, residualAugmentation_complete (hgp 0),
    residualAugmentation_complete (hgp 1), residualAugmentation_complete (hgp 2),
    residualAugmentation_complete hr0, residualAugmentation_complete hr3, one_mul]
  split_ifs <;> rfl

private theorem endpoint_count_tie (x y X Y : ℤ)
    (h : (if x = max x y then (1 : ℚ) else 0) + (if y = max x y then 1 else 0) =
      (if X = max X Y then 1 else 0) + (if Y = max X Y then 1 else 0))
    (hxy : x = y) : X = Y := by
  subst y
  simp only [max_self, if_pos rfl, ite_true] at h
  by_contra hne
  by_cases hle : X ≤ Y
  · rw [max_eq_right hle, if_neg hne, if_pos rfl] at h
    norm_num at h
  · rw [max_eq_left (by omega), if_pos rfl, if_neg (Ne.symm hne)] at h
    norm_num at h

/-- An endpoint tie has augmentation two and cannot match a strict endpoint
coefficient of augmentation one, including coincident numerator monomials. -/
theorem restriction_endpoint_tie_iff {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hA : Q.r 0 ≠ q.val)
    (he : restriction q P = restriction q Q) :
    prefixIndex P = suffixIndex P ↔ prefixIndex Q = suffixIndex Q := by
  have hh := congrArg residualAugmentation (restriction_second_coefficient_eq hP hQ ha hA he)
  rw [second_coefficient_augmentation hP ha, second_coefficient_augmentation hQ hA] at hh
  change
    (if prefixIndex P = max (prefixIndex P) (suffixIndex P) then (1 : ℚ) else 0) +
        (if suffixIndex P = max (prefixIndex P) (suffixIndex P) then 1 else 0) =
      (if prefixIndex Q = max (prefixIndex Q) (suffixIndex Q) then 1 else 0) +
        (if suffixIndex Q = max (prefixIndex Q) (suffixIndex Q) then 1 else 0) at hh
  exact ⟨endpoint_count_tie _ _ _ _ hh, endpoint_count_tie _ _ _ _ hh.symm⟩

private theorem actual_strict_endpoint_ratio {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) (left : Bool)
    (hstrict : if left then prefixIndex P < suffixIndex P else suffixIndex P < prefixIndex P) :
    MvPolynomial.pderiv (secondGenerator hP) (restriction q P) *
        complete (if left then (P.g 0 : ℤ) else P.g 2) =
      gapMonomial P * complete (if left then (P.r 0 : ℤ) else P.r 3) := by
  cases left with
  | false =>
      change suffixIndex P < prefixIndex P at hstrict
      change MvPolynomial.pderiv (secondGenerator hP) (restriction q P) * complete (P.g 2) =
        gapMonomial P * complete (P.r 3)
      have hh := four_strict_prefix_endpoint hP hstrict
      have hbottom : q.val + P.g 2 < P.r 3 := by
        simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
      have hlast : (P.r 3 : ℤ) ≠ q.val := by omega
      rw [four_full_coefficient hP, neg_neg,
        bar_eq_complete_of_ne q _ (by exact_mod_cast hP.gap_ne 2),
        bar_eq_complete_of_ne q _ hlast] at hh
      exact hh
  | true =>
      change prefixIndex P < suffixIndex P at hstrict
      change MvPolynomial.pderiv (secondGenerator hP) (restriction q P) * complete (P.g 0) =
        gapMonomial P * complete (P.r 0)
      have hh := four_strict_suffix_endpoint hP hstrict
      rw [four_full_coefficient hP, neg_neg,
        bar_eq_complete_of_ne q _ (by exact_mod_cast hP.gap_ne 0),
        bar_eq_complete_of_ne q _ (by exact_mod_cast ha)] at hh
      exact hh

/-- In any two strict orientations, actual restriction equality recovers
the ordered endpoint row and its adjacent gap.  No rotated component is assumed. -/
theorem restriction_strict_endpoint_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hA : Q.r 0 ≠ q.val)
    (he : restriction q P = restriction q Q) (leftP leftQ : Bool)
    (hstrictP : if leftP then prefixIndex P < suffixIndex P else suffixIndex P < prefixIndex P)
    (hstrictQ : if leftQ then prefixIndex Q < suffixIndex Q else suffixIndex Q < prefixIndex Q) :
    (if leftP then (P.r 0 : ℤ) else P.r 3) =
        (if leftQ then (Q.r 0 : ℤ) else Q.r 3) ∧
      (if leftP then (P.g 0 : ℤ) else P.g 2) =
        (if leftQ then (Q.g 0 : ℤ) else Q.g 2) := by
  let a : ℤ := if leftP then P.r 0 else P.r 3
  let r : ℤ := if leftP then P.g 0 else P.g 2
  let A : ℤ := if leftQ then Q.r 0 else Q.r 3
  let R : ℤ := if leftQ then Q.g 0 else Q.g 2
  have hM := restriction_second_coefficient_eq hP hQ ha hA he
  obtain ⟨_, hG⟩ := restriction_full_and_gap_eq hP hQ he
  have hp := actual_strict_endpoint_ratio hP ha leftP hstrictP
  have hq := actual_strict_endpoint_ratio hQ hA leftQ hstrictQ
  rw [← hM, ← hG] at hq
  change MvPolynomial.pderiv (secondGenerator hP) (restriction q P) * complete r =
    gapMonomial P * complete a at hp
  change MvPolynomial.pderiv (secondGenerator hP) (restriction q P) * complete R =
    gapMonomial P * complete A at hq
  have hprod : gapMonomial P * (complete a * complete R) =
      gapMonomial P * (complete A * complete r) := by
    linear_combination hq * complete r - hp * complete R
  have hc := mul_left_cancel₀ (gapMonomial_ne_zero P) hprod
  have hdP := P.four_domain hP.thick.hessenberg
  have hdQ := Q.four_domain hQ.thick.hessenberg
  rcases hdP with ⟨hpr, hps, hpt, hpa, hpb, hpc, hpd⟩
  rcases hdQ with ⟨hqr, hqs, hqt, hqa, hqb, hqc, hqd⟩
  have hP0 : (0 : ℤ) < P.g 0 := by exact_mod_cast hP.gap_pos 0
  have hP2 : (0 : ℤ) < P.g 2 := by exact_mod_cast hP.gap_pos 2
  have hQ0 : (0 : ℤ) < Q.g 0 := by exact_mod_cast hQ.gap_pos 0
  have hQ2 : (0 : ℤ) < Q.g 2 := by exact_mod_cast hQ.gap_pos 2
  apply endpoint_ordered_ratio_reading a r A R
  · cases leftP <;> dsimp [r] <;> omega
  · cases leftQ <;> dsimp [R] <;> omega
  · cases leftP <;> dsimp [a, r] <;> omega
  · cases leftQ <;> dsimp [A, R] <;> omega
  · exact hc

/-- At an actual endpoint tie, the two ordered row/gap pairs are recovered
as an unordered pair, with repeated Laurent monomials counted twice. -/
theorem restriction_tied_endpoint_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hA : Q.r 0 ≠ q.val)
    (he : restriction q P = restriction q Q)
    (hxy : prefixIndex P = suffixIndex P) (hXY : prefixIndex Q = suffixIndex Q) :
    (((P.r 0 : ℤ) = Q.r 0 ∧ (P.g 0 : ℤ) = Q.g 0 ∧
        (P.r 3 : ℤ) = Q.r 3 ∧ (P.g 2 : ℤ) = Q.g 2) ∨
      ((P.r 0 : ℤ) = Q.r 3 ∧ (P.g 0 : ℤ) = Q.g 2 ∧
        (P.r 3 : ℤ) = Q.r 0 ∧ (P.g 2 : ℤ) = Q.g 0)) := by
  have hM := restriction_second_coefficient_eq hP hQ ha hA he
  obtain ⟨_, hG⟩ := restriction_full_and_gap_eq hP hQ he
  have hp := four_tied_endpoint_ratio hP hxy
  have hq := four_tied_endpoint_ratio hQ hXY
  have hbP : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hbQ : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hbarP (i : Fin 3) : bar q (P.g i) = complete (P.g i) :=
    bar_eq_complete_of_ne q _ (by exact_mod_cast hP.gap_ne i)
  have hbarQ (i : Fin 3) : bar q (Q.g i) = complete (Q.g i) :=
    bar_eq_complete_of_ne q _ (by exact_mod_cast hQ.gap_ne i)
  rw [four_full_coefficient hP, neg_neg, hbarP 0, hbarP 2,
    bar_eq_complete_of_ne q _ (by exact_mod_cast ha),
    bar_eq_complete_of_ne q _ (by omega)] at hp
  rw [four_full_coefficient hQ, neg_neg, hbarQ 0, hbarQ 2,
    bar_eq_complete_of_ne q _ (by exact_mod_cast hA),
    bar_eq_complete_of_ne q _ (by omega), ← hM, ← hG] at hq
  have hc :
      (complete (P.r 0) * complete (P.g 2) + complete (P.r 3) * complete (P.g 0)) *
          complete (Q.g 0) * complete (Q.g 2) =
        (complete (Q.r 0) * complete (Q.g 2) + complete (Q.r 3) * complete (Q.g 0)) *
          complete (P.g 0) * complete (P.g 2) := by
    apply mul_left_cancel₀ (gapMonomial_ne_zero P)
    linear_combination hq * complete (P.g 0) * complete (P.g 2) -
      hp * complete (Q.g 0) * complete (Q.g 2)
  have hdP := P.four_domain hP.thick.hessenberg
  have hdQ := Q.four_domain hQ.thick.hessenberg
  rcases hdP with ⟨hpr, hps, hpt, hpa, hpb, hpc, hpd⟩
  rcases hdQ with ⟨hqr, hqs, hqt, hqa, hqb, hqc, hqd⟩
  have hP0 : (0 : ℤ) < P.g 0 := by exact_mod_cast hP.gap_pos 0
  have hP2 : (0 : ℤ) < P.g 2 := by exact_mod_cast hP.gap_pos 2
  have hQ0 : (0 : ℤ) < Q.g 0 := by exact_mod_cast hQ.gap_pos 0
  have hQ2 : (0 : ℤ) < Q.g 2 := by exact_mod_cast hQ.gap_pos 2
  exact endpoint_unordered_ratio_reading _ _ _ _ _ _ _ _
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hc

/-- Actual equality aligns the strict endpoint or both tied endpoint pairs,
before any middle-contact case is considered. -/
theorem restriction_endpoint_alignment {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hA : Q.r 0 ≠ q.val)
    (he : restriction q P = restriction q Q) :
    (prefixIndex P < suffixIndex P ∧ prefixIndex Q < suffixIndex Q ∧
      (P.r 0 : ℤ) = Q.r 0 ∧ (P.g 0 : ℤ) = Q.g 0) ∨
    (prefixIndex P < suffixIndex P ∧ suffixIndex Q < prefixIndex Q ∧
      (P.r 0 : ℤ) = Q.r 3 ∧ (P.g 0 : ℤ) = Q.g 2) ∨
    (suffixIndex P < prefixIndex P ∧ prefixIndex Q < suffixIndex Q ∧
      (P.r 3 : ℤ) = Q.r 0 ∧ (P.g 2 : ℤ) = Q.g 0) ∨
    (suffixIndex P < prefixIndex P ∧ suffixIndex Q < prefixIndex Q ∧
      (P.r 3 : ℤ) = Q.r 3 ∧ (P.g 2 : ℤ) = Q.g 2) ∨
    (prefixIndex P = suffixIndex P ∧ prefixIndex Q = suffixIndex Q ∧
      (((P.r 0 : ℤ) = Q.r 0 ∧ (P.g 0 : ℤ) = Q.g 0 ∧
          (P.r 3 : ℤ) = Q.r 3 ∧ (P.g 2 : ℤ) = Q.g 2) ∨
        ((P.r 0 : ℤ) = Q.r 3 ∧ (P.g 0 : ℤ) = Q.g 2 ∧
          (P.r 3 : ℤ) = Q.r 0 ∧ (P.g 2 : ℤ) = Q.g 0))) := by
  have hties := restriction_endpoint_tie_iff hP hQ ha hA he
  rcases lt_trichotomy (prefixIndex P) (suffixIndex P) with hp | hp | hp
  · have hq : prefixIndex Q ≠ suffixIndex Q := by
      intro hq
      exact (ne_of_lt hp) (hties.mpr hq)
    rcases lt_or_gt_of_ne hq with hq | hq
    · obtain ⟨hrow, hgap⟩ := restriction_strict_endpoint_eq hP hQ ha hA he true true hp hq
      exact Or.inl ⟨hp, hq, hrow, hgap⟩
    · obtain ⟨hrow, hgap⟩ := restriction_strict_endpoint_eq hP hQ ha hA he true false hp hq
      exact Or.inr (Or.inl ⟨hp, hq, hrow, hgap⟩)
  · have hq := hties.mp hp
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hp, hq, restriction_tied_endpoint_eq hP hQ ha hA he hp hq⟩)))
  · have hq : prefixIndex Q ≠ suffixIndex Q := by
      intro hq
      exact (ne_of_gt hp) (hties.mpr hq)
    rcases lt_or_gt_of_ne hq with hq | hq
    · obtain ⟨hrow, hgap⟩ := restriction_strict_endpoint_eq hP hQ ha hA he false true hp hq
      exact Or.inr (Or.inr (Or.inl ⟨hp, hq, hrow, hgap⟩))
    · obtain ⟨hrow, hgap⟩ := restriction_strict_endpoint_eq hP hQ ha hA he false false hp hq
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hq, hrow, hgap⟩)))

private theorem diagonal_bc_endpoint_impossible {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (haP : P.r 0 ≠ q.val) (haQ : Q.r 0 ≠ q.val)
    (hbQ : Q.r 1 = q.val) (hcQ : Q.r 2 = q.val)
    (hOrientP : prefixIndex P ≤ suffixIndex P)
    (hOrientQ : prefixIndex Q ≤ suffixIndex Q)
    (he : restriction q P = restriction q Q)
    (hMatch : FourRowHessenberg.fourMatch (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (Q.g 0) (Q.g 2) ((Q.r 0 : ℤ) + q.val - Q.g 0)
      ((q.val : ℤ) + Q.r 3 - Q.g 2)) : False := by
  obtain ⟨_, hG⟩ := restriction_full_and_gap_eq hP hQ he
  have hprod : complete (P.g 0) * complete (P.g 1) * complete (P.g 2) =
      complete (Q.g 0) * complete (Q.g 1) * complete (Q.g 2) := by
    simpa only [gapMonomial, Fin.prod_univ_three, mul_assoc] using hG
  have hg := residual_triple_product_reading
    (show (0 : ℤ) < P.g 0 by exact_mod_cast hP.gap_pos 0)
    (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1)
    (show (0 : ℤ) < P.g 2 by exact_mod_cast hP.gap_pos 2)
    (show (0 : ℤ) < Q.g 0 by exact_mod_cast hQ.gap_pos 0)
    (show (0 : ℤ) < Q.g 1 by exact_mod_cast hQ.gap_pos 1)
    (show (0 : ℤ) < Q.g 2 by exact_mod_cast hQ.gap_pos 2) hprod
  have hsum : (P.g 0 : ℤ) + P.g 1 + P.g 2 = (Q.g 0 : ℤ) + Q.g 1 + Q.g 2 := by
    unfold FourRowHessenberg.tripleMatch at hg
    rcases hg with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> omega
  have hp01 := hP.thick 0 1 (by decide)
  have hp12 := hP.thick 1 2 (by decide)
  have hq01 := hQ.thick 0 1 (by decide)
  have hq12 := hQ.thick 1 2 (by decide)
  change P.g 0 + P.g 1 < P.r 1 at hp01
  change P.g 1 + P.g 2 < P.r 2 at hp12
  change Q.g 0 + Q.g 1 < Q.r 1 at hq01
  change Q.g 1 + Q.g 2 < Q.r 2 at hq12
  have hp0 := P.g_lt_castSucc 0
  change P.g 0 < P.r 0 at hp0
  have hpBottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hqBottom : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hAlignment := restriction_endpoint_alignment hP hQ haP haQ he
  have aligned (hRow : (P.r 0 : ℤ) = Q.r 0) (hGap : (P.g 0 : ℤ) = Q.g 0) : False := by
    have hFirst : (P.r 0 : ℤ) = Q.g 2 := by
      have hm := hMatch
      unfold FourRowHessenberg.fourMatch at hm
      rcases hm with ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩
      all_goals dsimp [prefixIndex, suffixIndex] at hOrientQ
      all_goals omega
    have h0 : (Q.g 0 : ℤ) < P.r 0 := by omega
    have h1 : (Q.g 0 : ℤ) < P.r 1 := by omega
    have h2 : (Q.g 0 : ℤ) < P.r 2 := by omega
    have h3 : (Q.g 0 : ℤ) < P.r 3 := by omega
    have hm := hMatch
    unfold FourRowHessenberg.fourMatch at hm
    rcases hm with ⟨h4, hr⟩ | ⟨h4, hr⟩ | ⟨h4, hr⟩ | ⟨h4, hr⟩
    all_goals unfold FourRowHessenberg.tripleMatch at hr
    all_goals rcases hr with ⟨h5, h6, h7⟩ | ⟨h5, h6, h7⟩ | ⟨h5, h6, h7⟩ |
      ⟨h5, h6, h7⟩ | ⟨h5, h6, h7⟩ | ⟨h5, h6, h7⟩
    all_goals omega
  rcases hAlignment with ⟨hp, hq, hrow, hgap⟩ | ⟨hp, hq, hrow, hgap⟩ |
    ⟨hp, hq, hrow, hgap⟩ | ⟨hp, hq, hrow, hgap⟩ | ⟨hp, hq, hpairs⟩
  · exact aligned hrow hgap
  · omega
  · omega
  · omega
  · rcases hpairs with ⟨ha, hr, hd, ht⟩ | ⟨ha, hr, hd, ht⟩
    · exact aligned ha hr
    · dsimp [prefixIndex, suffixIndex] at hq
      unfold FourRowHessenberg.fourMatch at hMatch
      rcases hMatch with ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩
      all_goals omega

private theorem restriction_no_row_BC_ne {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hrows : ∀ i, P.r i ≠ q.val) (hbQ : Q.r 1 = q.val) (hcQ : Q.r 2 = q.val)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 4)
    (hOrientP : prefixIndex P ≤ suffixIndex P)
    (hOrientQ : prefixIndex Q ≤ suffixIndex Q) :
    restriction q P ≠ restriction q Q := by
  intro he
  have hinit := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  have heps : residualAugmentation
      (Base.initialForm Base.squareWeight.generatorWeight (restriction q Q)) = 1 := by
    rw [← hinit]
    exact restriction_initial_augmentation_one q P hrows
  have hBC := restriction_BC_positive_initial hQ hbQ hcQ hdQ heps
  rw [restriction_square_initial_no_row_contact q P hrows, hBC] at hinit
  have hq0 := Q.g_lt_castSucc 0
  change Q.g 0 < Q.r 0 at hq0
  have hbottom : q.val + Q.g 2 < Q.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hQ.bottom
  have hqpos := q.pos
  have hMatch := FourRowHessenberg.four_product_reading
    (show (0 : ℤ) < P.r 0 by exact_mod_cast P.r_pos 0)
    (show (0 : ℤ) < P.r 1 by exact_mod_cast P.r_pos 1)
    (show (0 : ℤ) < P.r 2 by exact_mod_cast P.r_pos 2)
    (show (0 : ℤ) < P.r 3 by exact_mod_cast P.r_pos 3)
    (show (0 : ℤ) < Q.g 0 by exact_mod_cast hQ.gap_pos 0)
    (show (0 : ℤ) < Q.g 2 by exact_mod_cast hQ.gap_pos 2)
    (show (0 : ℤ) < (Q.r 0 : ℤ) + q.val - Q.g 0 by omega)
    (show (0 : ℤ) < (q.val : ℤ) + Q.r 3 - Q.g 2 by omega)
    (by simpa [Fin.prod_univ_succ, mul_assoc] using hinit)
  exact diagonal_bc_endpoint_impossible hP hQ (hrows 0)
    (four_quartic_nonextraction hQ hdQ).2.1 hbQ hcQ hOrientP hOrientQ he hMatch


private theorem restriction_no_row_transport {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hrows : ∀ i, P.r i ≠ q.val)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 4)
    (hOrientP : prefixIndex P ≤ suffixIndex P)
    (hOrientQ : prefixIndex Q ≤ suffixIndex Q)
    (he : restriction q P = restriction q Q) : ∀ i, Q.r i ≠ q.val := by
  have haQ := (four_quartic_nonextraction hQ hdQ).2.1
  by_cases hbQ : Q.r 1 = q.val
  · by_cases hcQ : Q.r 2 = q.val
    · exact (restriction_no_row_BC_ne hP hQ hrows hbQ hcQ hdQ hOrientP hOrientQ he).elim
    · exact (restriction_no_row_middleB_ne hrows hQ hbQ haQ hcQ he).elim
  · by_cases hcQ : Q.r 2 = q.val
    · exact (restriction_no_row_middleC_ne hrows hQ hcQ haQ hbQ he).elim
    · exact rows_off_cut_of_middle_off hQ haQ hbQ hcQ

/-- Quartic equality cannot replace a surviving diagonal by any deleted-row
stratum, including UC and the mixed-sign BC minimum. -/
theorem restriction_no_row_contact_iff {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hdP : (canonicalPrimitive hP).totalDegree = 4)
    (hdQ : (canonicalPrimitive hQ).totalDegree = 4)
    (hOrientP : prefixIndex P ≤ suffixIndex P)
    (hOrientQ : prefixIndex Q ≤ suffixIndex Q)
    (he : restriction q P = restriction q Q) :
    (∀ i, P.r i ≠ q.val) ↔ ∀ i, Q.r i ≠ q.val := by
  exact ⟨fun hp => restriction_no_row_transport hP hQ hp hdQ hOrientP hOrientQ he,
    fun hq => restriction_no_row_transport hQ hP hq hdP hOrientQ hOrientP he.symm⟩

private theorem endpoint_indices_rotate (P : Profile 3) :
    prefixIndex P.rotate = suffixIndex P ∧ suffixIndex P.rotate = prefixIndex P := by
  constructor <;> simp [prefixIndex, suffixIndex, Profile.rotate, Fin.rev] <;> ring

/-- Rotation is a legal component orientation when the prefix endpoint is
at least as large as the suffix endpoint.  The bottom inequality is derived. -/
theorem component_rotate_of_prefix_ge {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hxy : suffixIndex P ≤ prefixIndex P) :
    QComponent q P.rotate := by
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hleft : q.val + P.g 0 < P.r 0 := by
    dsimp [prefixIndex, suffixIndex] at hxy
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j k hjk
    have hrev : k.rev.succ = j.rev.castSucc := by
      have hh := congrArg (fun i : Fin 4 => i.rev) hjk
      simpa only [Fin.rev_succ, Fin.rev_castSucc] using hh.symm
    have hh := hP.thick k.rev j.rev hrev
    change P.g j.rev + P.g k.rev < P.r j.succ.rev
    rw [Fin.rev_succ, ← hrev]
    omega
  · intro j
    exact hP.gap_pos j.rev
  · intro j
    exact hP.gap_ne j.rev
  · simpa [lastGap, Profile.rotate, Fin.rev, Fin.sum_univ_succ] using hleft

/-- Contact is intrinsic to the actual matrix and is unchanged by rotation. -/
theorem noEntryContact_rotate_iff {n : ℕ} (q : ℕ+) (P : Profile n) :
    NoEntryContact q P.rotate ↔ NoEntryContact q P := by
  have hentry (i j : Fin (n + 1)) :
      P.rotate.xi i - P.rotate.zeta j = P.xi j.rev - P.zeta i.rev := by
    rw [P.xi_rotate, P.zeta_rotate]
    ring
  constructor
  · intro h i j
    have hh := h j.rev i.rev
    rw [hentry] at hh
    simpa only [Fin.rev_rev] using hh
  · intro h i j
    rw [hentry]
    exact h j.rev i.rev



/-- The actual augmentation on the nonendpoint quartic contact domain. -/
noncomputable def quarticScalar (q : ℕ+) (P : Profile 3) : ℚ :=
  let B : ℚ := if (P.r 1 : ℤ) = q.val then 0 else 1
  let C : ℚ := if (P.r 2 : ℤ) = q.val then 0 else 1
  let U : ℚ := if (P.r 0 : ℤ) + P.r 1 - P.g 0 = q.val then 0 else 1
  let V : ℚ := if (P.r 1 : ℤ) + P.r 2 - P.g 1 = q.val then 0 else 1
  let X : ℚ := if prefixIndex P = q.val then 0 else 1
  B * C - U * C - V - B + X + U

theorem four_quartic_scalar {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (haq : P.r 0 ≠ q.val) :
    residualAugmentation (restriction q P) = quarticScalar q P := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hbottom : q.val + P.g 2 < P.r 3 := by
    simpa [lastGap, Fin.sum_univ_succ] using hP.bottom
  have hA : (P.r 0 : ℤ) ≠ q.val := by exact_mod_cast haq
  have hD : (P.r 3 : ℤ) ≠ q.val := by omega
  have hR : (P.g 0 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 0
  have hS : (P.g 1 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 1
  have hT : (P.g 2 : ℤ) ≠ q.val := by exact_mod_cast hP.gap_ne 2
  have hW : (P.r 2 : ℤ) + P.r 3 - P.g 2 ≠ q.val := by omega
  have hY : (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 ≠ q.val := by omega
  have hF : (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 ≠ q.val := by omega
  rw [restriction_four_expansion q P hP.thick]
  simp only [fourInterval, map_sub, map_add, map_mul,
    residualAugmentation_bar q (show (0 : ℤ) < P.r 0 by exact_mod_cast P.r_pos 0),
    residualAugmentation_bar q (show (0 : ℤ) < P.r 1 by exact_mod_cast P.r_pos 1),
    residualAugmentation_bar q (show (0 : ℤ) < P.r 2 by exact_mod_cast P.r_pos 2),
    residualAugmentation_bar q (show (0 : ℤ) < P.r 3 by exact_mod_cast P.r_pos 3),
    residualAugmentation_bar q (show (0 : ℤ) < P.g 0 by exact_mod_cast hP.gap_pos 0),
    residualAugmentation_bar q (show (0 : ℤ) < P.g 1 by exact_mod_cast hP.gap_pos 1),
    residualAugmentation_bar q (show (0 : ℤ) < P.g 2 by exact_mod_cast hP.gap_pos 2),
    residualAugmentation_bar q (show 0 < (P.r 0 : ℤ) + P.r 1 - P.g 0 by omega),
    residualAugmentation_bar q (show 0 < (P.r 1 : ℤ) + P.r 2 - P.g 1 by omega),
    residualAugmentation_bar q (show 0 < (P.r 2 : ℤ) + P.r 3 - P.g 2 by omega),
    residualAugmentation_bar q (show 0 < (P.r 0 : ℤ) + P.r 1 + P.r 2 - P.g 0 - P.g 1 by omega),
    residualAugmentation_bar q (show 0 < (P.r 1 : ℤ) + P.r 2 + P.r 3 - P.g 1 - P.g 2 by omega),
    residualAugmentation_bar q (show 0 < (P.r 0 : ℤ) + P.r 1 + P.r 2 + P.r 3 - P.g 0 - P.g 1 - P.g 2 by omega),
    if_neg hA, if_neg hD, if_neg hR, if_neg hS, if_neg hT,
    if_neg hW, if_neg hY, if_neg hF, one_mul, mul_one]
  dsimp [quarticScalar, prefixIndex]
  ring


/-- Contacted quartic matching after actual endpoint recovery.  The outer
orientation and first endpoint equations are supplied by the proved reading. -/
private theorem four_quartic_inventory_aligned {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (htouch : ¬ (NoEntryContact q P ∧ NoEntryContact q Q))
    (hOrientP : prefixIndex P ≤ suffixIndex P)
    (hOrientQ : prefixIndex Q ≤ suffixIndex Q)
    (hRowEq : (P.r 0 : ℤ) = Q.r 0) (hGapEq : (P.g 0 : ℤ) = Q.g 0) :
    inventoryCoordinateAlternatives q P Q := by
  classical
  have hdQ : (canonicalPrimitive hQ).totalDegree = 4 := by rw [← he]; exact hd
  have haP := (four_quartic_nonextraction hP hd).2.1
  have haQ := (four_quartic_nonextraction hQ hdQ).2.1
  have hzero := four_quartic_restriction_eq hP hQ hd he
  have hrowsIff := restriction_no_row_contact_iff hP hQ hd hdQ hOrientP hOrientQ hzero
  by_cases hrowsP : ∀ i, P.r i ≠ q.val
  · have hrowsQ := hrowsIff.mp hrowsP
    rcases no_rows_aligned_reading hP hQ hrowsP hrowsQ htouch hOrientP
        hRowEq hGapEq hzero with hEq | hRot
    · exact Or.inl ((inventoryData_eq_iff P Q).mpr hEq)
    · exact Or.inr (Or.inl ((inventoryData_eq_iff P Q.rotate).mpr hRot))
  · have hSomeP : P.r 1 = q.val ∨ P.r 2 = q.val := by
      by_contra hn
      push_neg at hn
      exact hrowsP (rows_off_cut_of_middle_off hP haP hn.1 hn.2)
    have hSomeQ : Q.r 1 = q.val ∨ Q.r 2 = q.val := by
      by_contra hn
      push_neg at hn
      have hrowsQ := rows_off_cut_of_middle_off hQ haQ hn.1 hn.2
      exact hrowsP (hrowsIff.mpr hrowsQ)
    exact deleted_rows_aligned_reading hP hQ hd he hSomeP hSomeQ hRowEq hGapEq

private theorem four_quartic_inventory_oriented {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (htouch : ¬ (NoEntryContact q P ∧ NoEntryContact q Q))
    (hOrientP : prefixIndex P ≤ suffixIndex P)
    (hOrientQ : prefixIndex Q ≤ suffixIndex Q) :
    inventoryCoordinateAlternatives q P Q := by
  have hdQ : (canonicalPrimitive hQ).totalDegree = 4 := by rw [← he]; exact hd
  have haP := (four_quartic_nonextraction hP hd).2.1
  have haQ := (four_quartic_nonextraction hQ hdQ).2.1
  have hzero := four_quartic_restriction_eq hP hQ hd he
  have hAlignment := restriction_endpoint_alignment hP hQ haP haQ hzero
  have aligned (hRow : (P.r 0 : ℤ) = Q.r 0) (hGap : (P.g 0 : ℤ) = Q.g 0) :
      inventoryCoordinateAlternatives q P Q :=
    four_quartic_inventory_aligned hP hQ hd he htouch hOrientP hOrientQ hRow hGap
  rcases hAlignment with ⟨hp, hq, ha, hr⟩ | ⟨hp, hq, ha, hr⟩ |
    ⟨hp, hq, ha, hr⟩ | ⟨hp, hq, ha, hr⟩ | ⟨hp, hq, hpairs⟩
  · exact aligned ha hr
  · omega
  · omega
  · omega
  · rcases hpairs with ⟨ha, hr, hLastRow, hLastGap⟩ | ⟨ha, hr, hLastRow, hLastGap⟩
    · exact aligned ha hr
    · have hRotQ := component_rotate_of_prefix_ge hQ (le_of_eq hq.symm)
      have hcanon := canonical_rotate_eq hQ hRotQ
      have heRot : canonicalPrimitive hP = canonicalPrimitive hRotQ := he.trans hcanon.symm
      have htouchRot : ¬ (NoEntryContact q P ∧ NoEntryContact q Q.rotate) := by
        intro hh
        exact htouch ⟨hh.1, (noEntryContact_rotate_iff q Q).mp hh.2⟩
      have hOrientRot : prefixIndex Q.rotate ≤ suffixIndex Q.rotate := by
        rw [(endpoint_indices_rotate Q).1, (endpoint_indices_rotate Q).2]
        omega
      apply inventoryCoordinateAlternatives_unrotate_right
      apply four_quartic_inventory_aligned hP hRotQ hd heRot htouchRot hOrientP hOrientRot
      · simpa [Profile.rotate, Fin.rev] using ha
      · simpa [Profile.rotate, Fin.rev] using hr

private theorem four_quartic_inventory_left_oriented {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (htouch : ¬ (NoEntryContact q P ∧ NoEntryContact q Q))
    (hOrientP : prefixIndex P ≤ suffixIndex P) :
    inventoryCoordinateAlternatives q P Q := by
  by_cases hOrientQ : prefixIndex Q ≤ suffixIndex Q
  · exact four_quartic_inventory_oriented hP hQ hd he htouch hOrientP hOrientQ
  · have hRotQ := component_rotate_of_prefix_ge hQ (by omega)
    have hcanon := canonical_rotate_eq hQ hRotQ
    have heRot : canonicalPrimitive hP = canonicalPrimitive hRotQ := he.trans hcanon.symm
    have htouchRot : ¬ (NoEntryContact q P ∧ NoEntryContact q Q.rotate) := by
      intro hh
      exact htouch ⟨hh.1, (noEntryContact_rotate_iff q Q).mp hh.2⟩
    have hOrientRot : prefixIndex Q.rotate ≤ suffixIndex Q.rotate := by
      rw [(endpoint_indices_rotate Q).1, (endpoint_indices_rotate Q).2]
      omega
    exact inventoryCoordinateAlternatives_unrotate_right
      (four_quartic_inventory_oriented hP hRotQ hd heRot htouchRot hOrientP hOrientRot)

/-- Actual quartic matching first produces legal suffix orientations.
All original component boundaries remain in force. -/
theorem four_quartic_inventory_necessity {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ)
    (htouch : ¬ (NoEntryContact q P ∧ NoEntryContact q Q)) :
    inventoryCoordinateAlternatives q P Q := by
  by_cases hOrientP : prefixIndex P ≤ suffixIndex P
  · exact four_quartic_inventory_left_oriented hP hQ hd he htouch hOrientP
  · have hRotP := component_rotate_of_prefix_ge hP (by omega)
    have hcanon := canonical_rotate_eq hP hRotP
    have hdRot : (canonicalPrimitive hRotP).totalDegree = 4 := by rw [hcanon]; exact hd
    have heRot : canonicalPrimitive hRotP = canonicalPrimitive hQ := hcanon.trans he
    have htouchRot : ¬ (NoEntryContact q P.rotate ∧ NoEntryContact q Q) := by
      intro hh
      exact htouch ⟨(noEntryContact_rotate_iff q P).mp hh.1, hh.2⟩
    have hOrientRot : prefixIndex P.rotate ≤ suffixIndex P.rotate := by
      rw [(endpoint_indices_rotate P).1, (endpoint_indices_rotate P).2]
      omega
    exact inventoryCoordinateAlternatives_unrotate_left
      (four_quartic_inventory_left_oriented hRotP hQ hdRot heRot htouchRot hOrientRot)

/-- Full actual quartic necessity, including every q-component contact,
repeated generator label, source/mate maximum tie, and endpoint tie. -/
theorem four_quartic_residual_necessity {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) :
    quarticResidualAlternatives q P Q := by
  classical
  by_cases hfree : NoEntryContact q P ∧ NoEntryContact q Q
  · exact Or.inr (Or.inr (Or.inl ⟨hfree.1, hfree.2,
      (untouched_four_match_iff hP hQ hfree.1 hfree.2).mp he⟩))
  · exact inventoryCoordinateAlternatives_residual
      (four_quartic_inventory_necessity hP hQ hd he hfree)

/-- Quartic matching of actual canonical primitives in both directions. -/
theorem four_quartic_residual_match_iff {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4) :
    canonicalPrimitive hP = canonicalPrimitive hQ ↔ quarticResidualAlternatives q P Q :=
  ⟨four_quartic_residual_necessity hP hQ hd,
    quarticResidualAlternatives_canonical_eq hP hQ⟩


/-- Size-preserving four-row residual matching in the actual canonical
normalization.  Both directions cover all legal endpoint lifts, constant-gap
cubic exceptions, untouched full-four alternatives, and the r/s residual quartet. -/
theorem staircase_residual_matching {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hsame : (canonicalPrimitive hP).totalDegree = (canonicalPrimitive hQ).totalDegree)
    (hdegree : (canonicalPrimitive hP).totalDegree = 3 ∨
      (canonicalPrimitive hP).totalDegree = 4) :
    canonicalPrimitive hP = canonicalPrimitive hQ ↔
      ((canonicalPrimitive hP).totalDegree = 3 ∧ cubicResidualAlternatives q P Q) ∨
        ((canonicalPrimitive hP).totalDegree = 4 ∧ quarticResidualAlternatives q P Q) := by
  rcases hdegree with hd | hd
  · have hdQ : (canonicalPrimitive hQ).totalDegree = 3 := hsame.symm.trans hd
    have hnot : (canonicalPrimitive hP).totalDegree ≠ 4 := by omega
    simpa only [hd, show (3 : ℕ) ≠ 4 by decide,
      true_and, false_and, or_false] using
      four_cubic_residual_match_iff hP hQ hd hdQ
  · have hnot : (canonicalPrimitive hP).totalDegree ≠ 3 := by omega
    simpa only [hd, show (4 : ℕ) ≠ 3 by decide,
      true_and, false_and, false_or] using
      four_quartic_residual_match_iff hP hQ hd


end SkewJacobiNegative.Staircase
