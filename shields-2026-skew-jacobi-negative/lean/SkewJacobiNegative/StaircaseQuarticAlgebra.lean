/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseCubicMatching

/-!
# Quartic staircase residual algebra

Signed word normalization and exact endpoint coefficients for actual four-row q-components.
-/

namespace SkewJacobiNegative.Staircase

open Gluing HessenbergExpansion

noncomputable def quartetTerm (T : Fin 4 → ℤ) : CompleteRing :=
  complete (T 0) * complete (T 1) * complete (T 2) * complete (T 3)

noncomputable def quartetExponent (T : Fin 4 → ℤ) : ℕ+ →₀ ℕ :=
  hExp (T 0).toNat + hExp (T 1).toNat +
    hExp (T 2).toNat + hExp (T 3).toNat

theorem quartet_relation_term_eq {T U : Fin 4 → ℤ}
    (h : FourRowHessenberg.fourMatch (T 0) (T 1) (T 2) (T 3)
      (U 0) (U 1) (U 2) (U 3)) : quartetTerm T = quartetTerm U := by
  unfold FourRowHessenberg.fourMatch at h
  rcases h with ⟨h0, hr⟩ | ⟨h0, hr⟩ | ⟨h0, hr⟩ | ⟨h0, hr⟩
  all_goals unfold FourRowHessenberg.tripleMatch at hr
  all_goals rcases hr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  all_goals unfold quartetTerm
  all_goals rw [h0, h1, h2, h3] <;> ring

/-- A genuine join cannot preserve its word, even when unrelated factors coincide. -/
theorem quartet_join_ne (U V R S g : ℤ) (hg : 0 < g)
    (hU : g < U) (hV : g < V) (hR : 0 < R) (hS : 0 < S) :
    quartetTerm ![U, V, R, S] ≠ quartetTerm ![g, U + V - g, R, S] := by
  intro he
  have hRS : complete R * complete S ≠ 0 :=
    mul_ne_zero ((complete_ne_zero_iff R).mpr hR.le) ((complete_ne_zero_iff S).mpr hS.le)
  have hpair : complete U * complete V = complete g * complete (U + V - g) := by
    apply mul_right_cancel₀ hRS
    simpa only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, mul_assoc] using he
  have hread := complete_two_product_reading (show 0 < U by omega)
    (show 0 < V by omega) hg (show 0 < U + V - g by omega) hpair
  rcases hread with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> omega


/-- The incomparable first-two-joins and last-single-join words can match only here. -/
theorem quartic_internal_left_locus (a b c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hb : r + s < b) (hc : s + t < c) (hd : t < d)
    (he : FourRowHessenberg.fourMatch r s (a + b + c - r - s) d
      t a b (c + d - t)) : r = t ∧ a = s ∧ d = b := by
  unfold FourRowHessenberg.fourMatch at he
  rcases he with ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩
  all_goals unfold FourRowHessenberg.tripleMatch at hrest
  all_goals rcases hrest with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  all_goals omega

/-- The middle incomparable pair has exactly its two reflected cancellation loci. -/
theorem quartic_internal_middle_locus (a b c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hb : r + s < b) (hc : s + t < c) (hd : t < d)
    (he : FourRowHessenberg.fourMatch r t (a + b - r) (c + d - t)
      s a (b + c - s) d) :
    (s = r ∧ a = t ∧ d = b + t - r) ∨
      (s = t ∧ d = r ∧ a = c + r - s) := by
  unfold FourRowHessenberg.fourMatch at he
  rcases he with ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩
  all_goals unfold FourRowHessenberg.tripleMatch at hrest
  all_goals rcases hrest with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  all_goals omega

/-- The remaining incomparable pair has the reflected endpoint locus. -/
theorem quartic_internal_right_locus (a b c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hb : r + s < b) (hc : s + t < c) (hd : t < d)
    (he : FourRowHessenberg.fourMatch s t a (b + c + d - s - t)
      r (a + b - r) c d) : r = t ∧ s = d ∧ a = c := by
  unfold FourRowHessenberg.fourMatch at he
  rcases he with ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩ | ⟨h0, hrest⟩
  all_goals unfold FourRowHessenberg.tripleMatch at hrest
  all_goals rcases hrest with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  all_goals omega

/-- Among the proper four-row words, only the three incomparable cut pairs
can cancel.  Strict thickness excludes every comparable pair. -/
theorem quartic_opposite_locus (a b c d r s t : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ha : r < a) (hb : r + s < b) (hc : s + t < c) (hd : t < d)
    (X Y : Fin 4 → ℤ)
    (hX : X ∈ [![a, b, c, d], ![r, s, a + b + c - r - s, d],
      ![r, t, a + b - r, c + d - t], ![s, t, a, b + c + d - s - t]])
    (hY : Y ∈ [![r, a + b - r, c, d], ![s, a, b + c - s, d],
      ![t, a, b, c + d - t]])
    (hm : FourRowHessenberg.fourMatch (X 0) (X 1) (X 2) (X 3)
      (Y 0) (Y 1) (Y 2) (Y 3)) :
    (r = t ∧ a = s ∧ d = b ∧
      X = ![r, s, a + b + c - r - s, d] ∧ Y = ![t, a, b, c + d - t]) ∨
    (((s = r ∧ a = t ∧ d = b + t - r) ∨
      (s = t ∧ d = r ∧ a = c + r - s)) ∧
      X = ![r, t, a + b - r, c + d - t] ∧ Y = ![s, a, b + c - s, d]) ∨
    (r = t ∧ s = d ∧ a = c ∧
      X = ![s, t, a, b + c + d - s - t] ∧ Y = ![r, a + b - r, c, d]) := by
  have he := quartet_relation_term_eq hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl | rfl | rfl
  · rcases hY with rfl | rfl | rfl
    · exact ((quartet_join_ne a b c d r hr ha (by omega) (by omega) (by omega)) he).elim
    · apply False.elim
      apply quartet_join_ne b c a d s hs (by omega) (by omega) (by omega) (by omega)
      dsimp [quartetTerm] at he ⊢
      linear_combination he
    · apply False.elim
      apply quartet_join_ne c d a b t ht (by omega) hd (by omega) (by omega)
      dsimp [quartetTerm] at he ⊢
      linear_combination he
  · rcases hY with rfl | rfl | rfl
    · apply False.elim
      apply quartet_join_ne (a + b - r) c r d s hs (by omega) (by omega) hr (by omega)
      have hindex : a + b - r + c - s = a + b + c - r - s := by omega
      dsimp [quartetTerm] at he ⊢
      rw [hindex]
      linear_combination -he
    · apply False.elim
      apply quartet_join_ne a (b + c - s) s d r hr ha (by omega) hs (by omega)
      have hindex : a + (b + c - s) - r = a + b + c - r - s := by omega
      dsimp [quartetTerm] at he ⊢
      rw [hindex]
      linear_combination -he
    · obtain ⟨h0, h1, h2⟩ := quartic_internal_left_locus a b c d r s t hr hs ht ha hb hc hd hm
      exact Or.inl ⟨h0, h1, h2, rfl, rfl⟩
  · rcases hY with rfl | rfl | rfl
    · apply False.elim
      apply quartet_join_ne c d r (a + b - r) t ht (by omega) hd hr (by omega)
      dsimp [quartetTerm] at he ⊢
      linear_combination -he
    · exact Or.inr (Or.inl
        ⟨quartic_internal_middle_locus a b c d r s t hr hs ht ha hb hc hd hm, rfl, rfl⟩)
    · apply False.elim
      apply quartet_join_ne a b t (c + d - t) r hr ha (by omega) ht (by omega)
      dsimp [quartetTerm] at he ⊢
      linear_combination -he
  · rcases hY with rfl | rfl | rfl
    · obtain ⟨h0, h1, h2⟩ := quartic_internal_right_locus a b c d r s t hr hs ht ha hb hc hd hm
      exact Or.inr (Or.inr ⟨h0, h1, h2, rfl, rfl⟩)
    · apply False.elim
      apply quartet_join_ne (b + c - s) d s a t ht (by omega) hd hs (by omega)
      have hindex : b + c - s + d - t = b + c + d - s - t := by omega
      dsimp [quartetTerm] at he ⊢
      rw [hindex]
      linear_combination -he
    · apply False.elim
      apply quartet_join_ne b (c + d - t) t a s hs (by omega) (by omega) ht (by omega)
      have hindex : b + (c + d - t) - s = b + c + d - s - t := by omega
      dsimp [quartetTerm] at he ⊢
      rw [hindex]
      linear_combination -he

private theorem quartic_cancel_left_eq (a b c d r s t : ℤ)
    (h : r = t ∧ a = s ∧ d = b) :
    quartetTerm ![r, s, a + b + c - r - s, d] =
      quartetTerm ![t, a, b, c + d - t] := by
  rcases h with ⟨h0, h1, h2⟩
  have hindex : a + b + c - r - s = c + d - t := by omega
  simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [hindex, h0, ← h1, h2]
  ring

private theorem quartic_cancel_middle_eq (a b c d r s t : ℤ)
    (h : (s = r ∧ a = t ∧ d = b + t - r) ∨
      (s = t ∧ d = r ∧ a = c + r - s)) :
    quartetTerm ![r, t, a + b - r, c + d - t] =
      quartetTerm ![s, a, b + c - s, d] := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have hU : a + b - r = d := by omega
    have hW : c + d - t = b + c - s := by omega
    simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [hU, hW, h0, h1]
    ring
  · have hU : a + b - r = b + c - s := by omega
    have hW : c + d - t = a := by omega
    simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [hU, hW, h0, h1, h2]
    ring

private theorem quartic_cancel_right_eq (a b c d r s t : ℤ)
    (h : r = t ∧ s = d ∧ a = c) :
    quartetTerm ![s, t, a, b + c + d - s - t] =
      quartetTerm ![r, a + b - r, c, d] := by
  rcases h with ⟨h0, h1, h2⟩
  have hindex : b + c + d - s - t = a + b - r := by omega
  simp only [quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [hindex, h0, h1, h2]
  ring


def QuartetPositive (L : List (Fin 4 → ℤ)) : Prop :=
  ∀ T ∈ L, ∀ j, 0 < T j

noncomputable def quartetSum (L : List (Fin 4 → ℤ)) : CompleteRing :=
  (L.map quartetTerm).sum

@[simp] theorem quartetSum_nil : quartetSum [] = 0 := rfl

@[simp] theorem quartetSum_cons (T : Fin 4 → ℤ) (L : List (Fin 4 → ℤ)) :
    quartetSum (T :: L) = quartetTerm T + quartetSum L := rfl

theorem quartetSum_append (L R : List (Fin 4 → ℤ)) :
    quartetSum (L ++ R) = quartetSum L + quartetSum R := by
  simp [quartetSum, List.map_append, List.sum_append]

theorem quartetTerm_monomial (T : Fin 4 → ℤ) (hT : ∀ j, 0 < T j) :
    quartetTerm T = MvPolynomial.monomial (quartetExponent T) 1 := by
  rw [quartetTerm, complete_eq_hh, complete_eq_hh, complete_eq_hh,
    complete_eq_hh, hh_eq_monomial (hT 0).le, hh_eq_monomial (hT 1).le,
    hh_eq_monomial (hT 2).le, hh_eq_monomial (hT 3).le,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial]
  simp [quartetExponent]

theorem quartetPositive_tail {T : Fin 4 → ℤ} {L : List (Fin 4 → ℤ)}
    (h : QuartetPositive (T :: L)) : QuartetPositive L := by
  intro U hU j
  exact h U (by simp [hU]) j

theorem quartetPositive_eraseIdx {L : List (Fin 4 → ℤ)}
    (h : QuartetPositive L) (i : ℕ) : QuartetPositive (L.eraseIdx i) := by
  intro U hU j
  exact h U (List.mem_of_mem_eraseIdx hU) j

theorem quartetSum_coeff_nonnegative (L : List (Fin 4 → ℤ))
    (hL : QuartetPositive L) (e : ℕ+ →₀ ℕ) :
    0 ≤ (quartetSum L).coeff e := by
  induction L with
  | nil => simp
  | cons T L ih =>
    have hT := hL T (by simp)
    have hrest := ih (quartetPositive_tail hL)
    rw [quartetSum_cons, MvPolynomial.coeff_add, quartetTerm_monomial T hT,
      MvPolynomial.coeff_monomial]
    split_ifs <;> linarith

theorem quartetSum_coeff_zero_of_no_matching_exponent
    (L : List (Fin 4 → ℤ)) (hL : QuartetPositive L) (e : ℕ+ →₀ ℕ)
    (hn : ∀ T ∈ L, quartetExponent T ≠ e) :
    (quartetSum L).coeff e = 0 := by
  induction L with
  | nil => simp
  | cons T L ih =>
    have hT := hL T (by simp)
    have hne := hn T (by simp)
    have hrest := ih (quartetPositive_tail hL) (by
      intro U hU
      exact hn U (by simp [hU]))
    rw [quartetSum_cons, MvPolynomial.coeff_add, quartetTerm_monomial T hT,
      MvPolynomial.coeff_monomial, if_neg hne, hrest, zero_add]

theorem quartetSum_augmentation (L : List (Fin 4 → ℤ))
    (hL : QuartetPositive L) : residualAugmentation (quartetSum L) = L.length := by
  induction L with
  | nil => simp
  | cons T L ih =>
    have hT := hL T (by simp)
    rw [quartetSum_cons, map_add]
    simp only [quartetTerm, map_mul, residualAugmentation_complete (hT 0),
      residualAugmentation_complete (hT 1), residualAugmentation_complete (hT 2),
      residualAugmentation_complete (hT 3), one_mul]
    rw [ih (quartetPositive_tail hL)]
    simp [List.length_cons, add_comm]

theorem quartetSum_lengths {L R : List (Fin 4 → ℤ)}
    (hL : QuartetPositive L) (hR : QuartetPositive R)
    (he : quartetSum L = quartetSum R) : L.length = R.length := by
  have hh := congrArg residualAugmentation he
  rw [quartetSum_augmentation L hL, quartetSum_augmentation R hR] at hh
  exact_mod_cast hh

private theorem quartetSum_monomial (L : List (Fin 4 → ℤ))
    (hL : QuartetPositive L) :
    quartetSum L =
      (L.map (fun T => (MvPolynomial.monomial (quartetExponent T) 1 : CompleteRing))).sum := by
  induction L with
  | nil => rfl
  | cons T L ih =>
      have hT := hL T (by simp)
      rw [quartetSum_cons, quartetTerm_monomial T hT, ih (quartetPositive_tail hL)]
      rfl

/-- Collected quartic words have unique positive and negative parts once their
own opposite signs are disjoint.  No distinctness within a sign is required. -/
theorem quartet_signed_parts_unique (PP NP PQ NQ : List (Fin 4 → ℤ))
    (hpP : QuartetPositive PP) (hnP : QuartetPositive NP)
    (hpQ : QuartetPositive PQ) (hnQ : QuartetPositive NQ)
    (hdP : ∀ x ∈ PP, ∀ y ∈ NP,
      ¬ FourRowHessenberg.fourMatch (x 0) (x 1) (x 2) (x 3)
        (y 0) (y 1) (y 2) (y 3))
    (hdQ : ∀ x ∈ PQ, ∀ y ∈ NQ,
      ¬ FourRowHessenberg.fourMatch (x 0) (x 1) (x 2) (x 3)
        (y 0) (y 1) (y 2) (y 3))
    (he : quartetSum PP + quartetSum NQ = quartetSum NP + quartetSum PQ) :
    quartetSum PP = quartetSum PQ ∧ quartetSum NP = quartetSum NQ := by
  have hdisP : ∀ x ∈ PP, ∀ y ∈ NP, quartetExponent x ≠ quartetExponent y := by
    intro x hx y hy hxy
    apply hdP x hx y hy
    have hp := hpP x hx
    have hn := hnP y hy
    apply FourRowHessenberg.four_product_reading
      (hp 0) (hp 1) (hp 2) (hp 3) (hn 0) (hn 1) (hn 2) (hn 3)
    change quartetTerm x = quartetTerm y
    rw [quartetTerm_monomial x hp, quartetTerm_monomial y hn, hxy]
  have hdisQ : ∀ x ∈ PQ, ∀ y ∈ NQ, quartetExponent x ≠ quartetExponent y := by
    intro x hx y hy hxy
    apply hdQ x hx y hy
    have hp := hpQ x hx
    have hn := hnQ y hy
    apply FourRowHessenberg.four_product_reading
      (hp 0) (hp 1) (hp 2) (hp 3) (hn 0) (hn 1) (hn 2) (hn 3)
    change quartetTerm x = quartetTerm y
    rw [quartetTerm_monomial x hp, quartetTerm_monomial y hn, hxy]
  rw [quartetSum_monomial PP hpP, quartetSum_monomial NP hnP,
    quartetSum_monomial PQ hpQ, quartetSum_monomial NQ hnQ] at he ⊢
  exact CubicNecessity.signed_monomial_parts_unique quartetExponent PP NP PQ NQ hdisP hdisQ he

/-- Exact one-occurrence cancellation in a collected positive sum.  Repeated
monomials and repeated factors require no distinctness hypothesis. -/
theorem quartetSum_head_reading (T : Fin 4 → ℤ)
    (L R : List (Fin 4 → ℤ))
    (hL : QuartetPositive (T :: L)) (hR : QuartetPositive R)
    (he : quartetSum (T :: L) = quartetSum R) :
    ∃ i : Fin R.length,
      FourRowHessenberg.fourMatch (T 0) (T 1) (T 2) (T 3)
        ((R.get i) 0) ((R.get i) 1) ((R.get i) 2) ((R.get i) 3) ∧
      quartetSum L = quartetSum (R.eraseIdx i.val) ∧
      QuartetPositive L ∧ QuartetPositive (R.eraseIdx i.val) := by
  classical
  have hT := hL T (by simp)
  have hfound : ∃ U ∈ R, quartetExponent U = quartetExponent T := by
    by_contra hn
    push_neg at hn
    have hz := quartetSum_coeff_zero_of_no_matching_exponent R hR
      (quartetExponent T) hn
    have hh := congrArg (fun p : CompleteRing => p.coeff (quartetExponent T)) he
    rw [quartetSum_cons, MvPolynomial.coeff_add, quartetTerm_monomial T hT,
      MvPolynomial.coeff_monomial, if_pos rfl, hz] at hh
    have hp := quartetSum_coeff_nonnegative L (quartetPositive_tail hL)
      (quartetExponent T)
    linarith
  obtain ⟨i, hi⟩ := (List.exists_mem_iff_get
    (l := R) (p := fun U => quartetExponent U = quartetExponent T)).mp hfound
  have hRi : ∀ j, 0 < (R.get i) j := hR _ (by
    simpa only [List.get_eq_getElem] using List.getElem_mem i.isLt)
  have hprod : quartetTerm T = quartetTerm (R.get i) := by
    rw [quartetTerm_monomial T hT, quartetTerm_monomial (R.get i) hRi, hi]
  have hmatch := FourRowHessenberg.four_product_reading
    (hT 0) (hT 1) (hT 2) (hT 3) (hRi 0) (hRi 1) (hRi 2) (hRi 3)
    (by simpa only [quartetTerm] using hprod)
  have hperm := List.getElem_cons_eraseIdx_perm (l := R) i.isLt
  have hsum : quartetTerm (R.get i) + quartetSum (R.eraseIdx i.val) = quartetSum R := by
    simpa [quartetSum, List.get_eq_getElem] using (hperm.map quartetTerm).sum_eq
  refine ⟨i, hmatch, ?_, quartetPositive_tail hL, quartetPositive_eraseIdx hR i.val⟩
  rw [quartetSum_cons] at he
  linear_combination he - hsum - hprod

def quartetSurvives (q : ℕ+) (T : Fin 4 → ℤ) : Prop :=
  T 0 ≠ (q.val : ℤ) ∧ T 1 ≠ (q.val : ℤ) ∧
    T 2 ≠ (q.val : ℤ) ∧ T 3 ≠ (q.val : ℤ)

instance quartetSurvivesDecidable (q : ℕ+) (T : Fin 4 → ℤ) :
    Decidable (quartetSurvives q T) := by
  unfold quartetSurvives
  infer_instance

noncomputable def survivingQuartets (q : ℕ+) (L : List (Fin 4 → ℤ)) :
    List (Fin 4 → ℤ) := L.filter (fun T => decide (quartetSurvives q T))

noncomputable def barredQuartetSum (q : ℕ+) (L : List (Fin 4 → ℤ)) : CompleteRing :=
  (L.map (fun T => bar q (T 0) * bar q (T 1) * bar q (T 2) * bar q (T 3))).sum

theorem barredQuartet_eq (q : ℕ+) (T : Fin 4 → ℤ) :
    bar q (T 0) * bar q (T 1) * bar q (T 2) * bar q (T 3) =
      if quartetSurvives q T then quartetTerm T else 0 := by
  classical
  by_cases h0 : T 0 = (q.val : ℤ) <;>
    by_cases h1 : T 1 = (q.val : ℤ) <;>
    by_cases h2 : T 2 = (q.val : ℤ) <;>
    by_cases h3 : T 3 = (q.val : ℤ) <;>
    simp [quartetSurvives, quartetTerm, bar, eraseGenerator_complete, h0, h1, h2, h3]

theorem barredQuartetSum_eq_surviving (q : ℕ+) (L : List (Fin 4 → ℤ)) :
    barredQuartetSum q L = quartetSum (survivingQuartets q L) := by
  classical
  induction L with
  | nil => simp [barredQuartetSum, survivingQuartets, quartetSum]
  | cons T L ih =>
    change (bar q (T 0) * bar q (T 1) * bar q (T 2) * bar q (T 3)) +
      barredQuartetSum q L = _
    rw [barredQuartet_eq, ih]
    by_cases hT : quartetSurvives q T <;>
      simp [survivingQuartets, hT, quartetSum]

/-- The full-index term is excluded here because it is read and cancelled
separately, together with its repeated gap monomial. -/
def fourPositiveInventory (P : Profile 3) : List (Fin 4 → ℤ) :=
  [![(P.r 0 : ℤ), P.r 1, P.r 2, P.r 3],
   ![(P.g 0 : ℤ), P.g 1, prefixIndex P, P.r 3],
   ![(P.g 0 : ℤ), P.g 2, (P.r 0 : ℤ) + P.r 1 - P.g 0,
      (P.r 2 : ℤ) + P.r 3 - P.g 2],
   ![(P.g 1 : ℤ), P.g 2, P.r 0, suffixIndex P]]

def fourNegativeInventory (P : Profile 3) : List (Fin 4 → ℤ) :=
  [![(P.g 0 : ℤ), (P.r 0 : ℤ) + P.r 1 - P.g 0, P.r 2, P.r 3],
   ![(P.g 1 : ℤ), P.r 0, (P.r 1 : ℤ) + P.r 2 - P.g 1, P.r 3],
   ![(P.g 2 : ℤ), P.r 0, P.r 1, (P.r 2 : ℤ) + P.r 3 - P.g 2]]

def fourCancellationLeft (P : Profile 3) : Prop :=
  (P.g 0 : ℤ) = P.g 2 ∧ (P.r 0 : ℤ) = P.g 1 ∧ (P.r 3 : ℤ) = P.r 1

def fourCancellationMiddle (P : Profile 3) : Prop :=
  ((P.g 1 : ℤ) = P.g 0 ∧ (P.r 0 : ℤ) = P.g 2 ∧
      (P.r 3 : ℤ) = P.r 1 + P.g 2 - P.g 0) ∨
    ((P.g 1 : ℤ) = P.g 2 ∧ (P.r 3 : ℤ) = P.g 0 ∧
      (P.r 0 : ℤ) = P.r 2 + P.g 0 - P.g 1)

def fourCancellationRight (P : Profile 3) : Prop :=
  (P.g 0 : ℤ) = P.g 2 ∧ (P.g 1 : ℤ) = P.r 3 ∧ (P.r 0 : ℤ) = P.r 2

instance (P : Profile 3) : Decidable (fourCancellationLeft P) := by
  unfold fourCancellationLeft
  infer_instance

instance (P : Profile 3) : Decidable (fourCancellationMiddle P) := by
  unfold fourCancellationMiddle
  infer_instance

instance (P : Profile 3) : Decidable (fourCancellationRight P) := by
  unfold fourCancellationRight
  infer_instance

/-- Cancellation removes one occurrence of each sign before specialization. -/
def fourReducedPositive (P : Profile 3) : List (Fin 4 → ℤ) :=
  if fourCancellationLeft P then (fourPositiveInventory P).eraseIdx 1
  else if fourCancellationMiddle P then (fourPositiveInventory P).eraseIdx 2
  else if fourCancellationRight P then (fourPositiveInventory P).eraseIdx 3
  else fourPositiveInventory P

def fourReducedNegative (P : Profile 3) : List (Fin 4 → ℤ) :=
  if fourCancellationLeft P then (fourNegativeInventory P).eraseIdx 2
  else if fourCancellationMiddle P then (fourNegativeInventory P).eraseIdx 1
  else if fourCancellationRight P then (fourNegativeInventory P).eraseIdx 0
  else fourNegativeInventory P

theorem fourReduced_parts (P : Profile 3) :
    quartetSum (fourPositiveInventory P) - quartetSum (fourNegativeInventory P) =
      quartetSum (fourReducedPositive P) - quartetSum (fourReducedNegative P) := by
  by_cases hL : fourCancellationLeft P
  · have hc := quartic_cancel_left_eq (P.r 0) (P.r 1) (P.r 2) (P.r 3)
      (P.g 0) (P.g 1) (P.g 2) hL
    simp only [fourReducedPositive, fourReducedNegative, if_pos hL]
    simp [fourPositiveInventory, fourNegativeInventory, List.eraseIdx, quartetSum,
      prefixIndex, suffixIndex]
    linear_combination hc
  · by_cases hM : fourCancellationMiddle P
    · have hc := quartic_cancel_middle_eq (P.r 0) (P.r 1) (P.r 2) (P.r 3)
        (P.g 0) (P.g 1) (P.g 2) hM
      simp only [fourReducedPositive, fourReducedNegative, if_neg hL, if_pos hM]
      simp [fourPositiveInventory, fourNegativeInventory, List.eraseIdx, quartetSum,
        prefixIndex, suffixIndex]
      linear_combination hc
    · by_cases hR : fourCancellationRight P
      · have hc := quartic_cancel_right_eq (P.r 0) (P.r 1) (P.r 2) (P.r 3)
          (P.g 0) (P.g 1) (P.g 2) hR
        simp only [fourReducedPositive, fourReducedNegative, if_neg hL, if_neg hM, if_pos hR]
        simp [fourPositiveInventory, fourNegativeInventory, List.eraseIdx, quartetSum,
          prefixIndex, suffixIndex]
        linear_combination hc
      · simp only [fourReducedPositive, fourReducedNegative, if_neg hL, if_neg hM, if_neg hR]

theorem fourReducedPositive_mem {P : Profile 3} {X : Fin 4 → ℤ}
    (hX : X ∈ fourReducedPositive P) : X ∈ fourPositiveInventory P := by
  unfold fourReducedPositive at hX
  split_ifs at hX <;> first
  | exact List.mem_of_mem_eraseIdx hX
  | exact hX

theorem fourReducedNegative_mem {P : Profile 3} {X : Fin 4 → ℤ}
    (hX : X ∈ fourReducedNegative P) : X ∈ fourNegativeInventory P := by
  unfold fourReducedNegative at hX
  split_ifs at hX <;> first
  | exact List.mem_of_mem_eraseIdx hX
  | exact hX

/-- After its unique possible incomparable cancellation, an actual thick
four-row inventory has disjoint signs, even at repeated generator labels. -/
theorem fourReduced_sign_disjoint {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    ∀ X ∈ fourReducedPositive P, ∀ Y ∈ fourReducedNegative P,
      ¬ FourRowHessenberg.fourMatch (X 0) (X 1) (X 2) (X 3)
        (Y 0) (Y 1) (Y 2) (Y 3) := by
  intro X hX Y hY hm
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hgr : (0 : ℤ) < P.g 0 := by exact_mod_cast hP.gap_pos 0
  have hgs : (0 : ℤ) < P.g 1 := by exact_mod_cast hP.gap_pos 1
  have hgt : (0 : ℤ) < P.g 2 := by exact_mod_cast hP.gap_pos 2
  have hXp := fourReducedPositive_mem hX
  have hYn := fourReducedNegative_mem hY
  have hloc := quartic_opposite_locus (P.r 0) (P.r 1) (P.r 2) (P.r 3)
    (P.g 0) (P.g 1) (P.g 2) hgr hgs hgt
    (by omega) (by omega) (by omega) (by omega) X Y
    (by simpa only [fourPositiveInventory, prefixIndex, suffixIndex] using hXp)
    (by simpa only [fourNegativeInventory] using hYn) hm
  clear hm hXp hYn hP
  unfold fourReducedPositive at hX
  unfold fourReducedNegative at hY
  split_ifs at hX hY
  all_goals simp [fourPositiveInventory, fourNegativeInventory, List.eraseIdx,
    prefixIndex, suffixIndex] at hX hY
  all_goals
    repeat' first
    | (rcases hX with hX | hX)
    | (rcases hY with hY | hY)
    | (subst X)
    | (subst Y)
  all_goals rcases hloc with ⟨h0, h1, h2, hXp, hYn⟩ |
    ⟨h0, hXp, hYn⟩ | ⟨h0, h1, h2, hXp, hYn⟩
  all_goals
    have hx0 := congrFun hXp 0
    have hx1 := congrFun hXp 1
    have hx2 := congrFun hXp 2
    have hx3 := congrFun hXp 3
    have hy0 := congrFun hYn 0
    have hy1 := congrFun hYn 1
    have hy2 := congrFun hYn 2
    have hy3 := congrFun hYn 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk] at hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3
    dsimp [fourCancellationLeft, fourCancellationMiddle, fourCancellationRight] at *
    omega

theorem fourInventory_positive {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    QuartetPositive (fourPositiveInventory P ++ fourNegativeInventory P) := by
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hgr : (0 : ℤ) < P.g 0 := by exact_mod_cast hP.gap_pos 0
  have hgs : (0 : ℤ) < P.g 1 := by exact_mod_cast hP.gap_pos 1
  have hgt : (0 : ℤ) < P.g 2 := by exact_mod_cast hP.gap_pos 2
  intro T hT j
  simp only [fourPositiveInventory, fourNegativeInventory, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  all_goals fin_cases j <;>
    simp [prefixIndex, suffixIndex] <;> omega

theorem eraseGenerator_quartetSum (q : ℕ+) (L : List (Fin 4 → ℤ)) :
    eraseGenerator q (quartetSum L) = quartetSum (survivingQuartets q L) := by
  rw [← barredQuartetSum_eq_surviving]
  induction L with
  | nil => simp [quartetSum, barredQuartetSum]
  | cons T L ih =>
      simp only [quartetSum_cons, map_add, quartetTerm, map_mul]
      change
        bar q (T 0) * bar q (T 1) * bar q (T 2) * bar q (T 3) +
          eraseGenerator q (quartetSum L) = _
      rw [ih]
      rfl

theorem fourReduced_surviving_parts (q : ℕ+) (P : Profile 3) :
    quartetSum (survivingQuartets q (fourPositiveInventory P)) -
        quartetSum (survivingQuartets q (fourNegativeInventory P)) =
      quartetSum (survivingQuartets q (fourReducedPositive P)) -
        quartetSum (survivingQuartets q (fourReducedNegative P)) := by
  have he := congrArg (eraseGenerator q) (fourReduced_parts P)
  simpa only [map_sub, eraseGenerator_quartetSum] using he

theorem fourReduced_surviving_positive {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) :
    QuartetPositive (survivingQuartets q (fourReducedPositive P)) ∧
      QuartetPositive (survivingQuartets q (fourReducedNegative P)) := by
  have hpos := fourInventory_positive hP
  constructor
  · intro X hX i
    exact hpos X (List.mem_append.mpr
      (Or.inl (fourReducedPositive_mem (List.mem_filter.mp hX).1))) i
  · intro X hX i
    exact hpos X (List.mem_append.mpr
      (Or.inr (fourReducedNegative_mem (List.mem_filter.mp hX).1))) i

private theorem fourReduced_surviving_disjoint {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) :
    ∀ X ∈ survivingQuartets q (fourReducedPositive P),
      ∀ Y ∈ survivingQuartets q (fourReducedNegative P),
      ¬ FourRowHessenberg.fourMatch (X 0) (X 1) (X 2) (X 3)
        (Y 0) (Y 1) (Y 2) (Y 3) := by
  intro X hX Y hY
  exact fourReduced_sign_disjoint hP X (List.mem_filter.mp hX).1 Y (List.mem_filter.mp hY).1

theorem four_restriction_inventory {q : ℕ+} {P : Profile 3} (hP : QComponent q P) :
    restriction q P =
      quartetSum (survivingQuartets q (fourPositiveInventory P)) -
      quartetSum (survivingQuartets q (fourNegativeInventory P)) -
      gapMonomial P * complete (fullIndex P) := by
  rw [← barredQuartetSum_eq_surviving, ← barredQuartetSum_eq_surviving,
    restriction_four_expansion q P hP.thick]
  have hfull : bar q (fullIndex P) = complete (fullIndex P) :=
    bar_eq_complete_of_ne q _ (ne_of_gt (fullIndex_gt_q hP))
  have hgap (j : Fin 3) : bar q (P.g j) = complete (P.g j) :=
    bar_eq_complete_of_ne q _ (by exact_mod_cast hP.gap_ne j)
  simp only [barredQuartetSum, fourPositiveInventory, fourNegativeInventory,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    fourInterval, prefixIndex, suffixIndex, gapMonomial,
    Fin.prod_univ_three, add_zero,
    hgap 0, hgap 1, hgap 2]
  rw [fullIndex_four] at hfull ⊢
  rw [hfull]
  ring

theorem four_restriction_reduced_inventory {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) :
    restriction q P =
      quartetSum (survivingQuartets q (fourReducedPositive P)) -
        quartetSum (survivingQuartets q (fourReducedNegative P)) -
        gapMonomial P * complete (fullIndex P) := by
  rw [four_restriction_inventory hP, fourReduced_surviving_parts]

/-- Actual canonical equality, not a matching hypothesis, supplies both
normalized quartic inventories with their complete multiplicities. -/
theorem four_quartic_signed_parts {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (hd : (canonicalPrimitive hP).totalDegree = 4)
    (he : canonicalPrimitive hP = canonicalPrimitive hQ) :
    quartetSum (survivingQuartets q (fourReducedPositive P)) =
        quartetSum (survivingQuartets q (fourReducedPositive Q)) ∧
      quartetSum (survivingQuartets q (fourReducedNegative P)) =
        quartetSum (survivingQuartets q (fourReducedNegative Q)) := by
  have hzero := four_quartic_restriction_eq hP hQ hd he
  obtain ⟨hfull, hgap⟩ := restriction_full_and_gap_eq hP hQ hzero
  have htop : gapMonomial P * complete (fullIndex P) =
      gapMonomial Q * complete (fullIndex Q) := by rw [hfull, hgap]
  have hp := fourReduced_surviving_positive hP
  have hq := fourReduced_surviving_positive hQ
  apply quartet_signed_parts_unique _ _ _ _ hp.1 hp.2 hq.1 hq.2
    (fourReduced_surviving_disjoint hP) (fourReduced_surviving_disjoint hQ)
  rw [four_restriction_reduced_inventory hP, four_restriction_reduced_inventory hQ] at hzero
  linear_combination hzero + htop

/-- Ordered endpoint recovery from a reduced Laurent monomial, expressed as
cross multiplication in the free generator ring so no denominator convention is hidden. -/
theorem endpoint_ordered_ratio_reading (a r A R : ℤ)
    (hr : 0 < r) (hR : 0 < R) (ha : r < a) (hA : R < A)
    (he : complete a * complete R = complete A * complete r) :
    a = A ∧ r = R := by
  have h := complete_two_product_reading (show 0 < a by omega) hR
    (show 0 < A by omega) hr he
  rcases h with ⟨ha', hr'⟩ | ⟨ha', hr'⟩ <;> omega

/-- The tied endpoint ratio retains the unordered two pairs with multiplicity,
including a coefficient-two contribution when the two Laurent monomials coincide. -/
theorem four_tied_endpoint_ratio {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (hxy : prefixIndex P = suffixIndex P) :
    MvPolynomial.pderiv (secondGenerator hP) (restriction q P) *
        bar q (P.g 0) * bar q (P.g 2) =
      -MvPolynomial.pderiv (fullGenerator P) (restriction q P) *
        (bar q (P.r 0) * bar q (P.g 2) + bar q (P.r 3) * bar q (P.g 0)) := by
  rw [four_second_coefficient hP, four_full_coefficient hP]
  have hx : secondIndex P = prefixIndex P := by
    dsimp [secondIndex]
    rw [hxy]
    simp
  simp only [hx, hxy, if_pos rfl, ite_true, ite_false, neg_neg, gapMonomial,
    Fin.prod_univ_three]
  rw [bar_eq_complete_of_ne q (P.g 0) (by exact_mod_cast hP.gap_ne 0),
    bar_eq_complete_of_ne q (P.g 1) (by exact_mod_cast hP.gap_ne 1),
    bar_eq_complete_of_ne q (P.g 2) (by exact_mod_cast hP.gap_ne 2)]
  ring

private theorem not_mem_vars_det {n : ℕ} (v : ℕ+)
    (M : Matrix (Fin n) (Fin n) CompleteRing) (hM : ∀ i j, v ∉ (M i j).vars) :
    v ∉ M.det.vars := by
  classical
  intro hv
  rw [Matrix.det_apply'] at hv
  have hsum := MvPolynomial.vars_sum_subset Finset.univ
    (fun σ => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : CompleteRing)) *
      ∏ i, M (σ i) i) hv
  obtain ⟨σ, _, hterm⟩ := Finset.mem_biUnion.mp hsum
  have hmul := MvPolynomial.vars_mul _ _ hterm
  rcases Finset.mem_union.mp hmul with hsign | hprod
  · have hs : ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : CompleteRing)).vars = ∅ := by
      rw [show ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : CompleteRing)) =
        MvPolynomial.C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) by simp]
      rw [MvPolynomial.vars_C]
    simpa only [hs, Finset.notMem_empty] using hsign
  · have h := MvPolynomial.vars_prod (fun i : Fin n => M (σ i) i) hprod
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    exact hM (σ i) i hi

/-- No supported variable lies above the endpoint maximum except the private
full interval.  This is derived from every actual matrix entry. -/
theorem restriction_vars_le_second_except_full {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (v : ℕ+)
    (hv : v ≠ fullGenerator P) (hbig : secondIndex P < (v.val : ℤ)) :
    v ∉ (restriction q P).vars := by
  have hT : fullIndex P ≠ (v.val : ℤ) := by
    intro he
    apply hv
    apply PNat.coe_injective
    exact_mod_cast ((fullGenerator_int_coe P).trans he).symm
  obtain ⟨hMq, hMT, hrows, hgaps, hU, hV, hW⟩ := four_endpoint_index_bounds hP
  have hrow0 := hrows 0
  have hrow1 := hrows 1
  have hrow2 := hrows 2
  have hrow3 := hrows 3
  have hgap0 := hgaps 0
  have hgap1 := hgaps 1
  have hgap2 := hgaps 2
  have hX := le_max_left (prefixIndex P) (suffixIndex P)
  have hY := le_max_right (prefixIndex P) (suffixIndex P)
  change prefixIndex P ≤ secondIndex P at hX
  change suffixIndex P ≤ secondIndex P at hY
  dsimp [prefixIndex, suffixIndex] at hX hY
  rw [fullIndex_four] at hT
  have hdom := P.four_domain hP.thick.hessenberg
  rcases hdom with ⟨hr, hs, ht, ha, hb, hc, hd⟩
  have hentries : ∀ i j : Fin 4, v ∉ (P.toBetaDiagram.matrix i j).vars := by
    intro i j
    change v ∉ (complete (P.xi i - P.zeta j)).vars
    rw [mem_vars_complete_iff]
    change (v.val : ℤ) ≠ (Matrix.of (fun i j : Fin 4 => P.xi i - P.zeta j)) i j
    rw [P.indices_four]
    fin_cases i <;> fin_cases j <;> norm_num [fourIndices] <;> omega
  exact not_mem_vars_erase q v P.toBetaDiagram.schur
    (not_mem_vars_det v P.toBetaDiagram.matrix hentries)

/-- The actual two largest supported labels are exactly T and M. -/
theorem four_endpoint_supported_labels {q : ℕ+} {P : Profile 3}
    (hP : QComponent q P) (ha : P.r 0 ≠ q.val) :
    fullGenerator P ∈ (restriction q P).vars ∧
      secondGenerator hP ∈ (restriction q P).vars ∧
      ((secondGenerator hP).val : ℤ) < (fullGenerator P).val ∧
      (∀ v ∈ (restriction q P).vars, v ≠ fullGenerator P →
        (v.val : ℤ) ≤ (secondGenerator hP).val) := by
  have hfull : fullGenerator P ∈ (restriction q P).vars := by
    by_contra hn
    have h := MvPolynomial.pderiv_eq_zero_of_notMem_vars hn
    rw [four_full_coefficient hP] at h
    exact neg_ne_zero.mpr (gapMonomial_ne_zero P) h
  have hsecond : secondGenerator hP ∈ (restriction q P).vars := by
    by_contra hn
    exact four_second_coefficient_ne_zero hP ha
      (MvPolynomial.pderiv_eq_zero_of_notMem_vars hn)
  refine ⟨hfull, hsecond, ?_, ?_⟩
  · rw [secondGenerator_val, fullGenerator_int_coe]
    exact (four_endpoint_index_bounds hP).2.1
  · intro v hv hne
    rw [secondGenerator_val]
    by_contra hn
    exact restriction_vars_le_second_except_full hP v hne (by omega) hv

private theorem positive_quartet_sum_reading (T U : Fin 2 → Fin 4 → ℤ)
    (hT : ∀ i j, 0 < T i j) (hU : ∀ i j, 0 < U i j)
    (he : quartetTerm (T 0) + quartetTerm (T 1) =
      quartetTerm (U 0) + quartetTerm (U 1)) :
    ((FourRowHessenberg.fourMatch (T 0 0) (T 0 1) (T 0 2) (T 0 3)
          (U 0 0) (U 0 1) (U 0 2) (U 0 3) ∧
        FourRowHessenberg.fourMatch (T 1 0) (T 1 1) (T 1 2) (T 1 3)
          (U 1 0) (U 1 1) (U 1 2) (U 1 3)) ∨
      (FourRowHessenberg.fourMatch (T 0 0) (T 0 1) (T 0 2) (T 0 3)
          (U 1 0) (U 1 1) (U 1 2) (U 1 3) ∧
        FourRowHessenberg.fourMatch (T 1 0) (T 1 1) (T 1 2) (T 1 3)
          (U 0 0) (U 0 1) (U 0 2) (U 0 3))) := by
  have hm := he
  rw [quartetTerm_monomial (T 0) (hT 0), quartetTerm_monomial (T 1) (hT 1),
    quartetTerm_monomial (U 0) (hU 0), quartetTerm_monomial (U 1) (hU 1)] at hm
  have hread (i j : Fin 2) (he : quartetExponent (T i) = quartetExponent (U j)) :
      FourRowHessenberg.fourMatch (T i 0) (T i 1) (T i 2) (T i 3)
        (U j 0) (U j 1) (U j 2) (U j 3) := by
    apply FourRowHessenberg.four_product_reading
      (hT i 0) (hT i 1) (hT i 2) (hT i 3) (hU j 0) (hU j 1) (hU j 2) (hU j 3)
    change quartetTerm (T i) = quartetTerm (U j)
    rw [quartetTerm_monomial (T i) (hT i), quartetTerm_monomial (U j) (hU j), he]
  rcases residual_monomial_pair_reading _ _ _ _ hm with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨hread 0 0 h0, hread 1 1 h1⟩
  · exact Or.inr ⟨hread 0 1 h0, hread 1 0 h1⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- Equal tied Laurent ratios recover the unordered endpoint pairs with
multiplicity; positivity and row>gap exclude every numerator/denominator swap. -/
theorem endpoint_unordered_ratio_reading (a d r t A D R T : ℤ)
    (hr : 0 < r) (ht : 0 < t) (ha : r < a) (hd : t < d)
    (hR : 0 < R) (hT : 0 < T) (hA : R < A) (hD : T < D)
    (he : (complete a * complete t + complete d * complete r) * complete R * complete T =
      (complete A * complete T + complete D * complete R) * complete r * complete t) :
    (a = A ∧ r = R ∧ d = D ∧ t = T) ∨
      (a = D ∧ r = T ∧ d = A ∧ t = R) := by
  let P : Fin 2 → Fin 4 → ℤ := ![![a, t, R, T], ![d, r, R, T]]
  let Q : Fin 2 → Fin 4 → ℤ := ![![A, T, r, t], ![D, R, r, t]]
  have hp : ∀ i j, 0 < P i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [P] <;> omega
  have hq : ∀ i j, 0 < Q i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [Q] <;> omega
  have hsum : quartetTerm (P 0) + quartetTerm (P 1) =
      quartetTerm (Q 0) + quartetTerm (Q 1) := by
    simp only [P, Q, quartetTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    linear_combination he
  have hm := positive_quartet_sum_reading P Q hp hq hsum
  rcases hm with ⟨hm0, hm1⟩ | ⟨hm0, hm1⟩ <;>
    simp only [P, Q, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hm0 hm1 <;>
    unfold FourRowHessenberg.fourMatch at hm0 hm1 <;>
    rcases hm0 with ⟨h0, hrest0⟩ | ⟨h0, hrest0⟩ | ⟨h0, hrest0⟩ | ⟨h0, hrest0⟩ <;>
    rcases hm1 with ⟨h1, hrest1⟩ | ⟨h1, hrest1⟩ | ⟨h1, hrest1⟩ | ⟨h1, hrest1⟩ <;>
    unfold FourRowHessenberg.tripleMatch at hrest0 hrest1 <;>
    rcases hrest0 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    rcases hrest1 with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ |
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
/-- The second private endpoint index is determined by the two largest
supported labels of the actual restriction. -/
theorem restriction_second_index_eq {q : ℕ+} {P Q : Profile 3}
    (hP : QComponent q P) (hQ : QComponent q Q)
    (ha : P.r 0 ≠ q.val) (hA : Q.r 0 ≠ q.val)
    (he : restriction q P = restriction q Q) : secondIndex P = secondIndex Q := by
  obtain ⟨hfull, _⟩ := restriction_full_and_gap_eq hP hQ he
  have hT : fullGenerator P = fullGenerator Q := by
    apply Subtype.ext
    have hh : ((fullGenerator P).val : ℤ) = (fullGenerator Q).val := by
      rw [fullGenerator_int_coe, fullGenerator_int_coe, hfull]
    exact Int.ofNat_inj.mp hh
  have hp := four_endpoint_supported_labels hP ha
  have hq := four_endpoint_supported_labels hQ hA
  have hneP : secondGenerator hP ≠ fullGenerator Q := by
    intro hh
    have hv := congrArg (fun v : ℕ+ => (v.val : ℤ)) hh
    rw [← hT] at hv
    exact (ne_of_lt hp.2.2.1) hv
  have hneQ : secondGenerator hQ ≠ fullGenerator P := by
    intro hh
    have hv := congrArg (fun v : ℕ+ => (v.val : ℤ)) hh
    rw [hT] at hv
    exact (ne_of_lt hq.2.2.1) hv
  have hPQ := hq.2.2.2 (secondGenerator hP)
    (by rw [← he]; exact hp.2.1) hneP
  have hQP := hp.2.2.2 (secondGenerator hQ)
    (by rw [he]; exact hq.2.1) hneQ
  have hh := le_antisymm hPQ hQP
  simpa only [secondGenerator_val] using hh

end SkewJacobiNegative.Staircase
